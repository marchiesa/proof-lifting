# Proof Lifting: Dafny → Boogie → SMT → Proof

Tools for extracting and analyzing proof evidence from the Dafny verification pipeline. The system captures mappings at each stage of compilation (Dafny → Boogie → SMT), enabling reverse lookup from Z3 unsat cores back to Dafny source constructs.

## Architecture

```
Dafny source
    ↓ (AstMappingManager - captures during Boogie generation)
Boogie IL (with {:id} attributes)
    ↓ (Namer - captures during SMT linearization)
SMT-LIB ($generated@@N names)
    ↓ (Z3)
Unsat core / Spurious model
    ↓ (reverse lookup via saved mappings)
Dafny assertions/invariants / Proof hints
```

Both mappings are captured during compilation, not reverse-engineered.

## Components

### Modified Dafny ([marchiesa/dafny@proof-lifting](https://github.com/marchiesa/dafny/tree/proof-lifting))

New `--ast-mapping` flag outputs a JSON file mapping Dafny constructs to Boogie IL:

- Variables: `dafnyName` → `boogieName` → `ssaVersions`
- Functions: `dafnyName` → `boogieName`
- Invariants, Assertions, Requires, Ensures, Foralls
- Full expression AST serialization per assertion (node types, children, variable/function references)

**Key file:** `Source/DafnyCore/Verifier/AstMappingManager.cs` (new)

**Modified files:**
- `BoogieGenerator.cs` - hooks to capture variable/function mappings
- `BoogieGenerator.TrLoop.cs` - invariant mapping hooks
- `BoogieGenerator.Methods.cs` - method context tracking
- `BoogieGenerator.TrCall.cs`, `TrForallStmt.cs`, `TrPredicateStatement.cs` - additional hooks
- `VerifyCommand.cs` - `--ast-mapping` CLI flag

### Modified Boogie ([marchiesa/boogie@proof-lifting](https://github.com/marchiesa/boogie/tree/proof-lifting))

New `/nameMap` flag outputs a JSON file mapping `$generated@@N` SMT names back to Boogie identifiers, tracked per-VC (since names are reused after `(reset)`).

**Key files:**
- `SMTLibLineariser.cs` - captures `Namer.GetQuotedName()` during linearization
- `SMTLibInteractiveTheoremProver.cs` - saves per-VC mappings at reset boundaries
- `SMTLibProcessTheoremProver.cs` - `/nameMap` flag and JSON serialization
- `ProverInterface.cs` - `NamedAssumesSmtNames` dictionary

### Proof Extractor (`proof-extractor/`)

Python pipeline that runs the full chain and extracts proof steps from Z3 unsat cores.

### SMT Analysis (`leonardo-experiments/smt_analysis/`)

Tools for analyzing Z3's behavior on failing VCs, including a CEGAR-style prototype that detects spurious counterexamples and injects proof hints.

## Prerequisites

- [.NET 8 SDK](https://dotnet.microsoft.com/download/dotnet/8.0)
- [Z3](https://github.com/Z3Prover/z3) (tested with 4.15.x)
- Python 3.8+

## Setup

### 1. Clone this repo

```bash
git clone https://github.com/marchiesa/proof-lifting.git
cd proof-lifting
```

### 2. Clone and build modified Dafny

```bash
git clone -b proof-lifting https://github.com/marchiesa/dafny.git dafny-source
cd dafny-source
git submodule update --init --recursive
dotnet build Source/Dafny.sln
cd ..
```

> On macOS with multiple .NET versions, use the .NET 8 SDK explicitly:
> ```bash
> /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet build Source/Dafny.sln
> ```

### 3. Clone and build modified Boogie

```bash
git clone -b proof-lifting https://github.com/marchiesa/boogie.git boogie
cd boogie
dotnet build Source/Boogie.sln
cd ..
```

## Usage

### Full pipeline (proof extraction)

```bash
python3 proof-extractor/pipeline.py examples/sum_seq.dfy
```

### Step by step

#### Step 1: Dafny → Boogie + AST mapping

```bash
dotnet dafny-source/Binaries/Dafny.dll verify input.dfy \
    --ast-mapping ast_mapping.json \
    --bprint output.bpl
```

**Output:**
- `output.bpl` - Boogie intermediate language
- `ast_mapping.json` - Dafny→Boogie mapping with expression ASTs

#### Step 2: Boogie → SMT + name mapping

```bash
dotnet boogie/Source/BoogieDriver/bin/Debug/net8.0/BoogieDriver.dll \
    output.bpl \
    /proverLog:smt_input.smt2 \
    /nameMap:name_map.json \
    /trackVerificationCoverage \
    /normalizeNames:1
```

**Output:**
- `smt_input.smt2` - full SMT-LIB trace sent to Z3
- `name_map.json` - per-VC mapping of `$generated@@N` → Boogie names

#### Step 3: Run Z3 for unsat cores

```bash
z3 smt_input.smt2
```

#### Step 4: Map results back to Dafny

Use `name_map.json` to decode SMT names to Boogie, then `ast_mapping.json` to decode Boogie to Dafny.

### CEGAR-style proof hint discovery

When Z3 returns `unknown` (verification fails), the spurious model can be analyzed to discover missing proof hints:

```bash
cd leonardo-experiments/smt_analysis
python3 cegar_prototype.py failing_vc.smt2
```

This parses Z3's candidate model, finds pairs of sequence terms that should be equal but aren't (detected via same-length heuristic + different function values), and suggests `Seq#Equal` hints to inject.

## Mapping Formats

### AST Mapping (Dafny → Boogie)

```json
{
  "methods": [{
    "name": "ComputeSum",
    "variables": {
      "sum": {"dafnyName": "sum", "boogieName": "sum#0", "ssaVersions": ["sum#0"]}
    },
    "invariants": [{
      "boogieId": "id18",
      "text": "sum == Sum(s[..i])",
      "expressionAst": { ... }
    }],
    "ensures": [{"boogieId": "id9", "text": "sum == Sum(s)"}]
  }],
  "functions": [{"dafnyName": "Sum", "boogieName": "_module.__default.Sum"}]
}
```

### Name Map (Boogie → SMT)

```json
{
  "variables": {"$generated@@593": "_module.__default.segmentSum", "$generated@@379": "Seq#Take"},
  "assertions": {"$generated@@1825": "assert$$id13$maintained"},
  "perVc": [
    {
      "vc": 3,
      "variables": {"$generated@@1808": "i#0", "$generated@@1809": "nums#0"}
    }
  ]
}
```

## Example: The `segmentSum` case

See `leonardo-experiments/smt_analysis/` for a detailed analysis of why `assert nums[..i+1][..i] == nums[..i]` is needed for Z3 to verify a simple sum method. The analysis includes:

- Side-by-side Boogie IL comparison (with/without assert)
- Decoded SMT-LIB traces showing the exact VC formulas
- Z3's spurious counterexample model (assigns `segmentSum` values that differ by 1)
- CEGAR prototype that automatically discovers the missing `Seq#Equal` hint

## Base Commits

- Dafny: `58b3f6a` (dafny-lang/dafny@master)
- Boogie: `3f38a63` (boogie-org/boogie@master)
