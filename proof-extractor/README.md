# Proof Extractor

Extract proof steps from Z3 unsat cores and map them back to Dafny.

## Prerequisites

- Modified Dafny (`../dafny-source/`) with `--ast-mapping` support
- Modified Boogie (`../boogie/`) with `/nameMap` support
- Python 3.8+
- .NET 8 SDK

## Usage

```bash
python3 pipeline.py input.dfy
```

## Pipeline

```
Dafny Source
    ↓ dafny --ast-mapping --bprint
AST Mapping (JSON) + Boogie IL
    ↓ boogie /proverLog /nameMap /trackVerificationCoverage /normalizeNames:1
SMT-LIB (with :named) + nameMap (JSON)
    ↓ Z3
Unsat Core
    ↓ Map via nameMap → AST mapping
Dafny Proof Steps
```

## Mapping Chain

```
Dafny name (e.g., sum)
    ↓ AST mapping
Boogie name (e.g., sum#0)
    ↓ nameMap with /normalizeNames:1
SMT name ($generated@@N)
    ↓ Z3 unsat core
Proof dependencies
    ↓ reverse mapping
Dafny assertions
```

**No pattern matching.** All translations use the mapping chain.

## Key Files

| File | Purpose |
|------|---------|
| `pipeline.py` | Main entry - runs full chain |
| `core_to_proof.py` | SMT parsing, DAG building, core extraction |
| `vc_extractor.py` | Boogie expression → Dafny translation |
| `src/name_mapper.py` | `$generated@@N` → Boogie name mapping |
| `src/sexpr_parser.py` | SMT S-expression parser |

## AST Mapping Format

From `dafny --ast-mapping`:

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
      "smtMaintained": "assert$$id18$maintained"
    }],
    "ensures": [{"boogieId": "id9", "text": "sum == Sum(s)"}]
  }],
  "functions": [{"dafnyName": "Sum", "boogieName": "_module.__default.Sum"}]
}
```

## nameMap Format

From `boogie /nameMap`:

```json
{
  "variables": {"$generated@@123": "sum#0", "$generated@@456": "_module.__default.Sum"},
  "assertions": {"assert$$id18$maintained": "assert$$id18$maintained"}
}
```
