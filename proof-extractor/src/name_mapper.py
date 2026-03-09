"""Map Z3 internal names ($generated@@N) to Boogie/Dafny names."""

import re
from dataclasses import dataclass
from typing import Dict, Optional, Tuple, List
from pathlib import Path


@dataclass
class FunctionSignature:
    """A function signature."""
    name: str
    arg_types: List[str]
    return_type: str

    def __repr__(self):
        args = ", ".join(self.arg_types)
        return f"{self.name}({args}) -> {self.return_type}"


class NameMapper:
    """Maps Z3 internal names to Boogie/Dafny names."""

    # Known Boogie functions and their Dafny syntax
    BOOGIE_TO_DAFNY = {
        # Sequence operations
        "Seq#Length": "|{}|",           # |s|
        "Seq#Index": "{}[{}]",          # s[i]
        "Seq#Update": "{}[{} := {}]",   # s[i := v]
        "Seq#Append": "{} + {}",        # s1 + s2
        "Seq#Take": "{}[..{}]",         # s[..n]
        "Seq#Drop": "{}[{}..]",         # s[n..]
        "Seq#Contains": "{} in {}",     # val in s (args swapped)
        "Seq#Equal": "{} == {}",        # s1 == s2
        "Seq#Empty": "[]",              # []

        # Set operations
        "Set#Card": "|{}|",             # |s|
        "Set#Union": "{} + {}",         # s1 + s2
        "Set#Intersection": "{} * {}",  # s1 * s2
        "Set#Difference": "{} - {}",    # s1 - s2
        "Set#Subset": "{} <= {}",       # s1 <= s2
        "Set#Equal": "{} == {}",        # s1 == s2
        "Set#UnionOne": "{} + {{{}}}",  # s + {x}
        "Set#Disjoint": "{} !! {}",     # s1 !! s2
        "Set#Empty": "{}",              # {}
        "Set#Singleton": "{{{}}}",      # {x}

        # Box/Unbox (identity in Dafny)
        "$Box": "{}",
        "$Unbox": "{}",
        "LitInt": "{}",
        "Lit": "{}",
    }

    # Signature patterns to help identify functions
    # (arg_count, return_type) -> possible functions
    SIGNATURE_HINTS = {
        (1, "Int"): ["Seq#Length", "Set#Card"],
        (2, "T@U"): ["Seq#Index", "Seq#Take", "Seq#Drop", "Set#UnionOne"],
        (3, "T@U"): ["Seq#Update"],
        (2, "Bool"): ["Seq#Equal", "Seq#Contains", "Set#Equal", "Set#Subset", "Set#Disjoint"],
    }

    def __init__(self):
        self.z3_to_boogie: Dict[str, str] = {}
        self.boogie_to_z3: Dict[str, str] = {}
        self.z3_signatures: Dict[str, FunctionSignature] = {}
        self.variables: Dict[str, str] = {}  # Z3 var -> Dafny var

    def parse_smt_declarations(self, smt_content: str):
        """Parse SMT file to extract function declarations."""
        # Match: (declare-fun $generated@@N (Type1 Type2) ReturnType)
        pattern = r'\(declare-fun\s+(\$generated@@\d+)\s+\(([^)]*)\)\s+(\S+)\)'

        for match in re.finditer(pattern, smt_content):
            name = match.group(1)
            args = match.group(2).strip()
            ret = match.group(3)

            arg_types = args.split() if args else []
            self.z3_signatures[name] = FunctionSignature(name, arg_types, ret)

    def parse_boogie_declarations(self, boogie_content: str):
        """Parse Boogie file to extract function declarations."""
        # Match: function Seq#Length(s: Seq) : int;
        # or: revealed function Seq#Take(s: Seq, howMany: int) : Seq;
        pattern = r'(?:revealed\s+)?function\s+(\S+)\s*\(([^)]*)\)\s*:\s*(\S+)'

        boogie_sigs: Dict[str, FunctionSignature] = {}

        for match in re.finditer(pattern, boogie_content):
            name = match.group(1)
            params = match.group(2)
            ret = match.group(3).rstrip(';')

            # Parse parameter types
            arg_types = []
            if params.strip():
                for param in params.split(','):
                    param = param.strip()
                    if ':' in param:
                        _, type_part = param.split(':', 1)
                        arg_types.append(type_part.strip())

            # Normalize types to Z3 format
            z3_arg_types = [self._boogie_type_to_z3(t) for t in arg_types]
            z3_ret_type = self._boogie_type_to_z3(ret)

            boogie_sigs[name] = FunctionSignature(name, z3_arg_types, z3_ret_type)

        return boogie_sigs

    def _boogie_type_to_z3(self, boogie_type: str) -> str:
        """Convert Boogie type to Z3 type."""
        type_map = {
            "int": "Int",
            "bool": "Bool",
            "Seq": "T@U",
            "Box": "T@U",
            "Heap": "T@U",
            "ref": "T@U",
            "LayerType": "T@U",
            "Field": "T@U",
            "Ty": "T@T",
        }
        return type_map.get(boogie_type, "T@U")

    def build_mapping(self, smt_content: str, boogie_content: str):
        """Build the mapping from Z3 names to Boogie names."""
        self.parse_smt_declarations(smt_content)
        boogie_sigs = self.parse_boogie_declarations(boogie_content)

        # Try to match by signature
        for z3_name, z3_sig in self.z3_signatures.items():
            z3_key = (tuple(z3_sig.arg_types), z3_sig.return_type)

            for boogie_name, boogie_sig in boogie_sigs.items():
                boogie_key = (tuple(boogie_sig.arg_types), boogie_sig.return_type)

                if z3_key == boogie_key:
                    # Potential match - use heuristics for common functions
                    if self._is_likely_match(z3_name, boogie_name, z3_sig):
                        self.z3_to_boogie[z3_name] = boogie_name
                        self.boogie_to_z3[boogie_name] = z3_name
                        break

    def _is_likely_match(self, z3_name: str, boogie_name: str, sig: FunctionSignature) -> bool:
        """Heuristic to determine if names likely match."""
        # For now, accept any signature match
        # Could be improved with usage context
        return True

    def add_known_mapping(self, z3_name: str, boogie_name: str):
        """Manually add a known mapping."""
        self.z3_to_boogie[z3_name] = boogie_name
        self.boogie_to_z3[boogie_name] = z3_name

    def get_boogie_name(self, z3_name: str) -> str:
        """Get Boogie name for Z3 name, or return original if unknown."""
        return self.z3_to_boogie.get(z3_name, z3_name)

    def get_dafny_name(self, z3_name: str) -> str:
        """Get Dafny name for Z3 name."""
        boogie = self.get_boogie_name(z3_name)

        # Strip module prefix
        if boogie.startswith("_module.__default."):
            boogie = boogie[len("_module.__default."):]

        return boogie

    def format_dafny_call(self, boogie_name: str, args: List[str]) -> str:
        """Format a Boogie function call as Dafny syntax.

        Args:
            boogie_name: The Boogie function name (e.g., "Seq#Length")
            args: The resolved argument strings

        Returns:
            Dafny syntax string (e.g., "|s|" for Seq#Length)
        """
        template = self.BOOGIE_TO_DAFNY.get(boogie_name)
        if template:
            try:
                # Handle special case: Seq#Contains has swapped args
                if boogie_name == "Seq#Contains" and len(args) >= 2:
                    return template.format(args[1], args[0])
                return template.format(*args)
            except (IndexError, KeyError):
                pass

        # Default: function call syntax
        if args:
            return f"{boogie_name}({', '.join(args)})"
        return boogie_name

    def is_identity_function(self, boogie_name: str) -> bool:
        """Check if a function is an identity (Box, Unbox, Lit)."""
        return boogie_name in ("$Box", "$Unbox", "LitInt", "Lit")

    def infer_variable_mapping(self, smt_content: str, boogie_content: str):
        """Infer variable mappings from context."""
        # Look for patterns like $generated@@145 used with Seq#Length
        # These are likely sequence variables

        # Extract variable declarations from Boogie
        # Match: var s#0: Seq; or parameter s#0: Seq
        var_pattern = r'(?:var|parameter)\s+(\w+#\d+)\s*:\s*(\w+)'
        for match in re.finditer(var_pattern, boogie_content):
            var_name = match.group(1)
            var_type = match.group(2)
            # Store for later resolution
            self.variables[var_name] = var_name.split('#')[0]  # s#0 -> s

    def infer_function_mapping_from_axioms(self, smt_content: str):
        """Infer function mappings from SMT axioms.

        Boogie generates characteristic axioms for built-in functions.
        We can identify functions by recognizing these patterns.
        """
        # Track which functions are Box/Unbox (to exclude from other mappings)
        box_unbox_fns = set()

        # Pattern: Box/Unbox inverse axioms
        # (= ($generated@@10 ($generated@@9 x)) x) means @@10=Unbox, @@9=Box
        unbox_box_pattern = r'\(=\s+\((\$generated@@\d+)\s+\((\$generated@@\d+)\s+\$generated@@\d+\)\)\s+\$generated@@\d+\)'
        for match in re.finditer(unbox_box_pattern, smt_content):
            unbox_fn = match.group(1)
            box_fn = match.group(2)
            self.z3_to_boogie[unbox_fn] = "$Unbox"
            self.z3_to_boogie[box_fn] = "$Box"
            box_unbox_fns.add(unbox_fn)
            box_unbox_fns.add(box_fn)

        # Pattern: Seq#Length - (T@U) -> Int, NOT Box/Unbox
        # Characteristic: (<= 0 (length s)) axiom - length is non-negative
        for fn, sig in self.z3_signatures.items():
            if fn in box_unbox_fns:
                continue
            if sig.arg_types == ["T@U"] and sig.return_type == "Int":
                # Check for (<= 0 (fn ...)) pattern - characteristic of Seq#Length
                if f'(<= 0 ({fn}' in smt_content:
                    self.z3_to_boogie[fn] = "Seq#Length"
                    break

        # Pattern: Seq#Empty - () -> T@U
        # Characteristic: (= (Seq#Length Seq#Empty) 0)
        length_fn = None
        for fn, name in self.z3_to_boogie.items():
            if name == "Seq#Length":
                length_fn = fn
                break

        if length_fn:
            # Find (= (length empty) 0)
            empty_pattern = rf'\(=\s+\({re.escape(length_fn)}\s+(\$generated@@\d+)\)\s+0\)'
            match = re.search(empty_pattern, smt_content)
            if match:
                empty_fn = match.group(1)
                if empty_fn not in self.z3_to_boogie:
                    self.z3_to_boogie[empty_fn] = "Seq#Empty"

        # Pattern: Seq#Update (3 args: T@U Int T@U -> T@U)
        # Characteristic: (= (Seq#Length (Seq#Update s i v)) (Seq#Length s))
        for fn, sig in self.z3_signatures.items():
            if fn in self.z3_to_boogie:
                continue
            if len(sig.arg_types) == 3 and sig.return_type == "T@U":
                if sig.arg_types[1] == "Int":  # Second arg is Int (index)
                    # Check if length of update equals length of original
                    if length_fn and f'({length_fn} ({fn}' in smt_content:
                        self.z3_to_boogie[fn] = "Seq#Update"
                        break

        # Pattern: Seq#Index (2 args: T@U Int -> T@U)
        # Often appears in axioms about Seq#Update: (= (index (update s i v) i) v)
        update_fn = None
        for fn, name in self.z3_to_boogie.items():
            if name == "Seq#Update":
                update_fn = fn
                break

        for fn, sig in self.z3_signatures.items():
            if fn in self.z3_to_boogie:
                continue
            if sig.arg_types == ["T@U", "Int"] and sig.return_type == "T@U":
                # Check if used with Seq#Update in axioms
                if update_fn and f'({fn} ({update_fn}' in smt_content:
                    self.z3_to_boogie[fn] = "Seq#Index"
                    break

        # Pattern: Typed Box (T@T T@U -> T@U) - used to wrap values with type info
        for fn, sig in self.z3_signatures.items():
            if fn in self.z3_to_boogie:
                continue
            if sig.arg_types == ["T@T", "T@U"] and sig.return_type == "T@U":
                self.z3_to_boogie[fn] = "$Box"
                break

        # Pattern: Typed Unbox (T@T T@U -> T@U) - unwraps values
        for fn, sig in self.z3_signatures.items():
            if fn in self.z3_to_boogie:
                continue
            if sig.arg_types == ["T@T", "T@U"] and sig.return_type == "T@U":
                # Check if this is Unbox (appears in inverse pattern with Box)
                for box_fn, name in self.z3_to_boogie.items():
                    if name == "$Box" and f'({fn} $generated@@' in smt_content:
                        if f'({box_fn} $generated@@' in smt_content:
                            self.z3_to_boogie[fn] = "$Unbox"
                            break


class ProofNameResolver:
    """Resolve names in a Z3 proof to human-readable form."""

    def __init__(self, mapper: NameMapper):
        self.mapper = mapper
        self.let_bindings: Dict[str, str] = {}

    def resolve_term(self, term) -> str:
        """Resolve a term to human-readable form."""
        try:
            from .sexpr_parser import Atom, SList
        except ImportError:
            from sexpr_parser import Atom, SList

        if isinstance(term, Atom):
            value = term.value

            # Check if it's a Z3 generated name
            if value.startswith('$generated@@'):
                return self.mapper.get_dafny_name(value)

            # Check if it's a let-bound variable
            if value.startswith('?x') or value.startswith('@x'):
                return self.let_bindings.get(value, value)

            return value

        elif isinstance(term, SList):
            if not term.items:
                return "()"

            head = term.items[0]
            if isinstance(head, Atom):
                op = head.value

                # Handle let bindings
                if op == "let":
                    return self._resolve_let(term)

                # Handle function applications
                resolved_args = [self.resolve_term(arg) for arg in term.items[1:]]
                resolved_op = self.mapper.get_dafny_name(op)

                return f"{resolved_op}({', '.join(resolved_args)})"

            return f"({' '.join(self.resolve_term(x) for x in term.items)})"

        return str(term)

    def _resolve_let(self, term) -> str:
        """Resolve a let expression."""
        try:
            from .sexpr_parser import SList
        except ImportError:
            from sexpr_parser import SList

        # (let ((var value)) body)
        bindings = term.items[1]
        body = term.items[2]

        # Process bindings
        if isinstance(bindings, SList):
            for binding in bindings.items:
                if isinstance(binding, SList) and len(binding.items) >= 2:
                    var = binding.items[0]
                    val = binding.items[1]
                    if hasattr(var, 'value'):
                        self.let_bindings[var.value] = self.resolve_term(val)

        return self.resolve_term(body)
