"""Source location mapping between Dafny, Boogie, and SMT.

Maps verification conditions back to their source locations.
"""

import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from pathlib import Path


@dataclass
class DafnyLocation:
    """A location in a Dafny source file."""
    file: str
    line: int
    column: int
    stmt_type: str  # 'assert statement', 'while statement', etc.

    def __repr__(self):
        return f"{self.file}:{self.line}:{self.column} ({self.stmt_type})"


@dataclass
class AssertionInfo:
    """Information about a Boogie assertion."""
    assertion_id: str  # e.g., "id22"
    boogie_line: int
    dafny_loc: Optional[DafnyLocation]
    assertion_text: str  # The actual assertion expression
    context: str  # What kind of VC: "invariant_init", "invariant_maint", "postcond", "assert"


@dataclass
class SourceMapping:
    """Complete mapping from Boogie to Dafny source."""
    boogie_file: str
    dafny_file: str

    # Boogie line -> Dafny location
    boogie_to_dafny: Dict[int, DafnyLocation] = field(default_factory=dict)

    # Assertion ID -> AssertionInfo
    assertions: Dict[str, AssertionInfo] = field(default_factory=dict)

    # For quick lookup: Dafny line -> list of assertion IDs
    dafny_line_to_assertions: Dict[int, List[str]] = field(default_factory=dict)


def parse_boogie_file(boogie_content: str, boogie_path: str = "") -> SourceMapping:
    """Parse a Boogie file and extract source mappings.

    Looks for patterns like:
    - // ----- assert statement ----- file.dfy(line,col)
    - assert {:id "id22"} expression;
    """
    mapping = SourceMapping(boogie_file=boogie_path, dafny_file="")

    lines = boogie_content.split('\n')

    # Pattern for Dafny source location comments
    source_pattern = re.compile(
        r'// ----- ([\w\s]+) ----- (.+\.dfy)\((\d+),(\d+)\)'
    )

    # Pattern for assertion IDs
    assert_id_pattern = re.compile(r'assert\s+\{:id\s+"(id\d+)"\}([^;]+);')

    current_dafny_loc = None
    current_context = "unknown"

    for i, line in enumerate(lines, 1):
        # Check for source location comment
        source_match = source_pattern.search(line)
        if source_match:
            stmt_type = source_match.group(1).strip()
            dafny_file = source_match.group(2)
            dafny_line = int(source_match.group(3))
            dafny_col = int(source_match.group(4))

            current_dafny_loc = DafnyLocation(
                file=Path(dafny_file).name,
                line=dafny_line,
                column=dafny_col,
                stmt_type=stmt_type
            )
            mapping.boogie_to_dafny[i] = current_dafny_loc

            # Update mapping's dafny_file if not set
            if not mapping.dafny_file:
                mapping.dafny_file = dafny_file

            # Determine context based on stmt_type
            if "while" in stmt_type.lower():
                current_context = "loop"
            elif "assert" in stmt_type.lower():
                current_context = "assert"
            elif "ensures" in stmt_type.lower() or "postcondition" in stmt_type.lower():
                current_context = "postcond"
            else:
                current_context = stmt_type

        # Check for assertion with ID
        assert_match = assert_id_pattern.search(line)
        if assert_match:
            assert_id = assert_match.group(1)
            assert_text = assert_match.group(2).strip()

            # Find the nearest Dafny location (look back a few lines)
            dafny_loc = None
            for offset in range(0, 10):
                if (i - offset) in mapping.boogie_to_dafny:
                    dafny_loc = mapping.boogie_to_dafny[i - offset]
                    break

            # Determine specific context
            context = current_context
            if "Loop invariant" in line or "LoopInvariant" in assert_text:
                if "entry" in line.lower() or "init" in line.lower():
                    context = "invariant_init"
                else:
                    context = "invariant_maint"
            elif "subsumption" in line:
                context = "subsumption"

            info = AssertionInfo(
                assertion_id=assert_id,
                boogie_line=i,
                dafny_loc=dafny_loc,
                assertion_text=assert_text,
                context=context
            )
            mapping.assertions[assert_id] = info

            # Update dafny_line_to_assertions
            if dafny_loc:
                if dafny_loc.line not in mapping.dafny_line_to_assertions:
                    mapping.dafny_line_to_assertions[dafny_loc.line] = []
                mapping.dafny_line_to_assertions[dafny_loc.line].append(assert_id)

    return mapping


def find_assertion_for_proof(mapping: SourceMapping,
                             proof_context: str) -> Optional[AssertionInfo]:
    """Try to match a Z3 proof to a specific assertion.

    Uses heuristics based on the proof content to find the best match.
    """
    # Look for qid references like |programbpl.LINE:COL|
    qid_pattern = re.compile(r'programbpl\.(\d+):(\d+)')
    matches = qid_pattern.findall(proof_context)

    if matches:
        # Find the assertion closest to these line references
        for line_str, col_str in matches:
            line = int(line_str)
            # Check if there's an assertion at or near this line
            for offset in range(-5, 5):
                check_line = line + offset
                dafny_loc = mapping.boogie_to_dafny.get(check_line)
                if dafny_loc:
                    # Find assertions for this Dafny line
                    assert_ids = mapping.dafny_line_to_assertions.get(dafny_loc.line, [])
                    if assert_ids:
                        return mapping.assertions.get(assert_ids[0])

    return None


def get_assertions_by_dafny_line(mapping: SourceMapping,
                                  dafny_line: int) -> List[AssertionInfo]:
    """Get all assertions that correspond to a specific Dafny line."""
    assert_ids = mapping.dafny_line_to_assertions.get(dafny_line, [])
    return [mapping.assertions[aid] for aid in assert_ids if aid in mapping.assertions]


def get_loop_invariant_assertions(mapping: SourceMapping) -> Dict[int, List[AssertionInfo]]:
    """Get assertions grouped by loop (Dafny line of while statement).

    Returns a dict: dafny_line -> list of invariant assertions
    """
    result = {}

    for info in mapping.assertions.values():
        if info.dafny_loc and "while" in info.dafny_loc.stmt_type.lower():
            line = info.dafny_loc.line
            if line not in result:
                result[line] = []
            result[line].append(info)

    return result


def get_explicit_assertions(mapping: SourceMapping) -> List[AssertionInfo]:
    """Get all explicit assert statements (not loop invariants or postconditions)."""
    return [
        info for info in mapping.assertions.values()
        if info.dafny_loc and "assert" in info.dafny_loc.stmt_type.lower()
    ]


def format_assertion_summary(mapping: SourceMapping) -> str:
    """Format a human-readable summary of the assertion mapping."""
    lines = []
    lines.append(f"Source mapping for {mapping.dafny_file}")
    lines.append(f"Total assertions: {len(mapping.assertions)}")
    lines.append("")

    # Group by Dafny line
    by_line = {}
    for info in mapping.assertions.values():
        if info.dafny_loc:
            line = info.dafny_loc.line
            if line not in by_line:
                by_line[line] = []
            by_line[line].append(info)

    for dafny_line in sorted(by_line.keys()):
        infos = by_line[dafny_line]
        first = infos[0]
        lines.append(f"Line {dafny_line} ({first.dafny_loc.stmt_type}):")
        for info in infos:
            # Truncate assertion text
            text = info.assertion_text[:60] + "..." if len(info.assertion_text) > 60 else info.assertion_text
            lines.append(f"  {info.assertion_id}: {text}")

    return "\n".join(lines)
