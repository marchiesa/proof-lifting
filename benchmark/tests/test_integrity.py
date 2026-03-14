#!/usr/bin/env python3
"""
Tests for the integrity checker.

Verifies that the checker correctly:
  - Accepts files with only proof annotations added
  - Rejects files with modified code logic
  - Rejects files with modified specifications
  - Handles edge cases (multi-line invariants, assert by blocks, etc.)
"""

import os
import sys
import tempfile
import unittest

# Add parent dirs to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'dafny-proxy'))
from check_integrity import (
    check_integrity,
    strip_proof_constructs,
    normalize_whitespace,
    DafnyParser,
    extract_spec_blocks,
    extract_methods,
)


class TestStripProofConstructs(unittest.TestCase):
    """Test the proof-stripping logic."""

    def test_strip_simple_invariant(self):
        code = """while i < n
  invariant 0 <= i <= n
{
  i := i + 1;
}"""
        stripped = strip_proof_constructs(code)
        self.assertNotIn("invariant", stripped)
        self.assertIn("while i < n", stripped)
        self.assertIn("i := i + 1;", stripped)

    def test_strip_multiple_invariants(self):
        code = """while i < n
  invariant 0 <= i <= n
  invariant acc == sum(s[..i])
  decreases n - i
{
  acc := acc + s[i];
  i := i + 1;
}"""
        stripped = strip_proof_constructs(code)
        self.assertNotIn("invariant", stripped)
        self.assertNotIn("decreases", stripped)
        self.assertIn("acc := acc + s[i];", stripped)

    def test_strip_multiline_invariant(self):
        code = """while i < n
  invariant forall j :: 0 <= j < i ==>
    s[j] > 0
{
  i := i + 1;
}"""
        stripped = strip_proof_constructs(code)
        self.assertNotIn("invariant", stripped)
        self.assertIn("while i < n", stripped)

    def test_strip_assert(self):
        code = """var x := 5;
assert x > 0;
var y := x + 1;"""
        stripped = strip_proof_constructs(code)
        self.assertNotIn("assert", stripped)
        self.assertIn("var x := 5;", stripped)
        self.assertIn("var y := x + 1;", stripped)

    def test_strip_assert_by(self):
        code = """var x := 5;
assert x > 0 by {
  reveal Foo();
  calc {
    x;
    == 5;
    > 0;
  }
}
var y := x + 1;"""
        stripped = strip_proof_constructs(code)
        self.assertNotIn("assert", stripped)
        self.assertNotIn("reveal", stripped)
        self.assertIn("var x := 5;", stripped)
        self.assertIn("var y := x + 1;", stripped)

    def test_strip_ghost_var(self):
        code = """var x := 5;
ghost var gx := x;
var y := x + 1;"""
        stripped = strip_proof_constructs(code)
        self.assertNotIn("ghost var", stripped)
        self.assertIn("var x := 5;", stripped)
        self.assertIn("var y := x + 1;", stripped)

    def test_strip_assume(self):
        code = """var x := 5;
assume x > 0;
var y := x + 1;"""
        stripped = strip_proof_constructs(code)
        self.assertNotIn("assume", stripped)

    def test_strip_calc(self):
        code = """var x := 5;
calc {
  x + 1;
  == 6;
  > 5;
}
var y := x + 1;"""
        stripped = strip_proof_constructs(code)
        self.assertNotIn("calc", stripped)
        self.assertIn("var x := 5;", stripped)
        self.assertIn("var y := x + 1;", stripped)

    def test_strip_forall_proof(self):
        code = """var x := 5;
forall j | 0 <= j < n
  ensures P(j)
{
  LemmaFoo(j);
}
var y := x + 1;"""
        stripped = strip_proof_constructs(code)
        self.assertNotIn("forall", stripped)
        self.assertIn("var x := 5;", stripped)

    def test_strip_decreases(self):
        code = """while i < n
  decreases n - i
{
  i := i + 1;
}"""
        stripped = strip_proof_constructs(code)
        self.assertNotIn("decreases", stripped)
        self.assertIn("while i < n", stripped)

    def test_preserve_code_logic(self):
        code = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  var acc := 0;
  while i < n
  {
    acc := acc + i;
    i := i + 1;
  }
  r := acc;
}"""
        stripped = strip_proof_constructs(code)
        self.assertIn("method Foo", stripped)
        self.assertIn("var i := 0;", stripped)
        self.assertIn("acc := acc + i;", stripped)
        self.assertIn("r := acc;", stripped)


class TestDafnyParser(unittest.TestCase):
    """Test the Dafny parser."""

    def test_extract_predicate(self):
        code = """predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method Sort(s: seq<int>) returns (r: seq<int>)
{
  r := s;
}"""
        parser = DafnyParser(code)
        blocks = parser.extract_top_level_blocks()
        self.assertEqual(len(blocks), 2)
        self.assertEqual(blocks[0]['type'], 'predicate')
        self.assertEqual(blocks[0]['name'], 'IsSorted')
        self.assertEqual(blocks[1]['type'], 'method')
        self.assertEqual(blocks[1]['name'], 'Sort')

    def test_extract_function(self):
        code = """function Sum(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + Sum(s[1..])
}"""
        parser = DafnyParser(code)
        blocks = parser.extract_top_level_blocks()
        self.assertEqual(len(blocks), 1)
        self.assertEqual(blocks[0]['type'], 'function')
        self.assertEqual(blocks[0]['name'], 'Sum')

    def test_extract_spec_blocks(self):
        code = """predicate P(x: int) { x > 0 }

function F(x: int): int { x + 1 }

method M(x: int) returns (r: int)
{
  r := x + 1;
}"""
        parser = DafnyParser(code)
        specs = extract_spec_blocks(parser)
        self.assertEqual(len(specs), 2)
        names = {s['name'] for s in specs}
        self.assertIn('P', names)
        self.assertIn('F', names)


class TestCheckIntegrity(unittest.TestCase):
    """Test the full integrity checker."""

    def _write_temp(self, content: str) -> str:
        fd, path = tempfile.mkstemp(suffix='.dfy')
        with os.fdopen(fd, 'w') as f:
            f.write(content)
        return path

    def test_identical_files(self):
        """Identical files should pass."""
        code = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  while i < n
  {
    i := i + 1;
  }
  r := i;
}"""
        orig = self._write_temp(code)
        sub = self._write_temp(code)
        ok, msg = check_integrity(orig, sub)
        self.assertTrue(ok, msg)
        os.unlink(orig)
        os.unlink(sub)

    def test_added_invariant(self):
        """Adding an invariant should pass."""
        original = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  while i < n
  {
    i := i + 1;
  }
  r := i;
}"""
        submitted = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    i := i + 1;
  }
  r := i;
}"""
        orig = self._write_temp(original)
        sub = self._write_temp(submitted)
        ok, msg = check_integrity(orig, sub)
        self.assertTrue(ok, msg)
        os.unlink(orig)
        os.unlink(sub)

    def test_added_assert(self):
        """Adding an assert should pass."""
        original = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  r := i;
}"""
        submitted = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  assert i >= 0;
  r := i;
}"""
        orig = self._write_temp(original)
        sub = self._write_temp(submitted)
        ok, msg = check_integrity(orig, sub)
        self.assertTrue(ok, msg)
        os.unlink(orig)
        os.unlink(sub)

    def test_added_ghost_var(self):
        """Adding a ghost var should pass."""
        original = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  r := i;
}"""
        submitted = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  ghost var old_i := i;
  r := i;
}"""
        orig = self._write_temp(original)
        sub = self._write_temp(submitted)
        ok, msg = check_integrity(orig, sub)
        self.assertTrue(ok, msg)
        os.unlink(orig)
        os.unlink(sub)

    def test_modified_code_logic(self):
        """Modifying code logic should fail."""
        original = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  while i < n
  {
    i := i + 1;
  }
  r := i;
}"""
        submitted = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  while i < n
  {
    i := i + 2;
  }
  r := i;
}"""
        orig = self._write_temp(original)
        sub = self._write_temp(submitted)
        ok, msg = check_integrity(orig, sub)
        self.assertFalse(ok, "Should reject modified code logic")
        os.unlink(orig)
        os.unlink(sub)

    def test_modified_spec(self):
        """Modifying a predicate should fail."""
        original = """predicate IsPositive(x: int)
{
  x > 0
}

method Foo(x: int) returns (r: bool)
{
  r := x > 0;
}"""
        submitted = """predicate IsPositive(x: int)
{
  x >= 0
}

method Foo(x: int) returns (r: bool)
{
  r := x > 0;
}"""
        orig = self._write_temp(original)
        sub = self._write_temp(submitted)
        ok, msg = check_integrity(orig, sub)
        self.assertFalse(ok, "Should reject modified specification")
        os.unlink(orig)
        os.unlink(sub)

    def test_modified_method_signature(self):
        """Modifying a method signature should fail."""
        original = """method Foo(n: nat) returns (r: nat)
{
  r := n;
}"""
        submitted = """method Foo(n: nat, m: nat) returns (r: nat)
{
  r := n;
}"""
        orig = self._write_temp(original)
        sub = self._write_temp(submitted)
        ok, msg = check_integrity(orig, sub)
        self.assertFalse(ok, "Should reject modified method signature")
        os.unlink(orig)
        os.unlink(sub)

    def test_removed_method(self):
        """Removing a method should fail."""
        original = """method Foo(n: nat) returns (r: nat)
{
  r := n;
}

method Bar(n: nat) returns (r: nat)
{
  r := n + 1;
}"""
        submitted = """method Foo(n: nat) returns (r: nat)
{
  r := n;
}"""
        orig = self._write_temp(original)
        sub = self._write_temp(submitted)
        ok, msg = check_integrity(orig, sub)
        self.assertFalse(ok, "Should reject removed method")
        os.unlink(orig)
        os.unlink(sub)

    def test_complex_proof_annotations(self):
        """Adding complex proof annotations should pass."""
        original = """predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method BubbleSort(s: seq<int>) returns (r: seq<int>)
  ensures IsSorted(r)
  ensures multiset(r) == multiset(s)
{
  r := s;
  var n := |r|;
  var i := 0;
  while i < n
  {
    var j := 0;
    while j < n - i - 1
    {
      if r[j] > r[j+1]
      {
        r := r[j := r[j+1]][j+1 := r[j]];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}"""
        submitted = """predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma SortedHelper(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures true
{
}

method BubbleSort(s: seq<int>) returns (r: seq<int>)
  ensures IsSorted(r)
  ensures multiset(r) == multiset(s)
{
  r := s;
  var n := |r|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == n
    invariant multiset(r) == multiset(s)
  {
    var j := 0;
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant |r| == n
      invariant multiset(r) == multiset(s)
      invariant forall k, l :: 0 <= k < l < |r| && l > n - i - 1 ==>
        r[k] <= r[l]
    {
      if r[j] > r[j+1]
      {
        ghost var old_r := r;
        r := r[j := r[j+1]][j+1 := r[j]];
        assert multiset(r) == multiset(old_r);
      }
      j := j + 1;
    }
    i := i + 1;
  }
}"""
        orig = self._write_temp(original)
        sub = self._write_temp(submitted)
        ok, msg = check_integrity(orig, sub)
        self.assertTrue(ok, f"Should accept complex proof annotations. Got: {msg}")
        os.unlink(orig)
        os.unlink(sub)

    def test_assert_by_block(self):
        """Adding assert ... by { ... } blocks should pass."""
        original = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  r := i;
}"""
        submitted = """method Foo(n: nat) returns (r: nat)
{
  var i := 0;
  assert i == 0 by {
    assert true;
  }
  r := i;
}"""
        orig = self._write_temp(original)
        sub = self._write_temp(submitted)
        ok, msg = check_integrity(orig, sub)
        self.assertTrue(ok, f"Should accept assert-by blocks. Got: {msg}")
        os.unlink(orig)
        os.unlink(sub)


if __name__ == '__main__':
    unittest.main()
