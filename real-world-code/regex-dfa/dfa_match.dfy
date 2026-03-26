// DFA matching loop — abstracted from Rust's regex-automata crate
// (regex-automata/src/dfa/automaton.rs)
//
// The real code walks a transition table one byte at a time.
// We keep exactly that logic, just without the Rust-specific details.

const NUM_BYTES: int := 256

predicate ValidDFA(numStates: nat, start: nat, transition: seq<seq<nat>>, accept: set<nat>)
{
  numStates > 0 &&
  start < numStates &&
  |transition| == numStates &&
  (forall s :: 0 <= s < numStates ==>
    |transition[s]| == NUM_BYTES &&
    (forall b :: 0 <= b < NUM_BYTES ==> transition[s][b] < numStates)) &&
  (forall s :: s in accept ==> s < numStates)
}

// Mathematical definition: state reached after processing input[..k]
function StateAfter(transition: seq<seq<nat>>, start: nat, input: seq<int>, k: nat): (result: nat)
  requires k <= |input|
  requires |transition| > 0
  requires start < |transition|
  requires forall i :: 0 <= i < |input| ==> 0 <= input[i] < NUM_BYTES
  requires forall s :: 0 <= s < |transition| ==>
    |transition[s]| == NUM_BYTES &&
    (forall b :: 0 <= b < NUM_BYTES ==> transition[s][b] < |transition|)
  ensures result < |transition|
  decreases k
{
  if k == 0 then start
  else
    var prev := StateAfter(transition, start, input, k - 1);
    transition[prev][input[k - 1]]
}

// The DFA matching method — directly models the Rust code's main loop
method DFAMatch(
    numStates: nat,
    start: nat,
    transition: seq<seq<nat>>,
    accept: set<nat>,
    input: seq<int>
  ) returns (matched: bool)
  requires ValidDFA(numStates, start, transition, accept)
  requires forall i :: 0 <= i < |input| ==> 0 <= input[i] < NUM_BYTES
  ensures matched == (StateAfter(transition, start, input, |input|) in accept)
{
  var state := start;
  var i := 0;

  while i < |input|
    invariant 0 <= i <= |input|
    invariant state == StateAfter(transition, start, input, i)
    invariant state < numStates
  {
    state := transition[state][input[i]];
    i := i + 1;
  }

  matched := state in accept;
}
