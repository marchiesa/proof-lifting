// DFA matching loop — abstracted from Rust's regex-automata crate
// (regex-automata/src/dfa/automaton.rs)
//
// Version using input slicing instead of index parameter.

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

function StateAfter(transition: seq<seq<nat>>, start: nat, input: seq<int>): (result: nat)
  requires |transition| > 0
  requires start < |transition|
  requires forall i :: 0 <= i < |input| ==> 0 <= input[i] < NUM_BYTES
  requires forall s :: 0 <= s < |transition| ==>
    |transition[s]| == NUM_BYTES &&
    (forall b :: 0 <= b < NUM_BYTES ==> transition[s][b] < |transition|)
  ensures result < |transition|
  decreases |input|
{
  if |input| == 0 then start
  else
    var prev := StateAfter(transition, start, input[..|input|-1]);
    transition[prev][input[|input|-1]]
}

method DFAMatch(
    numStates: nat,
    start: nat,
    transition: seq<seq<nat>>,
    accept: set<nat>,
    input: seq<int>
  ) returns (matched: bool)
  requires ValidDFA(numStates, start, transition, accept)
  requires forall i :: 0 <= i < |input| ==> 0 <= input[i] < NUM_BYTES
  ensures matched == (StateAfter(transition, start, input) in accept)
{
  var state := start;
  var i := 0;

  while i < |input|
    invariant 0 <= i <= |input|
    invariant state == StateAfter(transition, start, input[..i])
    invariant state < numStates
  {
    assert input[..i+1] == input[..i] + [input[i]];
    state := transition[state][input[i]];
    i := i + 1;
  }

  assert input[..|input|] == input;
  matched := state in accept;
}
