lemma LemmaTakeTake<T>()
  ensures forall l: seq<T>, n, m: nat {:trigger l[..m][..n]} :: 0 <= n <= m <= |l| ==> (l[..m])[..n] == l[..n]
{
}
lemma LemmaTakeAppend<T>()
  ensures forall s, t: seq<T>, n: nat {:trigger (s+t)[..n]} :: 0 <= n <= |s| ==> (s+t)[..n] == s[..n]
  ensures forall s, t: seq<T>, n: nat :: |s| <= n <= |s|+|t| ==> (s+t)[..n] == s + t[..n-|s|]
{
}
lemma LemmaFullSlice<T>()
  ensures forall s: seq<T> {:trigger s[..|s|]} :: s[..|s|] == s
{
}

lemma LemmaEmptyAdd<T>()
  ensures forall s, t: seq<T> :: t == [] ==> s + t == s && t + s == s
{
}

lemma LemmaSequenceTheoryAuto<T>()
  ensures forall l: seq<T>, n, m: nat {:trigger l[..m][..n]} :: 0 <= n <= m <= |l| ==> (l[..m])[..n] == l[..n]
  ensures forall s, t: seq<T>, n: nat {:trigger (s+t)[..n]} :: 0 <= n <= |s| ==> (s+t)[..n] == s[..n]
  ensures forall s, t: seq<T>, n: nat {:trigger (s+t)[..n]} :: |s| <= n <= |s|+|t| ==> (s+t)[..n] == s + t[..n-|s|]
  ensures forall s: seq<T> {:trigger s[..|s|]} :: s[..|s|] == s
  ensures forall s, t: seq<T> :: t == [] ==> s + t == s && t + s == s
{}