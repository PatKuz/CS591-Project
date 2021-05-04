require import AllCore.
require import List.

prover quorum=2 ["Z3" "Alt-Ergo"].

module M2 = {
  var r : bool
  var i : int

  proc test() : bool = {
  r <- false;
  i <- 0;

  i <- 1 + 2;
  
  i <- 3 * 4;
  
  i <- 5 - 6;

  i <- 7 /% 8;

  return i;

  }
}.

lemma fixed_compare (_s1 _s2 : bool list):
equiv[M2.compare ~ M2.compare : size M2.s1{1} = size M2.s2{1} /\
      size M2.s1{2} = size M2.s2{2} /\ size M2.s1{1} = size M2.s1{2}
      ==> ={M2.l}].
    proof.
    proc.    
    while(={M2.l, M2.i} /\ size M2.s1{1} = size M2.s2{1} /\
      size M2.s1{2} = size M2.s2{2} /\ size M2.s1{1} = size M2.s1{2});auto;smt().
  qed.