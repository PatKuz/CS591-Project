require import IntDiv AllCore.
require import IntDiv List.

prover quorum=2 ["Z3" "Alt-Ergo"].

module M2 = {
  var c_66d78a : int
  var r : bool
  var i : int

  proc test() : bool = {
  c_66d78a <- 0; 
  r <- false;
  i <- 0;

  i <- 1 + 2;
  c_66d78a <- c_66d78a + 1;
  
  i <- 3 * 4;
  c_66d78a <- c_66d78a + 5;
  
  i <- 5 - 6;
  c_66d78a <- c_66d78a + 1;

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
