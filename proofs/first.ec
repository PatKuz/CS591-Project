require import AllCore.
require import List.

prover quorum=2 ["Z3" "Alt-Ergo"].

module M2 = {
  var s1, s2 : bool list
  var l : bool list
  var r : bool
  var i : int

  proc compare() : bool = {
  r <- false;
  i <- 0;
  l <- [];

  while(i < size s1){
        l <- true::l;
        r <- (nth (false) s1 i = nth (false) s2 i) || r;
        i <- i + 1;
    }
        return r;
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

           
module M1 = {
  var s1, s2 : bool list
  var l : bool list
  var r : bool
  var i : int
  
  proc compare() : bool = {
  r <- true;
  i <- 0;
  l <- [];
    
  while (i < size s1){
  l <- true::l;
      if (nth (true) s1 i = nth (true) s2 i){
          l <- true::l;
      }else{
          l <- false::l;
          r <- false;
      }
      i <- i + 1;
    }
        l <- false::l;
    return r;
  }
}.
