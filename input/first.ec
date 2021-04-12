require import AllCore.
require import List.

prover quorum=2 ["Z3" "Alt-Ergo"].

module M2 = {
  var s1, s2 : bool list
  var r : bool
  var i : int

  proc compare() : bool = {
  r <- false;
  i <- 0;

  while(i < size s1){
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
  var r : bool
  var i : int
  
  proc compare() : bool = {
  r <- true;
  i <- 0;
    
  while (i < size s1){
      if (nth (true) s1 i = nth (true) s2 i){
      }else{
          r <- false;
      }
      i <- i + 1;
    }
    return r;
  }
}.

(* The precondition is that the length of the bitstrings are always of equal 
length. The postcondition is that l{1} and l{2} are always equal length. It seems
like to be totally secure they should be equal but since the program is branching
on private data, l depends on private data. *)
lemma compare (_s1 _s2 : bool list):
equiv[M1.compare ~ M1.compare : size M1.s1{1} = size M1.s2{1} /\
    size M1.s1{2} = size M1.s2{2} /\ size M1.s1{1} = size M1.s1{2}
      ==> size M1.l{1} = size M1.l{2}]. 
    proof.
      proc.
      auto;auto.
    while(={M1.i} /\ size M1.s1{1} = size M1.s1{2} /\ 
      size M1.s1{1} = size M1.s2{1} /\ size M1.s1{2} = size M1.s2{2} /\
      M1.i{1} <= size M1.s1{1} /\ size M1.l{1} = size M1.l{2}).
      auto.
    smt().
      auto.
      smt(size_ge0).
qed.



