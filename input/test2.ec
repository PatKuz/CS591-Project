require import AllCore IntDiv.

prover quorum=2 ["Z3" "Alt-Ergo"].

module M1 = {
  var r : bool
  var i : int

  proc test() : int = {
  
  i <- 10;
  
  if(r){
      i <- i - 10;
  }else{
      i <- i + 10;
  }

  return i;
  }
}.

lemma test:
equiv[M1.test ~ M1.test : 
      ==> ={M2.c}].
    proof.
    proc.    
  
  qed.



module M2 = {
  var r : bool
  var i : int

  proc test() : int = {
  var j : int;
  var cnt : int;
  
  cnt <- 0;
  j <- 0;

  while(j < i){
      cnt <- cnt + 10;
      j <- j + 1;
  }

 j <- 0;
  while(j < (100 - i)){
      cnt <- cnt - 10;
      j <- j + 1;
  }
  

  return i;
  }
}.


lemma test:
equiv[M1.test ~ M1.test : 
      ==> ={M2.c}].
    proof.
    proc.    
  
  qed.
