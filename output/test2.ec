require import AllCore IntDiv.

prover quorum=2 ["Z3" "Alt-Ergo"].

module M1 = {
  var c_fa9d65 : int
  var r : bool
  var i : int

  proc test() : int = {
  c_fa9d65 <- 0; 
  
  i <- 10;
  
  if(r){
      i <- i - 10;
  c_fa9d65 <- c_fa9d65 + 1;
  }else{
      i <- i + 10;
  c_fa9d65 <- c_fa9d65 + 1;
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
  var c_fa9d65 : int
  var r : bool
  var i : int

  proc test() : int = {
  var j : int;
  var cnt : int;
  c_fa9d65 <- 0; 
  
  cnt <- 0;
  j <- 0;

  while(j < i){
      cnt <- cnt + 10;
  c_fa9d65 <- c_fa9d65 + 1;
      j <- j + 1;
  c_fa9d65 <- c_fa9d65 + 1;
  }

 j <- 0;
  while(j < (100 - i)){
      cnt <- cnt - 10;
  c_fa9d65 <- c_fa9d65 + 1;
      j <- j + 1;
  c_fa9d65 <- c_fa9d65 + 1;
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
