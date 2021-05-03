require import AllCore IntDiv List.

prover quorum=2 ["Z3" "Alt-Ergo"].

module M1 = {
  var c_f9da02 : int
  var r : bool
  var i : int

  proc test() : int = {
  c_f9da02 <- 0;

  i <- 10;

  if(r){
  i <- i - 10;
  c_f9da02 <- c_f9da02 + 1;
    }else{
        i <- i + 10;
        c_f9da02 <- c_f9da02 + 1;
    }

        return i;
  }
}.

lemma test:
equiv[M1.test ~ M1.test :
     true ==> ={M1.c_f9da02}].
    proof.
      proc.
      auto.
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

lemma test2:
equiv[M2.test ~ M2.test :
     0 < M2.i{1} < 100 /\ 0 < M2.i{2} < 100 ==> ={M2.c_fa9d65}].
    proof.
      proc.
      seq 3 3 : (={cnt, j, M2.c_fa9d65} /\  0 < M2.i{1} < 100 /\ 0 < M2.i{2} < 100
      /\ cnt{1} = 0 /\ j{1} = 0 /\ M2.c_fa9d65{1}  = 0).
      auto.
      while {1} ( 0 < M2.i{1} < 100 /\ 0 < M2.i{2} < 100 /\
      M2.c_fa9d65{1} = M2.i{1} * 2 + j{1} * 2 /\ 
      0 <= j{1} <= (100 - M2.i{1})) ((100 - M2.i{1} - j{1})).
      auto;smt().

      while {2} ( 0 < M2.i{1} < 100 /\ 0 < M2.i{2} < 100 /\
      M2.c_fa9d65{2} = M2.i{2} * 2 + j{2} * 2 /\ 
      0 <= j{2} <= (100 - M2.i{2})) ((100 - M2.i{2} - j{2})).
      auto;smt().

     auto.

      while {1} ( 0 < M2.i{1} < 100 /\ 0 < M2.i{2} < 100 /\
      M2.c_fa9d65{1} = j{1} * 2 /\ 
      0 <= j{1} <= (M2.i{1})) ((M2.i{1} - j{1})).
      auto;smt().

      while {2} ( 0 < M2.i{1} < 100 /\ 0 < M2.i{2} < 100 /\
      M2.c_fa9d65{2} = j{2} * 2 /\ 
      0 <= j{2} <= (M2.i{2})) ((M2.i{2} - j{2})).
      auto;smt().

      skip;smt().

  qed.
  
