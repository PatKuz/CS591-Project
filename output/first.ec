require import List AllCore.
require import List.
prover quorum=2 ["Z3" "Alt-Ergo"].
module M2 = {
  var l_e8cdb9 : bool list
  var s1, s2 : bool list
  var r : bool
  var i : int

  proc compare() : bool = {
  l_e8cdb9 <- []; 
  r <- false;
  i <- 0;

  while(i < size s1){
  l_e8cdb9 <- true::l_e8cdb9;
        r <- (nth (false) s1 i = nth (false) s2 i) || r;
        i <- i + 1;
    }
 l_e8cdb9 <- false::l_e8cdb9;
        return r;
  }
}.
module M1 = {
  var l_e8cdb9 : bool list
  var s1, s2 : bool list
  var r : bool
  var i : int
  
  proc compare() : bool = {
  l_e8cdb9 <- []; 
  r <- true;
  i <- 0;
    
  while (i < size s1){
  l_e8cdb9 <- true::l_e8cdb9;
      if (nth (true) s1 i = nth (true) s2 i){
 l_e8cdb9 <- true::l_e8cdb9;
      }else{
l_e8cdb9 <- false::l_e8cdb9;
          r <- false;
      }
      i <- i + 1;
    }
 l_e8cdb9 <- false::l_e8cdb9;
    return r;
  }
}.
