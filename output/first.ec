require import List AllCore.
require import List.
module M2 = {
  var l_2b8920 : bool list
  var s1, s2 : bool list
  var r : bool
  var i : int

  proc compare() : bool = {
  l_2b8920 <- []; 
  r <- false;
  i <- 0;

  while(i < size s1){
  l_2b8920 <- true::l_2b8920;
        r <- (nth (false) s1 i = nth (false) s2 i) || r;
        i <- i + 1;
    }
 l_2b8920 <- false::l_2b8920;
        return r;
  }
}.
module M1 = {
  var l_2b8920 : bool list
  var s1, s2 : bool list
  var r : bool
  var i : int
  
  proc compare() : bool = {
  l_2b8920 <- []; 
  r <- true;
  i <- 0;
    
  while (i < size s1){
  l_2b8920 <- true::l_2b8920;
      if (nth (true) s1 i = nth (true) s2 i){
 l_2b8920 <- true::l_2b8920;
      }else{
l_2b8920 <- false::l_2b8920;
          r <- false;
      }
      i <- i + 1;
    }
 l_2b8920 <- false::l_2b8920;
    return r;
  }
}.
