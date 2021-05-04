require import IntDiv AllCore.
require import IntDiv List.
prover quorum=2 ["Z3" "Alt-Ergo"].
module M2 = {
  var c_59f1b3 : int
  var r : bool
  var i : int

  proc test() : bool = {
  c_59f1b3 <- 0; 
  r <- false;
  i <- 0;

  i <- 1 + 2;
  c_59f1b3 <- c_59f1b3 + 1;
  
  i <- 3 * 4;
  c_59f1b3 <- c_59f1b3 + 5;
  
  i <- 5 - 6;
  c_59f1b3 <- c_59f1b3 + 1;

  i <- 7 /% 8;

  return i;

  }
}.
