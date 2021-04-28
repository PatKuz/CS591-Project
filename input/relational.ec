require import AllCore List.
prover quorum=2 ["Z3" "Alt-Ergo"].


module M1 = {
  

  proc min(a : int list) : int = {
  var y, i : int;
  i <- 1;
  y <- nth 0 a 0;

  while(i < size a){
        if(nth 0 a i < y){
            y <- nth 0 a i;
        }
        i <- i + 1;
    }
        return y;
  }
}.