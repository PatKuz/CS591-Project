require import AllCore List.
prover quorum=2 ["Z3" "Alt-Ergo"].


module M1 = {
  var l_df77cf : bool list
  

  proc min(a : int list) : int = {
  var y, i : int;
  l_df77cf <- []; 
  i <- 1;
  y <- nth 0 a 0;

  while(i < size a){
    l_df77cf <- true::l_df77cf;
    if(nth 0 a i < y){
      l_df77cf <- true::l_df77cf;
      y <- nth 0 a i;
    }
    else{
      l_df77cf <- false::l_df77cf;
    }
        i <- i + 1;
    }
    l_df77cf <- false::l_df77cf;
    return y;
  }
}.
