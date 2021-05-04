require import List AllCore.
require import List.

prover quorum=2 ["Z3" "Alt-Ergo"].


module M1 = {
  var l_490245 : bool list
    var x, y: int (* public *)

    (* m is private *)

    proc f(m) : int{
        var temp : int;
  l_490245 <- []; 
        temp <- m;

        if(x = y){
 l_490245 <- true::l_490245;
            m <- m +5;
        }else{
l_490245 <- false::l_490245;
            m <- m;
        }
        if(temp==m){
 l_490245 <- true::l_490245;
            m <- m + 1;
        }else{
l_490245 <- false::l_490245;
            m <- m + 1;
        }
    }
    return m;
}
