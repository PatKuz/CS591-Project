require import List AllCore.
require import List.
prover quorum=2 ["Z3" "Alt-Ergo"].
module M1 = {
  var l_bb2a5b : bool list
    var x, y: int (* public *)

    (* m is private *)

    proc f(m) : int{
        var temp : int;
  l_bb2a5b <- []; 
        temp <- m;

        if(x = y){
 l_bb2a5b <- true::l_bb2a5b;
            m <- m +5;
        }else{
l_bb2a5b <- false::l_bb2a5b;
            m <- m;
        }
        if(temp==m){
 l_bb2a5b <- true::l_bb2a5b;
            m <- m + 1;
        }else{
l_bb2a5b <- false::l_bb2a5b;
            m <- m + 1;
        }
    }
    return m;
}
