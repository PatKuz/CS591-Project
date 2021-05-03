require import AllCore.
require import List.

prover quorum=2 ["Z3" "Alt-Ergo"].


module M1 = {
    var x, y: int (* public *)

    (* m is private *)

    proc f(m) : int{
        var temp : int;
        temp <- m;

        if(x = y){
            m <- m +5;
        }else{
            m <- m;
        }
        if(temp==m){
            m <- m + 1;
        }else{
            m <- m + 1;
        }
    }
    return m;
}
