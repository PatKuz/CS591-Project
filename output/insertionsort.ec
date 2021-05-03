    require import AllCore List.
    prover quorum=2 ["Z3" "Alt-Ergo"].


    module M1 = {
  var l_2d4d09 : bool list
    

    proc isort(a : int list) : int list = {
        var i,j,x : int;
  l_2d4d09 <- []; 
        i <- 1;

        while (i < size a){
  l_2d4d09 <- true::l_2d4d09;
            j <- i;
            while(0 < j &&  nth (-1) a (j) < (nth (-1) a (j-1))){
  l_2d4d09 <- true::l_2d4d09;
                x <- nth (-1) a j;
                a <- take (j-2) a ++ [x] ++ [nth (-1) a (j - 1)] ++ drop (j) a;
                j <- j - 1; 
            }
 l_2d4d09 <- false::l_2d4d09;
            i <- i + 1;
        }
 l_2d4d09 <- false::l_2d4d09;

        return a;
    }
    
    }.
