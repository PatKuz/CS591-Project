    require import AllCore List.
    prover quorum=2 ["Z3" "Alt-Ergo"].


    module M1 = {
    

    proc isort(a : int list) : int list = {
        var i,j,x : int;
        i <- 1;

        while (i < size a){
            j <- i;
            while(0 < j &&  nth (-1) a (j) < (nth (-1) a (j-1))){
                x <- nth (-1) a j;
                a <- take (j-2) a ++ [x] ++ [nth (-1) a (j - 1)] ++ drop (j) a;
                j <- j - 1; 
            }
            i <- i + 1;
        }

        return a;
    }
    
    }.