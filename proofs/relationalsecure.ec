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

lemma secureMin:
equiv [M1.min ~ M1.min : size a{1} = size a{2} /\ 1 <= size a{1} /\ 
    forall(x, c: int), 0 <= x <= size a{1} /\ 0 <= c <= size a{1} =>
      (nth 0 a{1} x < nth 0 a{1} c <=> nth 0 a{2} x < nth 0 a{2} c) 
      ==> ={M1.l_df77cf}].
        proc.
        seq 3 3 : (={i, M1.l_df77cf} /\ size a{1} = size a{2} /\ 1 <= size a{1} /\
           (forall(x, c: int), 0 <= x <= size a{1} /\ 0 <= c <= size a{1} =>
      (nth 0 a{1} x < nth 0 a{1} c <=> nth 0 a{2} x < nth 0 a{2} c)) /\
    i{1} = 1 /\ M1.l_df77cf{1} = [] /\
    y{1} = nth 0 a{1} 0 /\ y{2} = nth 0 a{2} 0);auto.

    while(={i, M1.l_df77cf} /\ 0 < i{1} /\  size a{1} = size a {2} /\
        (forall(x, c: int), 0 <= x <= size a{1} /\ 0 <= c <= size a{1} =>
      (nth 0 a{1} x < nth 0 a{1} c <=> nth 0 a{2} x < nth 0 a{2} c)) /\
        i{1} <= size a{1} /\ ((forall(k: int), (0 <= k <= size a{1} =>
          (nth 0 a{1} k < y{1} <=> nth 0 a{2} k < y{2})))));auto;smt().
        
  qed.
