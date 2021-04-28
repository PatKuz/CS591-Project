require import AllCore List.
prover quorum=2 ["Z3" "Alt-Ergo"].


module M1 = {
  var l_7de00c : bool list
  

  proc min(a : int list) : int = {
  var y, i : int;
  l_7de00c <- []; 
  i <- 1;
  y <- nth 0 a 0;

  if(true){
 l_7de00c <- true::l_7de00c;

  }else{
l_7de00c <- false::l_7de00c;

  }

  if(true){
 l_7de00c <- true::l_7de00c;

  }
else{
l_7de00c <- false::l_7de00c;
}

   if(true){
 l_7de00c <- true::l_7de00c;

   }
   else{
l_7de00c <- false::l_7de00c;

   }


    if(true){
 l_7de00c <- true::l_7de00c;
        if(true){
 l_7de00c <- true::l_7de00c;
            
        }
else{
l_7de00c <- false::l_7de00c;
}
    }
else{
l_7de00c <- false::l_7de00c;
}

}.
