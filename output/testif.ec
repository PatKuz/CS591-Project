'require import AllCore List.\n'
'prover quorum=2 ["Z3" "Alt-Ergo"].\n'
'\n'
'\n'
'module M1 = {\n  var l_bd1fda : bool list\n'
'  \n'
'\n'
'  proc min(a : int list) : int = {\n'
'  var y, i : int;\n'
'  l_bd1fda <- []; \n  i <- 1;\n'
'  y <- nth 0 a 0;\n'
'\n'
'  if(true){\n l_bd1fda <- true::l_bd1fda;\n'
'\n'
'  }else{\nl_bd1fda <- false::l_bd1fda;\n'
'\n'
'  }\n'
'\n'
'  if(true){\n l_bd1fda <- true::l_bd1fda;\n'
'\n'
'  }\n'
'else{\nl_bd1fda <- false::l_bd1fda;\n}\n'
'\n'
'   if(true){\n l_bd1fda <- true::l_bd1fda;\n'
'\n'
'   }\n'
'   else{\nl_bd1fda <- false::l_bd1fda;\n'
'\n'
'   }\n'
'\n'
'\n'
'    if(true){\n l_bd1fda <- true::l_bd1fda;\n'
'        if(true){\n l_bd1fda <- true::l_bd1fda;\n'
'            \n'
'        }\n'
'else{\nl_bd1fda <- false::l_bd1fda;\n}\n'
'    }\n'
'else{\nl_bd1fda <- false::l_bd1fda;\n}\n'
'\n'
'}.\n'