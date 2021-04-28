import sys, secrets, argparse

bracketStack = []

inModule = False
lookingForVar = False
lookingForElse = False

def checkLineCF(line, newLines, l_name):
    global inModule
    global lookingForVar
    global lookingForElse

    
    if inModule and "}" in line:
        ret = (addEnd(bracketStack.pop(), l_name))
        if ("else" in ret):
            newLines.append(ret)
            lookingForElse = True
            checkLineCF(line, newLines, l_name)
            return
        else:
            line += ret

    if inModule and lookingForVar and not "var" in line:
        line = "  " + l_name +" <- []; \n" + line
        lookingForVar = False

    if "module" in line:
        inModule = True
        bracketStack.append("module")
        line += "\n  var " + l_name +" : bool list"
    elif inModule and ("while" in line) and ("{" in line):
        bracketStack.append("while")
        line += "\n  " + l_name +" <- true::" + l_name +";"
    elif inModule and ("if" in line) and (not "if." in line):
        bracketStack.append("if")
        line += "\n " + l_name +" <- true::" + l_name +";"
    elif inModule and "else" in line:
        bracketStack.append("else")
        line += "\n" + l_name +" <- false::" + l_name +";"
    elif inModule and ("proc" in line) and (not "proc." in line):
        #have to put after the lines that intalize vars in them
        bracketStack.append("proc")
        lookingForVar = True
    elif inModule and "{" in line:
        bracketStack.append("empty")

   

    if inModule and lookingForElse:
        if ('else' in line):
            lookingForElse = False
        elif not line.isspace() and (not line.replace('}', '').isspace()):
            #add else statement
            lookingForElse = False
            line = 'else{\n' + l_name + ' <- false::' + l_name + ';\n}' + line  

    #make sure List is added to the imports
    if ("require import" in line) and (not "List" in line):
        line = line[:line.index("require import") + len("require import")] + " List" + line[line.index("require import") + len("require import") :]


    newLines.append(line)


def addEnd(t, var_name):
    global inModule
    global lookingForElse
    if t == "module":
        inModule = False
        return ""
    if t == "if":
        if(lookingForElse):
            return 'else{\n' + var_name + ' <- false::' + var_name + ';\n}'
        lookingForElse = True
        return ""
    if t == "proc" or t == "empty" or t =="if" or t == "else":
        return ""
    else:
        return "\n " + var_name +" <- false::" + var_name +";"

def checkLineT(line, newLines, c_name):
    global inModule
    global lookingForVar

    if inModule and lookingForVar and not "var" in line:
        line = "  " + c_name +" <- 0; \n" + line
        lookingForVar = False

    if "module" in line:
        inModule = True
        bracketStack.append("module")
        line += "\n  var " + c_name +" : int"
    elif inModule and ('<-' in line and '+' in line.replace('<-','')):
        line += '\n  ' + c_name + ' <- ' + c_name +' + 1;'
    elif inModule and ('<-' in line and '-' in line.replace('<-','')):
        line += '\n  ' + c_name + ' <- ' + c_name +' + 1;'
    elif inModule and ('<-' in line and '*' in line.replace('<-','')):
        line += '\n  ' + c_name + ' <- ' + c_name +' + 5;'
    elif inModule and ('<-' in line and '%/' in line.replace('<-','')):
        line += '\n  ' + c_name + ' <- ' + c_name +' + 5;'
    elif inModule and ("proc" in line) and (not "proc." in line):
        #have to put after the lines that intalize vars in them
        bracketStack.append("proc")
        lookingForVar = True
    elif inModule and "{" in line:
        bracketStack.append("empty")

    if inModule and "}" in line:
         line += (addEnd(bracketStack.pop(), c_name))

    if ("require import" in line) and (not "IntDiv" in line):
        line = line[:line.index("require import") + len("require import")] + " IntDiv" + line[line.index("require import") + len("require import") :]

    newLines.append(line)
    

def init(var_name):
    global inModule
    inModule = False

    parser = argparse.ArgumentParser(description='tool that helps user check for side-channel free noninterference')
    parser.add_argument('-fn', '-filename', dest='file_name',required=True, help='file name')
    parser.add_argument('-at', '-attack_type', dest='attack_type', choices=['cf','controlflow','t', 'timing'], type=str.lower, help='side-channel attack', required=True)
    args = parser.parse_args()
    FILE_NAME = args.file_name
    ATTACK_TYPE = args.attack_type

    fileLines = []

    with open('input/'+FILE_NAME) as f:
        for line in f:
            l = line.rstrip('\n')
            if ATTACK_TYPE == 'cf' or ATTACK_TYPE == 'controlflow':
                checkLineCF(l, fileLines, ('l_'+var_name))
            else:
                checkLineT(l, fileLines, ('c_'+var_name))

    with open('output/'+FILE_NAME, 'w') as f:
        for line in fileLines:
            f.write(line+'\n')


if __name__ == '__main__':
    init(secrets.token_hex(3))
