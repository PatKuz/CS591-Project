import sys, secrets, argparse

bracketStack = []

inModule = False
lookingForVar = False

def checkLineCF(line, newLines, l_name):
    global inModule
    global lookingForVar

    if inModule and lookingForVar and not "var" in line:
        line = "" + l_name +" <- []; \n" + line
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

    if inModule and "}" in line:
         line += (addEnd(bracketStack.pop(), l_name))

    #make sure List is added to the imports
    if ("require import" in line) and (not "List" in line):
        line = line[:line.index("require import") + len("require import")] + " List" + line[line.index("require import") + len("require import") :]


    newLines.append(line)


def addEnd(t, l_name):
    global inModule
    if t == "module":
        inModule = False
        return ""
    if t == "proc" or t == "empty" or t =="if" or t == "else":
        return ""
    else:
        return "\n " + l_name +" <- false::" + l_name +";"

def checkLineT(line, newLines, c_name):
    global inModule
    global lookingForVar

    if inModule and lookingForVar and not "var" in line:
        line = "" + c_name +" <- 0; \n" + line
        lookingForVar = False

    if "module" in line:
        inModule = True
        bracketStack.append("module")
        line += "\n  var " + c_name +" : int"
    elif inModule and ("+" in line) and ('<-' in line):
        line += '\n  c <- c + 1;'
    elif inModule and ("-" in line) and ('<-' in line):
        line += '\n  c <- c + 1;'
    elif inModule and ("*" in line) and ('<-' in line):
        line += '\n  c <- c + 5;'
    elif inModule and ("/%" in line) and ('<-' in line):
        line += '\n  c <- c + 5;'
    elif inModule and ("proc" in line) and (not "proc." in line):
        #have to put after the lines that intalize vars in them
        bracketStack.append("proc")
        lookingForVar = True
    elif inModule and "{" in line:
        bracketStack.append("empty")

    if inModule and "}" in line:
         line += (addEnd(bracketStack.pop(), l_name))

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
                checkLineT(l, filenames, ('c_'+var_name))

    with open('output/'+FILE_NAME, 'w') as f:
        for line in fileLines:
            f.write(line+'\n')


if __name__ == '__main__':
    init(secrets.token_hex(3))
