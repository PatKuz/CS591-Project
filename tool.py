import sys, secrets

bracketStack = []

inModule = False

def checkLine(line, newLines, l_name):
    whitespace = (len(line) - len(line.lstrip()))+1
    # print(whitespace)
    global inModule
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
        line += "\n " + l_name +" <- [];"
    elif inModule and "{" in line:
        bracketStack.append("empty")

    if inModule and "}" in line:
         line += (addEnd(bracketStack.pop()))

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


def init(l_name):
    global inModule
    inModule = False
    try:
        FILE_NAME = str(sys.argv[1])
    except:
        print('[ERROR] Usage: python3 tool.py <FILE_NAME> <>')

    fileLines = []
    with open('input/'+FILE_NAME) as f:
        for line in f:
            l = line.rstrip('\n')
            checkLine(l, fileLines, l_name)

    with open('output/'+FILE_NAME, 'w') as f:
        for line in fileLines:
            f.write(line+'\n')


if __name__ == '__main__':
    init(("l_"+secrets.token_hex(8)))
