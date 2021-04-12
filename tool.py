import sys

bracketStack = []

inModule = False

def checkLine(line, newLines):
    whitespace = (len(line) - len(line.lstrip()))+1
    # print(whitespace)
    global inModule
    if "module" in line:
        inModule = True
        bracketStack.append("module")
        line += "\n  var l : bool list"
    elif inModule and ("while" in line) and ("{" in line):
        bracketStack.append("while")
        line += "\n  l <- true::l;"
    elif inModule and ("if" in line) and (not "if." in line):
        bracketStack.append("if")
        line += "\n l <- true::l;"
    elif inModule and "else" in line:
        bracketStack.append("else")
        line += "\nl <- false::l;"
    elif inModule and ("proc" in line) and (not "proc." in line):
        #have to put after the lines that intalize vars in them 
        bracketStack.append("proc")
        line += "\n l <- [];"
    elif inModule and "{" in line:
        bracketStack.append("empty")

    if inModule and "}" in line:
         line += (addEnd(bracketStack.pop()))

    #make sure List is added to the imports
    if ("require import" in line) and (not "List" in line):
        line = line[:line.index("require import") + len("require import")] + " List" + line[line.index("require import") + len("require import") :]


    newLines.append(line)


def addEnd(t):
    global inModule
    if t == "module":
        inModule = False
        return ""
    if t == "proc" or t == "empty" or t =="if" or t == "else":
        return ""
    else:
        return "\n l <- false::l;"


def init():
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
            checkLine(l, fileLines)

    with open('output/'+FILE_NAME, 'w') as f:
        for line in fileLines:
            f.write(line+'\n')


if __name__ == '__main__':
    init()
