import sys

bracketStack = [] 

def checkLine(line, newLines):
    #find out how much white space to add to the start of a new line
    if "module" in line:
        bracketStack.append("module")
        line += "\n  var l : bool list"
    elif "while" in line:
        bracketStack.append("while")
        line += "\n  l <- true::l;" 
    elif "if" in line:
        bracketStack.append("if")
        line += "\n l <- true::l;"
    elif "else" in line:
        bracketStack.append("else")
        line += "\n l <- false::l;"
    elif "proc" in line:
        bracketStack.append("proc")
        line += "\n l <- [];"
    elif "{" in line:
        bracketStack.append("empty")

    if "}" in line:
         line += addEnd(bracketStack.pop())

    

    newLines.append(line)


def addEnd(t):
    print("This is called")
    print(t)
    if t == "module" or t == "proc" or t == "empty" or t =="if" or t == "else":
        return ""
    else:
        print("We are in here")
        return "\n l <- false::l"
    

def init():
    try:
        FILE_NAME = str(sys.argv[1])
    except:
        print('[ERROR] Usage: python3 tool.py <FILE_NAME>')

    fileLines = []
    with open('input/'+FILE_NAME) as f:
        for line in f:
            l = line.rstrip('\n')
            # fileLines.append(l)
            checkLine(l, fileLines)

    with open('output/'+FILE_NAME, 'w') as f:
        for line in fileLines:
            f.write(line+'\n')

 
if __name__ == '__main__':
    init()
