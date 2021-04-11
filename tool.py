import sys

def checkLine(line, newLines):
    print("placeholder")

def init():
    try:
        FILE_NAME = str(sys.argv[1])
    except:
        print('[ERROR] Usage: python3 tool.py <FILE_NAME>')

    fileLines = []
    with open('input/'+FILE_NAME) as f:
        for line in f:
            l = line.rstrip('\n')
            fileLines.append(l)
            checkLine(l, fileLines)

    with open('output/'+FILE_NAME, 'w') as f:
        for line in fileLines:
            f.write(line+'\n')


if __name__ == '__main__':
    init()
