import sys
import json

def myReadLine():
    try:
      l = sys.stdin.readline().strip()
      msg = json.loads(l)
      sys.stdin.flush
      return msg
    except Exception as ex:
        print(json.dumps({"error" : str(ex), "payload" : l}))

def validMsg(key, msg):
    return key in msg and len(msg.keys()) == 1


def main():
    """Main method"""
    try:
       for i in [False, True, False, True]:
           msg = myReadLine()
           validMsg("c",msg)

    except Exception as ex:
        print(json.dumps({"error" : str(ex), "payload" : payload}))

if __name__ == "__main__":
    main()
