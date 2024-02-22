"""A example external process that performs ping pong."""

import sys
import json

def myReadLine():
    try:
      l = sys.stdin.readline().strip()
      msg = json.loads(l)
      sys.stdin.flush
    except Exception as ex:
        print(json.dumps({"error" : str(ex), "payload" : l}))

    return msg

def validMsg(key, msg):
    return key in msg and len(msg.keys()) == 1

def retort(key,value):
    print(json.dumps({key : value }),flush=True)

def main():
    """Main method"""
    msg1 = myReadLine()
    if validMsg("token", msg1):
        if msg1["token"] == "Reviewer B":
          retort("ok",None);
          msg2 = myReadLine()
          if validMsg("yes",msg2):
              retort("result",1)
          elif validMsg("no",msg2):
              retort("result",2)
          else:
              print("Invalid Response")
        else:
            retort("reject", None)
    else:
        print("Invalid Response")


if __name__ == "__main__":
    main()
