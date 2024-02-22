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

class Pair(object):
  def __init__(self, x, y):
      self.x = x
      self.y = y

  def fold(self):
      return int(self.x * self.y)

def validPair(msg):
    if validMsg("query",msg):
      p = msg["query"]
      if "x" in p and "y" in p and len(p.keys()) == 2:
        return Pair(int(p["x"]),int(p["y"]))
      else:
        raise Exception("not alid pair")
    else:
        raise Exception("Not valid query")

def retort(key,value):
    print(json.dumps({key : value }),flush=True)

def main():
    """Main method"""
    try:
       payload = myReadLine()
       p = validPair(payload)
       retort("resp", int(p.fold()))
    except Exception as ex:
        print(json.dumps({"error" : str(ex), "payload" : payload}))

if __name__ == "__main__":
    main()
