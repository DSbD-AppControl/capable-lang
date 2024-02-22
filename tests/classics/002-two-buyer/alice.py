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


class Quote(object):
    def __init__(self,val):
        self.val=val
    def toMSG(self):
        return {"quote" : self.val}

def validQuote(msg):
    if validMsg("quote",msg):
        return Quote(msg["quote"])
    else:
        raise Exception("Not Valid Quote")

def retort(msg):
    print(json.dumps(msg),flush=True)

def main():
    """Main method"""
    try:
       retort(Quote(30).toMSG())
    except Exception as ex:
        print(json.dumps({"error" : str(ex), "payload" : payload}))

if __name__ == "__main__":
    main()
