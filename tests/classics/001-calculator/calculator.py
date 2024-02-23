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

class Command(object):
    def __init__(self, kind, x, y):
        self.kind = kind
        self.left = x
        self.right = y

    def compute(self):
        if self.kind == "adder":
            return json.dumps({ "answer" : self.left + self.right})
        elif self.kind == "suber":
            return json.dumps({ "answer" : self.left - self.right})
        elif self.kind == "diver":
            payload = None

            if self.right == 0:
                payload = { "divByZero" : None }
            else:
                payload = { "answerE" : floor(self.left / self.right)}
            return json.dumps( payload )
        elif self.kind == "muler":
            return json.dumps({ "answer" : self.left * self.right})
        else:
            raise Exception("Not a valid computation")

def validCommand(msg):
    if len(msg.keys()) == 1:
        kind = list(msg.keys())[0]
        x = (msg[kind])["x"]
        y = (msg[kind])["y"]
        return Command(kind,x,y)
    else:
        raise Exception("Not Valid Enum")


def retort(msg):
    print(msg,flush=True)

def main():
    """Main method"""
    try:
       raw_msg = myReadLine()
       cmd = validCommand(raw_msg)

       retort(cmd.compute())

    except Exception as ex:
        print(ex)

if __name__ == "__main__":
    main()
