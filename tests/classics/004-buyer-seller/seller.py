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
    while True:
      try:
         payload = myReadLine()
         if validMsg("product",payload):
             retort("price",123)
             retort("quote", "blah")
             continue
         elif validMsg("accept",payload):
             blah = payload["accept"]
             q = myReadLine()
             if validMsg("payment",q):
                 continue
             else:
                 raise Exception("oos")
         elif validMsg("quit",payload):
             break
         else:
             raise Exception("Oos")

      except Exception as ex:
          print(json.dumps({"error" : str(ex), "payload" : line}))
          continue

if __name__ == "__main__":
    main()
