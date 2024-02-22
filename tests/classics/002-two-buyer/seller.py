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

class NewType(object):
    def __init__(self,key,val):
        self.key = key
        self.val=val
    def toMSG(self):
        return {self.key : self.val}

    def toJSON(self):
        return json.dumps(self.toMSG())

def validNewType(key, msg):
    if validMsg(key,msg):
        return NewType(key,msg[key])
    else:
        raise Exception("Not Valid newtype")

class EnumMSG(object):
    def __init__(self,tag):
        self.tag = tag

    def toMSG(self):
        return { self.tag : None}

    def toJSON(self):
        return json.dumps(self.toMSG())

def validEnumMSG(key,msg):
    if validMsg(key,msg) and msg[key] == None:
        return EnumMSG(msg[key])
    else:
        raise Exception("Not Valid Enum")


def retort(msg):
    print(msg,flush=True)

def main():
    """Main method"""
    try:
       retort(NewType("quote",60).toJSON())
       raw_msg = myReadLine()
       if validMsg("quit", raw_msg):
           validEnumMSG("quit",raw_msg)
       elif validMsg("accept",raw_msg):
           validEnumMSG("accept",raw_msg)
           raw_msg_add = myReadLine()
           addr = validNewType("addr",raw_msg_add)
           retort(NewType("date","tomorrow").toJSON())
       else:
           raise Exception("Not a valid step")


    except Exception as ex:
        print(ex)

if __name__ == "__main__":
    main()
