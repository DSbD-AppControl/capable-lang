"""A example external process that performs ping pong."""

import sys
import json

def main():
    """Main method"""
    for line in sys.stdin:
        try:
            payload = json.loads(line.rstrip())
            sys.stdin.flush

            if "msg" in payload and len(payload.keys()) == 1:
                print(json.dumps({"Msg" : payload.get("msg").get("Msg")}) + '\n', flush=True)
                break
            elif "quit" in payload and len(payload.keys()) == 1:
                print(json.dumps({"Msg" : payload.get("quit").get("Msg")}) + '\n', flush=True)

        except Exception as ex:
            print(json.dumps({"msg" : str(ex), "payload" : line}))
            break

if __name__ == "__main__":
    main()
