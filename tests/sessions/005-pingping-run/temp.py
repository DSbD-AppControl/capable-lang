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
                print(json.dumps({"msg" : payload["msg"]}),flush=True)
                continue

        except Exception as ex:
            print(json.dumps({"error" : str(ex), "payload" : line}))
            continue

if __name__ == "__main__":
    main()
