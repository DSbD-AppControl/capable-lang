"""A example external process that performs ping pong."""

import sys
import json

def main():
    """Main method"""
    for line in sys.stdin:
        try:
            payload = json.loads(line.rstrip())

        except ValueError as ex:
            print(json.dumps({"msg" : str(ex), "payload" : line}))
            continue

        if "msg" in payload and len(payload.keys()) == 1:
            print(json.dumps(payload))
        else:
            print(json.dumps({"msg" : str(ex), "payload" : line}))

if __name__ == "__main__":
    main()
