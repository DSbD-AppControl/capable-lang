"""A example external process that performs ping pong."""

import sys
import json

def main():
    """Main method"""
    for line in sys.stdin:
        try:
            payload = json.loads(line.rstrip())


            if "msg" in payload and len(payload.keys()) == 1:
                sys.stdout.write(json.dumps(payload) + '\n')
                break

        except Exception as ex:
            print(json.dumps({"msg" : str(ex), "payload" : line}))
            break

if __name__ == "__main__":
    main()
