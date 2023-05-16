"""A example external process that performs ping pong."""

import sys
import json

def main():
    """Main method"""
    for line in sys.stdin:
        try:
            payload = json.loads(line.rstrip())


            if "stop" in payload and len(payload.keys()) == 1:
                sys.stdout.write(json.dumps({"msg" : payload["stop"]}) + '\n')
                break

            if "cont" in payload and len(payload.keys()) == 1:
                sys.stdout.write(json.dumps({"msg" : payload["cont"]}) + '\n')
                continue

        except Exception as ex:
            print(json.dumps({"error" : str(ex), "payload" : line}))
            continue

if __name__ == "__main__":
    main()
