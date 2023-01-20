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

        if len(payload.keys()) != 1:
            print(json.dumps({"error" : payload}))
        else:
            if "stop" in payload:
                if isinstance(payload["stop"], int):
                    print(json.dumps({"msg" : payload["stop"]}))
                    break

                print(json.dumps({"msg" : "Malformed payload", "payload" : line}))

            elif "cont" in payload:
                if isinstance(payload["cont"], int):
                    print(json.dumps({"msg" : payload["cont"]}))
                    continue
                print(json.dumps({"msg" : "Malformed payload", "payload" : line}))
            else:
                print(json.dumps({"error" : payload}))


if __name__ == "__main__":
    main()
