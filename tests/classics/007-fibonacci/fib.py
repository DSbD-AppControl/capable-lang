import sys
import json

def main():
    """Main method"""
    state = None;
    for line in sys.stdin:
        try:
            payload = json.loads(line.rstrip())
            sys.stdin.flush

            if "fibonacci" in payload and len(payload.keys()) == 1:
                p = None;
                if state == None:
                    p = payload["fibonacci"]
                else:
                    p = payload["fibonacci"] + state
                print(json.dumps({"num" : p }),flush=True)
                state = payload["fibonacci"]
                continue

            if "stop" in payload and len(payload.keys()) == 1:
                break

        except Exception as ex:
            print(json.dumps({"error" : str(ex), "payload" : line}))
            continue

if __name__ == "__main__":
    main()
