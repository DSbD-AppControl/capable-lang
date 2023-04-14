"""A example external process that performs ping pong."""

import sys
import json

def main():
    """Main method"""
    for line in sys.stdin:

        sys.stdout.write(":OF AA\n")
        break


if __name__ == "__main__":
    main()
