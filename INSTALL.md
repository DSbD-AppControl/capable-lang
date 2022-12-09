# Building, Installing, and Playing

## Building

To build and use Capable you will need [Idris2](https://github.com/idris-lang/Idris2).

Once Idris2 has been installed you can build the project with:

    make capable

The output should look something like:

```
$ make capable
idris2 --build capable.ipkg
1/53: Building Toolkit.Data.DList (src/Toolkit/Data/DList.idr)
...
```

## Testing

The test suite can be ran using:

    make test

## Installing

We have yet to add installation scripts or turn this into a serious tool to play with.
This might come later.

That being said, you can copy the binary from =build/exec= to a well known location under =PATH= and you should be able to use it from there.

## Playing

Capable is a very simple language with a simple UX.
We do not provide anything fancy as our interest at the moment is in the tool itself and not necessarily its use by others.

There are examples in the directory called =tests=.

<!-- EOF -->
