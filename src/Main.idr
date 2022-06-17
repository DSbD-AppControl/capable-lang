module Main

import Ola.Core
import Ola.Terms
import Ola.Exec

import Example

||| Run some examples...
main : IO ()
main
  = do Ola.run (exec example)
       Ola.run (exec example1)
       Ola.run (exec example2)
