||| IPC code.
|||
||| We assume that messages are received and sent on lines.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Exec.IPC

import Data.Maybe
import Data.Vect
import Data.String
import Data.List.Elem
import Data.List1.Elem
import Data.List.Quantifiers

import Data.String
import System.File
import System.Escape

import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Context.Item
import Toolkit.Data.Vect.Extra
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Capable.Core
import Capable.Terms

import Capable.Values
import Capable.Values.Marshall

import Capable.Exec.Env
import Capable.Exec.Common


%default total

||| Representing a set of typed channels involved within a MPST
||| communication context.
|||
||| Notes about the datatypes contained within.
|||
||| + We assume that we are _just_ dealing with the IPC context.
||| + We do not need to type them with a session type, the expressions that detail the communication to that.
||| + The representation is not 'sparse' we create a 'channel'  for each role defined. This _will_ result in a more verbose data structure. A simple datatype 'Channel' provides a place holder for unused channels.
||| + Ideally we would have a sub-context that only contains channels for roles involved in the communication. It is not clear how to provide such an elegant context.
|||   + We would need a _thinning_ of the role context based on if a role is involved in the communication.
|||   + roles are, however, nameless against the entire role context.
|||   + So our thinning would need to be rather magical.
export
data Channel : (role : Ty.Role)
                    -> Type
  where

    UsedNot : Channel role

    Closed : Channel role
    Waiting : (str : String) -> Channel role
    Open : (h : SubProcess)
             -> Channel role



public export
Channels : List Ty.Role -> Type
Channels = DList Ty.Role Channel

||| By default creates a list of unused channels.
fromEnv : Context Role rs -> Channels rs
fromEnv = map (const UsedNot)

init1 : (loc : IsVar roles x)
     -> (val : Value store STR)
     -> (cs  : Channels roles)
            -> Channels roles
init1 loc (S str)
  = update loc (Waiting str)

initDO : Assignments roles store ps
      -> Channels roles
      -> Channels roles
initDO Empty y = y
initDO (KV loc val rest) y
  = initDO rest (init1 loc val y)

export
init : Context Role roles
    -> Assignments       roles store ps
    -> Capable (Channels roles)
init rs as = pure $ initDO as (fromEnv rs)

start : Channel role -> Capable (Channel role)
start (Waiting str)
  = either (error)
           (pure . Open)
           (!(embed $ popen2 str))
start UsedNot = pure $ UsedNot
start _
  = panic "Error starting channel"

export
startAll : Channels roles -> Capable (Channels roles)
startAll = traverse start


close : Channel role -> Capable (Channel role)
close (Open fh)
  = do _ <- embed (pclose (input fh))
       _ <- embed (pclose (output fh))
       pure Closed
close UsedNot = pure $ UsedNot
close _
  = panic "Error closing channel"

export
closeAll : Channels roles -> Capable (Channels roles)
closeAll
  = traverse close


export
sendOn : (str   : String)
      -> (chan  : IsVar    roles role)
      -> (chans : Channels roles)
               -> Capable ()
sendOn str idx chans
  = case read idx chans of
      Open fh
        => do res <- embed $ fPutStrLn (input fh) (trim str)
              embed $ fflush (input fh)
              either (error)
                     (const $ pure ())
                     res
      _ => panic "Channel in wrong state."

export
recvOn : (chan  : IsVar roles role)
      -> (chans : Channels roles)
               -> Capable String
recvOn idx chans
  = case read idx chans of
      Open fh
        => do res <- embed (fGetLine (output fh))
              embed $ fflush (output fh)
              either error
                     (\res => pure (trim res))
                     res

      _ => panic "Channel in wrong state."

-- [ EOF ]
