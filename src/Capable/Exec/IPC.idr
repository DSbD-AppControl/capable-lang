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

import System.File

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

traverse : (f  : forall a . e a -> Capable (e a))
        -> (xs : DList ty e ts)
              -> Capable (DList ty e ts)
traverse f []
  = pure []
traverse f (elem :: rest)
  = do x <- f elem
       xs <- traverse f rest
       pure (x::xs)

traverse_ : (f  : forall a . e a -> Capable ())
         -> (xs : DList ty e ts)
               -> Capable ()
traverse_ f []
  = pure ()
traverse_ f (elem :: rest)
  = do f elem
       traverse_ f rest

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
namespace Channel


  public export
  data Channel : (role : Ty.Role)
                      -> Type
    where

      UsedNot : Channel role

      Closed : Channel role
      Waiting : (str : String) -> Channel role
      Open : (h : File)
               -> Channel role



  public export
  Channels : List Ty.Role -> Type
  Channels = DList Ty.Role Channel


process : Assign roles store role
       -> Channel            role
process AssignedNot
  = UsedNot
process (Assigned prf (S str))
  = Waiting str

export
populate : Assignments roles store
        -> Channels    roles
populate = map process

start : Channel role -> Capable (Channel role)
start (Waiting str)
  = either (error)
           (pure . Open)
           (!(embed $ popen str ReadWrite))
start UsedNot = pure $ UsedNot
start _
  = panic "Error starting channel"

export
startAll : Channels roles -> Capable (Channels roles)
startAll = traverse start


close : Channel role -> Capable (Channel role)
close (Open fh)
  = do _ <- embed (pclose fh)
       pure Closed
close UsedNot = pure $ UsedNot
close _
  = panic "Error starting channel"

export
closeAll : Channels roles -> Capable (Channels roles)
closeAll
  = traverse close


export
sendOn : (Value store STR)
      -> (chan  : IsVar    roles role)
      -> (chans : Channels roles)
               -> Capable ()
sendOn (S str) idx chans
  = case read idx chans of
      Open fh
        => either (error)
                  (const $ pure ())
                  (!(embed $ fPutStrLn fh str))

      _ => panic "Channel in wrong state."

export
recvOn : (chan  : IsVar roles role)
      -> (chans : Channels roles)
               -> Capable String
recvOn idx chans
  = case read idx chans of
      Open fh
        => either error
                  pure
                  (!(embed (fGetLine fh)))

      _ => panic "Channel in wrong state."

-- [ EOF ]
