module Literals (minusOneNat, unfoldLit) where

import Common
  ( Arg (..),
    Glob (..),
    Lit (..),
    PiMode (..),
  )
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Globals (KnownGlobal (..), knownCtor, knownData)
import Numeric.Natural (Natural)
import Value
  ( VTm (..),
    pattern VGl,
  )

minusOneNat :: VTm -> VTm
minusOneNat (VLit l@(NatLit n)) = minusOneNat (unfoldLit l)
minusOneNat (VGlobal (CtorGlob g) sp) | g == knownCtor KnownSucc = case sp of
  (Arg Explicit x :<| Empty) -> x
  _ -> error "minusOneNat: invalid spine"
minusOneNat _ = error "minusOneNat: invalid term"

unfoldLit :: Lit VTm -> VTm
unfoldLit = \case
  StringLit [] ->
    let inner =
          VGlobal
            (CtorGlob (knownCtor KnownNil))
            ( S.fromList
                [Arg Implicit (VGl (DataGlob (knownData KnownChar)))]
            )
     in VGlobal (CtorGlob (knownCtor KnownStr)) (S.fromList [Arg Explicit inner])
  StringLit (x : xs) ->
    let inner =
          VGlobal
            (CtorGlob (knownCtor KnownCons))
            ( S.fromList
                [ Arg Implicit (VGl (DataGlob (knownData KnownChar))),
                  Arg Explicit (VLit (CharLit x)),
                  Arg Explicit (VLit (StringLit xs))
                ]
            )
     in VGlobal (CtorGlob (knownCtor KnownStr)) (S.fromList [Arg Explicit inner])
  CharLit x ->
    let finBound = VLit (NatLit (2 ^ (32 :: Natural)))
     in VGlobal
          (CtorGlob (knownCtor KnownChr))
          ( S.singleton
              ( Arg
                  Explicit
                  ( VLit
                      ( FinLit
                          (fromIntegral (fromEnum x))
                          finBound
                      )
                  )
              )
          )
  NatLit 0 ->
    VGl (CtorGlob (knownCtor KnownZero))
  NatLit n ->
    VGlobal (CtorGlob (knownCtor KnownSucc)) (S.singleton (Arg Explicit (VLit (NatLit (n - 1)))))
  FinLit 0 n -> do
    VGlobal (CtorGlob (knownCtor KnownFZero)) (S.singleton (Arg Implicit n))
  FinLit d n ->
    VGlobal
      (CtorGlob (knownCtor KnownFSucc))
      ( S.fromList
          [ Arg Implicit n,
            Arg Explicit (VLit (FinLit (d - 1) (minusOneNat n)))
          ]
      )
