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
  ( VHead (..),
    VNeu (..),
    VTm (..),
    pattern VGl,
    pattern VGlob,
    pattern VGlobE,
  )

minusOneNat :: VTm -> VTm
minusOneNat (VLit l@(NatLit _)) = minusOneNat (unfoldLit l)
minusOneNat (VNeu (VApp (VGlobal (CtorGlob g) _) sp)) | g == knownCtor KnownSucc = case sp of
  (Arg Explicit x :<| Empty) -> x
  _ -> error "minusOneNat: invalid spine"
minusOneNat _ = error "minusOneNat: invalid term"

unfoldLit :: Lit VTm -> VTm
unfoldLit = \case
  StringLit [] ->
    let inner =
          VGlobE
            (CtorGlob (knownCtor KnownNil))
            ( S.fromList
                [Arg Implicit (VGl (DataGlob (knownData KnownChar)))]
            )
     in VGlobE (CtorGlob (knownCtor KnownStr)) (S.fromList [Arg Explicit inner])
  StringLit (x : xs) ->
    let inner =
          VGlobE
            (CtorGlob (knownCtor KnownCons))
            ( S.fromList
                [ Arg Implicit (VGl (DataGlob (knownData KnownChar))),
                  Arg Explicit (VLit (CharLit x)),
                  Arg Explicit (VLit (StringLit xs))
                ]
            )
     in VGlobE (CtorGlob (knownCtor KnownStr)) (S.fromList [Arg Explicit inner])
  CharLit x ->
    let finBound = VLit (NatLit (2 ^ (32 :: Natural)))
     in VGlobE
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
    VGlobE (CtorGlob (knownCtor KnownSucc)) (S.singleton (Arg Explicit (VLit (NatLit (n - 1)))))
  FinLit 0 n -> do
    VGlobE (CtorGlob (knownCtor KnownFZero)) (S.singleton (Arg Implicit n))
  FinLit d n ->
    VGlobE
      (CtorGlob (knownCtor KnownFSucc))
      ( S.fromList
          [ Arg Implicit n,
            Arg Explicit (VLit (FinLit (d - 1) (minusOneNat n)))
          ]
      )
