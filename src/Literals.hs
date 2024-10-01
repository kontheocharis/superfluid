module Literals (minusOneNat, unfoldLit) where

import Common
  ( Arg (..),
    Lit (..),
    PiMode (..),
  )
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Globals (KnownGlobal (..), knownCtor, knownData, knownDef)
import Numeric.Natural (Natural)
import Syntax
  ( VLazyHead (..),
    VNorm (..),
    VTm (..),
  )

minusOneNat :: VTm -> VTm
minusOneNat t = VLazy (VDef (knownDef KnownSub), S.singleton (Arg Explicit t))

unfoldLit :: Lit VTm -> VNorm
unfoldLit = \case
  StringLit [] ->
    let inner =
          VNorm
            ( VCtor
                ( (knownCtor KnownNil, []),
                  S.fromList [Arg Implicit (VNorm (VData (knownData KnownChar, Empty)))]
                )
            )
     in VCtor ((knownCtor KnownStr, []), S.fromList [Arg Explicit inner])
  StringLit (x : xs) ->
    let inner =
          VNorm
            ( VCtor
                ( (knownCtor KnownCons, []),
                  S.fromList
                    [ Arg Implicit (VNorm (VData (knownData KnownChar, Empty))),
                      Arg Explicit (VLazy (VLit (CharLit x), Empty)),
                      Arg Explicit (VLazy (VLit (StringLit xs), Empty))
                    ]
                )
            )
     in VCtor ((knownCtor KnownStr, []), S.fromList [Arg Explicit inner])
  CharLit x ->
    let finBound = VLazy (VLit (NatLit (2 ^ (32 :: Natural))), Empty)
     in VCtor
          ( (knownCtor KnownChr, []),
            S.singleton
              ( Arg
                  Explicit
                  ( VLazy
                      ( VLit
                          ( FinLit
                              (fromIntegral (fromEnum x))
                              finBound
                          ),
                        Empty
                      )
                  )
              )
          )
  NatLit 0 ->
    VCtor ((knownCtor KnownZero, []), S.empty)
  NatLit n ->
    VCtor ((knownCtor KnownSucc, []), S.singleton (Arg Explicit (VLazy (VLit (NatLit (n - 1)), Empty))))
  FinLit 0 n ->
    VCtor
        ( (knownCtor KnownFZero, []),
          S.singleton (Arg Implicit (VNorm (VData (knownData KnownNat, S.singleton (Arg Explicit n)))))
        )
  FinLit d n ->
    VCtor
        ( (knownCtor KnownFSucc, []),
          S.fromList
            [ Arg Implicit (VNorm (VData (knownData KnownNat, S.singleton (Arg Explicit n)))),
              Arg Explicit (VLazy (VLit (FinLit (d - 1) (minusOneNat n)), Empty))
            ]
        )
