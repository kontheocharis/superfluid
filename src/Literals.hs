module Literals (minusOneNat, unfoldLit) where

import Common
  ( Arg (..),
    Lit (..),
    PiMode (..),
    Qty (..),
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
minusOneNat t = VLazy (VDef (knownDef KnownSub), S.singleton (Arg Explicit Many t))

unfoldLit :: Lit VTm -> VNorm
unfoldLit = \case
  StringLit [] ->
    let inner =
          VNorm
            ( VCtor
                ( (knownCtor KnownNil, Empty),
                  S.fromList [Arg Implicit Zero (VNorm (VData (knownData KnownChar, Empty)))]
                )
            )
     in VCtor ((knownCtor KnownStr, Empty), S.fromList [Arg Explicit Many inner])
  StringLit (x : xs) ->
    let inner =
          VNorm
            ( VCtor
                ( (knownCtor KnownCons, Empty),
                  S.fromList
                    [ Arg Implicit Zero (VNorm (VData (knownData KnownChar, Empty))),
                      Arg Explicit Many (VLazy (VLit (CharLit x), Empty)),
                      Arg Explicit Many (VLazy (VLit (StringLit xs), Empty))
                    ]
                )
            )
     in VCtor ((knownCtor KnownStr, Empty), S.fromList [Arg Explicit Many inner])
  CharLit x ->
    let finBound = VLazy (VLit (NatLit (2 ^ (32 :: Natural))), Empty)
     in VCtor
          ( (knownCtor KnownChr, Empty),
            S.singleton
              ( Arg
                  Explicit
                  Many
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
    VCtor ((knownCtor KnownZero, Empty), S.empty)
  NatLit n ->
    VCtor ((knownCtor KnownSucc, Empty), S.singleton (Arg Explicit Many (VLazy (VLit (NatLit (n - 1)), Empty))))
  FinLit 0 n ->
    VCtor
      ( (knownCtor KnownFZero, Empty),
        S.singleton (Arg Implicit Zero n)
      )
  FinLit d n ->
    VCtor
      ( (knownCtor KnownFSucc, Empty),
        S.fromList
          [ Arg Implicit Zero n,
            Arg Explicit Many (VLazy (VLit (FinLit (d - 1) (minusOneNat n)), Empty))
          ]
      )
