{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Presyntax
  ( PTy,
    PPat,
    Tag,
    PDef (..),
    PCtor (..),
    PData (..),
    PCtorRep (..),
    PCaseRep (..),
    PDataRep (..),
    PDefRep (..),
    PItem (..),
    PTm (..),
    PPrim (..),
    PProgram (..),
    tagged,
    pApp,
    pGatherApps,
    pLams,
    toPSpine,
  )
where

import Common
  ( Arg (..),
    Clause (..),
    Lit,
    Loc,
    Name (..),
    PiMode (..),
    Spine,
    Tag (..),
    Tel,
    Times (..),
    arg,
  )
import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Sequence (Seq (..))
import Data.Set (Set)
import Data.Typeable (Typeable)
import Printing (Pretty (..), curlies)

type PTy = PTm

type PPat = PTm

data PDef = MkPDef
  { name :: Name,
    ty :: PTy,
    tm :: PTm,
    tags :: Set Tag
  }
  deriving (Eq, Show)

tagged :: Set Tag -> PItem -> PItem
tagged ts (PData d) = PData $ d {tags = ts}
tagged ts (PDef d) = PDef $ d {tags = ts}
tagged ts (PDataRep d) = PDataRep $ d {tags = ts}
tagged ts (PDefRep d) = PDefRep $ d {tags = ts}
tagged ts (PPrim d) = PPrim $ d {tags = ts}
tagged ts (PLocatedItem loc i) = PLocatedItem loc $ tagged ts i

data PCtor = MkPCtor
  { name :: Name,
    ty :: PTy,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PData = MkPData
  { name :: Name,
    params :: Tel PTy,
    ty :: PTy,
    ctors :: [PCtor],
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PCtorRep = MkPCtorRep
  { src :: PPat,
    target :: PTm,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PCaseRep = MkPCaseRep
  { srcSubject :: PPat,
    srcElim :: Maybe PPat,
    srcBranches :: [(Name, PPat)],
    target :: PTm,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PDataRep = MkPDataRep
  { src :: PPat,
    target :: PTy,
    ctors :: [PCtorRep],
    caseExpr :: PCaseRep,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PDefRep = MkPDefRep
  { src :: PPat,
    target :: PTm,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PPrim = MkPPrim
  { name :: Name,
    ty :: PTy,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PItem
  = PDef PDef
  | PData PData
  | PDataRep PDataRep
  | PDefRep PDefRep
  | PPrim PPrim
  | PLocatedItem Loc PItem
  deriving (Eq, Typeable, Show)

newtype PProgram = PProgram [PItem] deriving (Eq, Show)

data PTm
  = PPi PiMode Name PTy PTy
  | PSigma Name PTy PTy
  | PLam PiMode Name PTm
  | PLet Name PTy PTm PTm
  | PPair PTm PTm
  | PList [PTm] (Maybe PTm)
  | PApp PiMode PTm PTm
  | PCase PTm (Maybe PTm) [Clause PPat PTm]
  | PLambdaCase (Maybe PTm) [Clause PPat PTm]
  | PU
  | PName Name
  | PLit (Lit PTm)
  | PHole Name
  | PRepr Times PTm
  | PParams PTm [PTm]
  | PWild
  | PUnit
  | PLocated Loc PTm
  deriving (Eq, Show)

pApp :: PTm -> [Arg PTm] -> PTm
pApp = foldl (\g x -> PApp x.mode g x.arg)

toPSpine :: PTm -> (PTm, Spine PTm)
toPSpine (PApp m t u) = let (t', sp) = toPSpine t in (t', sp :|> Arg m u)
toPSpine t = (t, Empty)

pLamsToList :: PTm -> ([Arg Name], PTm)
pLamsToList (PLam m n t) = let (ns, b) = pLamsToList t in (Arg m n : ns, b)
pLamsToList (PLocated _ t) = pLamsToList t
pLamsToList t = ([], t)

pLams :: Spine Name -> PTm -> PTm
pLams Empty b = b
pLams (Arg m n :<| xs) b = PLam m n (pLams xs b)

pGatherApps :: PTm -> (PTm, Spine PTm)
pGatherApps (PApp m t u) = let (t', us) = pGatherApps t in (t', us :|> Arg m u)
pGatherApps (PLocated _ t) = pGatherApps t
pGatherApps t = (t, Empty)

pLetToList :: PTm -> ([(Name, PTy, PTm)], PTm)
pLetToList (PLet n ty t1 t2) = let (binds, ret) = pLetToList t2 in ((n, ty, t1) : binds, ret)
pLetToList (PLocated _ t) = pLetToList t
pLetToList t = ([], t)

isCompound :: PTm -> Bool
isCompound (PPi {}) = True
isCompound (PSigma {}) = True
isCompound (PLam {}) = True
isCompound (PLet {}) = True
isCompound (PCase {}) = True
isCompound (PApp {}) = True
isCompound (PRepr {}) = True
isCompound (PLocated _ t) = isCompound t
isCompound (PParams t []) = isCompound t
isCompound (PParams _ _) = True
isCompound _ = False

prettyLets :: (Monad m) => ([(Name, PTy, PTm)], PTm) -> m String
prettyLets (binds, ret) = do
  pbinds <-
    mapM
      ( \(v, ty, t) -> do
          pv <- pretty v
          pty <- pretty ty
          pt <- pretty t
          return $ "let " ++ pv ++ " : " ++ pty ++ " = " ++ pt ++ ";"
      )
      binds
  pret <- pretty ret
  return $ curlies $ intercalate "\n" (pbinds ++ [pret])

instance (Monad m) => Pretty m PTm where
  -- \| Show a term value, with parentheses if it is compound.
  singlePretty v | isCompound v = pretty v >>= \p -> return $ "(" ++ p ++ ")"
  singlePretty v = pretty v

  pretty (PPi Explicit (Name "_") t1 t2) = do
    pt1 <- singlePretty t1
    pt2 <- pretty t2
    return $ pt1 ++ " -> " ++ pt2
  pretty (PPi Explicit v t1 t2) = do
    pv <- pretty v
    pt1 <- pretty t1
    pt2 <- pretty t2
    return $ "(" ++ pv ++ " : " ++ pt1 ++ ") -> " ++ pt2
  pretty (PPi Implicit v t1 t2) = do
    pv <- pretty v
    pt1 <- pretty t1
    pt2 <- pretty t2
    return $ "[" ++ pv ++ " : " ++ pt1 ++ "] -> " ++ pt2
  pretty (PPi Instance v t1 t2) = do
    pv <- pretty v
    pt1 <- pretty t1
    pt2 <- pretty t2
    return $ "[[" ++ pv ++ " : " ++ pt1 ++ "]] -> " ++ pt2
  pretty l@(PLam {}) = do
    let (vs, b) = pLamsToList l
    pvs <- mapM pretty vs
    pb <- pretty b
    return $ "\\" ++ intercalate " " pvs ++ " => " ++ pb
  pretty (PSigma v t1 t2) = do
    pv <- pretty v
    pt1 <- pretty t1
    pt2 <- pretty t2
    return $ "(" ++ pv ++ " : " ++ pt1 ++ ") * " ++ pt2
  pretty (PPair t1 t2) = do
    pt1 <- pretty t1
    pt2 <- pretty t2
    return $ "(" ++ pt1 ++ ", " ++ pt2 ++ ")"
  pretty t@(PApp {}) = do
    let (x, xs) = pGatherApps t
    px <- singlePretty x
    pxs <- mapM singlePretty xs
    return $ px ++ " " ++ intercalate " " (toList pxs)
  pretty l@(PLet {}) = prettyLets (pLetToList l)
  pretty (PCase t r cs) = do
    pt <- singlePretty t
    pcs <- pretty cs
    pr <- case r of
      Nothing -> return ""
      Just r' -> do
        pr' <- singlePretty r'
        return $ " to " ++ pr'
    return $ "case " ++ pt ++ pr ++ " " ++ curlies pcs
  pretty (PLambdaCase r cs) = do
    pcs <- pretty cs
    pr <- case r of
      Nothing -> return ""
      Just r' -> do
        pr' <- singlePretty r'
        return $ " to " ++ pr'
    return $ "\\case " ++ pr ++ curlies pcs
  pretty PU = return "Type"
  pretty PWild = return "_"
  pretty (PName n) = pretty n
  pretty (PLit l) = pretty l
  pretty (PHole i) = do
    pi' <- pretty i
    return $ "?" ++ pi'
  pretty (PRepr n s) = do
    pn <- pretty n
    ps <- singlePretty s
    case n of
      Finite 1 -> return $ "repr " ++ ps
      Finite (-1) -> return $ "unrepr " ++ ps
      _ -> return $ "repr " ++ pn ++ " " ++ ps
  pretty (PLocated _ t) = pretty t
  pretty PUnit = return "()"
  pretty (PParams t []) = pretty t
  pretty (PParams t ps) = do
    pt <- singlePretty t
    pps <- mapM pretty ps
    return $ pt ++ "@[" ++ intercalate ", " pps ++ "]"
  pretty (PList ts rest) = do
    pts <- mapM pretty ts
    rest' <- case rest of
      Nothing -> return ""
      Just r -> do
        pr <- pretty r
        return $ ", .." ++ pr
    return $ "[" ++ intercalate ", " pts ++ rest' ++ "]"

instance (Monad m) => Pretty m PCtor where
  pretty (MkPCtor n ty ts) = do
    pts <- pretty ts
    pn <- pretty n
    pty <- pretty ty
    return $ pts ++ pn ++ " : " ++ pty

instance (Monad m) => Pretty m PData where
  pretty (MkPData n te ty cs ts) = do
    pts <- pretty ts
    pn <- pretty n
    pte <- if null te then return "" else (" " ++) <$> pretty te
    pty <- pretty ty
    pcs <- mapM pretty cs
    return $ pts ++ "data " ++ pn ++ pte ++ " : " ++ pty ++ " " ++ curlies (intercalate ",\n" pcs)

instance (Monad m) => Pretty m (Tel PTy) where
  pretty ps = intercalate " " <$> mapM pretty (toList ps)

instance (Monad m) => Pretty m PDef where
  pretty (MkPDef n ty tm ts) = do
    pts <- pretty ts
    pn <- pretty n
    pty <- pretty ty
    ptm <- prettyLets (pLetToList tm)
    return $ pts ++ "def " ++ pn ++ " : " ++ pty ++ " " ++ ptm

instance (Monad m) => Pretty m PPrim where
  pretty (MkPPrim n ty ts) = do
    pts <- pretty ts
    pn <- pretty n
    pty <- pretty ty
    return $ pts ++ "prim " ++ pn ++ " : " ++ pty

instance (Monad m) => Pretty m PCtorRep where
  pretty (MkPCtorRep src target ts) = do
    pts <- pretty ts
    psrc <- pretty src
    pt <- pretty target
    return $ pts ++ psrc ++ " as " ++ pt

instance (Monad m) => Pretty m PCaseRep where
  pretty (MkPCaseRep srcSubject srcElim srcBranches target ts) = do
    pts <- pretty ts
    psrcSubject <- pretty srcSubject
    psrcBranches <- mapM (\(n, p) -> do pn <- pretty n; pp <- pretty p; return $ pn ++ " => " ++ pp) srcBranches
    pt <- pretty target
    pe <- case srcElim of
      Nothing -> return ""
      Just e -> do
        pe' <- pretty e
        return $ " to " ++ pe'
    return $ pts ++ "case " ++ psrcSubject ++ pe ++ " " ++ curlies (intercalate ",\n" psrcBranches) ++ " as " ++ pt

instance (Monad m) => Pretty m PDataRep where
  pretty (MkPDataRep src target cs caseExpr ts) = do
    pts <- pretty ts
    psrc <- pretty src
    pt <- pretty target
    pcs <- mapM pretty cs
    pcaseExpr <- pretty caseExpr
    return $ pts ++ "data " ++ psrc ++ " as " ++ pt ++ " " ++ curlies (intercalate "\n\n" (pcs ++ [pcaseExpr]))

instance (Monad m) => Pretty m PDefRep where
  pretty (MkPDefRep src target ts) = do
    pts <- pretty ts
    psrc <- pretty src
    pt <- pretty target
    return $ pts ++ "def " ++ psrc ++ " as " ++ pt

instance (Monad m) => Pretty m PItem where
  pretty (PDef d) = pretty d
  pretty (PData d) = pretty d
  pretty (PDataRep d) = pretty d
  pretty (PDefRep d) = pretty d
  pretty (PPrim d) = pretty d
  pretty (PLocatedItem _ i) = pretty i

instance (Monad m) => Pretty m PProgram where
  pretty (PProgram is) = do
    pis <- mapM pretty is
    return $ intercalate "\n\n" pis
