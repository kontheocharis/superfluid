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
  )
where

import Common (Arg (..), Clause (..), Lit, Loc, Name (..), PiMode (..), Pos, Tag (..), Times (..), arg, mode)
import Data.List (intercalate)
import Data.Set (Set)
import Data.Typeable (Typeable)
import Printing (Pretty (..), curlies)
import Debug.Trace (traceM)

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
  | PApp PiMode PTm PTm
  | PCase PTm [Clause PPat PTm]
  | PU
  | PName Name
  | PLit (Lit PTm)
  | PHole Name
  | PRepr Times PTm
  | PWild
  | PUnit
  | PLocated Loc PTm
  deriving (Eq, Show)

pApp :: PTm -> [Arg PTm] -> PTm
pApp = foldl (\g x -> PApp x.mode g x.arg)

pLamsToList :: PTm -> ([Arg Name], PTm)
pLamsToList (PLam m n t) = let (ns, b) = pLamsToList t in (Arg m n : ns, b)
pLamsToList (PLocated _ t) = pLamsToList t
pLamsToList t = ([], t)

pAppToList :: PTm -> (PTm, [Arg PTm])
pAppToList (PApp m t u) = let (t', us) = pAppToList t in (t', us ++ [Arg m u])
pAppToList (PLocated _ t) = pAppToList t
pAppToList t = (t, [])

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
    let (x, xs) = pAppToList t
    px <- singlePretty x
    pxs <- mapM singlePretty xs
    return $ px ++ " " ++ intercalate " " pxs
  pretty l@(PLet {}) = prettyLets (pLetToList l)
  pretty (PCase t cs) = do
    pt <- pretty t
    pcs <- pretty cs
    return $ "case " ++ pt ++ " " ++ curlies pcs
  pretty PU = return "Type"
  pretty PWild = return "_"
  pretty (PName n) = pretty n
  pretty (PLit l) = pretty l
  pretty (PHole i) = do
    pi' <- pretty i
    return $ "?" ++ pi'
  pretty (PRepr n s) = do
    pn <- pretty n
    ps <- pretty s
    return $ "repr " ++ if n == Finite 1 then ps else pn ++ " " ++ ps
  pretty (PLocated _ t) = pretty t
  pretty PUnit = return "()"

instance (Monad m) => Pretty m PCtor where
  pretty (MkPCtor n ty ts) = do
    pts <- pretty ts
    pn <- pretty n
    pty <- pretty ty
    return $ pts ++ pn ++ " : " ++ pty

instance (Monad m) => Pretty m PData where
  pretty (MkPData n ty cs ts) = do
    pts <- pretty ts
    pn <- pretty n
    pty <- pretty ty
    pcs <- mapM pretty cs
    return $ pts ++ "data " ++ pn ++ " : " ++ pty ++ " " ++ curlies (intercalate ",\n" pcs)

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
  pretty (MkPCaseRep srcSubject srcBranches target ts) = do
    pts <- pretty ts
    psrcSubject <- pretty srcSubject
    psrcBranches <- mapM (\(n, p) -> do pn <- pretty n; pp <- pretty p; return $ pn ++ " => " ++ pp) srcBranches
    pt <- pretty target
    return $ pts ++ "case " ++ psrcSubject ++ " " ++ curlies (intercalate ",\n" psrcBranches) ++ " as " ++ pt

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
