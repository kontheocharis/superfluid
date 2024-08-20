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

import Common (Arg (..), Clause (..), Lit, Loc, Name, PiMode (..), Pos, Tag, Times (..), arg, mode)
import Data.List (intercalate)
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
  | PLocated Loc PTm
  deriving (Eq, Show)

pApp :: PTm -> [Arg PTm] -> PTm
pApp = foldl (\g x -> PApp x.mode g x.arg)

pLamsToList :: PTm -> ([Arg Name], PTm)
pLamsToList (PLam m n t) = let (ns, b) = pLamsToList t in (Arg m n : ns, b)
pLamsToList t = ([], t)

pAppToList :: PTm -> (PTm, [Arg PTm])
pAppToList (PApp m t u) = let (t', us) = pAppToList t in (t', us ++ [Arg m u])
pAppToList t = (t, [])

pLetToList :: PTm -> ([(Name, PTy, PTm)], PTm)
pLetToList (PLet n ty t1 t2) = let (binds, ret) = pLetToList t2 in ((n, ty, t1) : binds, ret)
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

instance (Monad m) => Pretty m PTm where
  -- \| Show a term value, with parentheses if it is compound.
  singlePretty v | isCompound v = pretty v >>= \p -> return $ "(" ++ p ++ ")"
  singlePretty v = pretty v

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
    px <- pretty x
    pxs <- mapM pretty xs
    return $ px ++ " " ++ intercalate " " pxs
  pretty l@(PLet {}) = do
    let (binds, ret) = pLetToList l
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
  pretty (PCase t cs) = do
    pt <- pretty t
    pcs <-
      mapM
        ( \(Clause p c) -> do
            pp <- pretty p
            pc <- maybe (return "impossible") pretty c
            return $ pp ++ " => " ++ pc
        )
        cs
    return $ "case " ++ pt ++ " " ++ curlies (intercalate ",\n" pcs)
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
