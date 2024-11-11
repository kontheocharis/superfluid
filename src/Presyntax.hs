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
    MaybeQty (..),
    tagged,
    pApp,
    pGatherApps,
    pGatherPis,
    pLams,
    toPSpine,
  )
where

import Common
  ( Arg (..),
    Clause (..),
    Lit (..),
    Loc,
    Name (..),
    Param (..),
    PiMode (..),
    Qty (..),
    Spine,
    Tag (..),
    Tel,
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

newtype MaybeQty = MaybeQty { un :: Maybe Qty }
  deriving (Eq)

instance Show MaybeQty where
  show (MaybeQty Nothing) = ""
  show (MaybeQty (Just q)) = show q

data PDef = MkPDef
  { name :: Name,
    qty :: MaybeQty,
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
    qty :: MaybeQty,
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
    qty :: MaybeQty,
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
  = PPi PiMode (MaybeQty) Name PTy PTy
  | PSigma (MaybeQty) Name PTy (MaybeQty) PTy
  | PLam PiMode PPat PTm
  | PLet (MaybeQty) PPat PTy PTm PTm
  | PPair PTm PTm
  | PList [PTm] (Maybe PTm)
  | PApp PiMode PTm PTm
  | PCase PTm (Maybe PTm) [Clause PPat PTm]
  | PIf PTm PTm PTm
  | PLambdaCase (Maybe PTm) [Clause PPat PTm]
  | PU
  | PName Name
  | PLit (Lit (Maybe PTm))
  | PHole Name
  | PRepr PTm
  | PUnrepr PTm
  | PParams PTm [PTm]
  | PWild
  | PUnit
  | PLocated Loc PTm
  deriving (Eq, Show)

pApp :: PTm -> [Arg PTm] -> PTm
pApp = foldl (\g x -> PApp x.mode g x.arg)

-- In all the above we don't care about the quantity

toPSpine :: PTm -> (PTm, Spine PTm)
toPSpine (PApp m t u) = let (t', sp) = toPSpine t in (t', sp :|> Arg m Many u)
toPSpine t = (t, Empty)

pLamsToList :: PTm -> ([Arg PPat], PTm)
pLamsToList (PLam m n t) = let (ns, b) = pLamsToList t in (Arg m Many n : ns, b)
pLamsToList (PLocated _ t) = pLamsToList t
pLamsToList t = ([], t)

pLams :: Tel a -> PTm -> PTm
pLams Empty b = b
pLams (Param m _ n _ :<| xs) b = PLam m (PName n) (pLams xs b)

pGatherApps :: PTm -> (PTm, Spine PTm)
pGatherApps (PApp m t u) = let (t', us) = pGatherApps t in (t', us :|> Arg m Many u)
pGatherApps (PLocated _ t) = pGatherApps t
pGatherApps t = (t, Empty)

pGatherPis :: PTm -> (Tel PTy, PTm)
pGatherPis (PPi m _ n a b) = let (ns, b') = pGatherPis b in (Param m Zero n a :<| ns, b')
pGatherPis (PLocated _ t) = pGatherPis t
pGatherPis t = (Empty, t)

pLetToList :: PTm -> ([(MaybeQty, PPat, PTy, PTm)], PTm)
pLetToList (PLet q n ty t1 t2) = let (binds, ret) = pLetToList t2 in ((q, n, ty, t1) : binds, ret)
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
isCompound (PUnrepr {}) = True
isCompound (PLocated _ t) = isCompound t
isCompound (PParams t _) = isCompound t
-- isCompound (PParams _ _) = True
isCompound _ = False

prettyLets :: (Monad m) => ([(MaybeQty, PPat, PTy, PTm)], PTm) -> m String
prettyLets (binds, ret) = do
  pbinds <-
    mapM
      ( \(MaybeQty q, v, ty, t) -> do
          pv <- singlePretty v
          pty <- pretty ty
          pt <- pretty t
          return $ "let " ++ maybe "" show q ++ pv ++ " : " ++ pty ++ " = " ++ pt ++ ";"
      )
      binds
  pret <- pretty ret
  return $ curlies $ intercalate "\n" (pbinds ++ [pret])

prettyMaybeLit :: (Monad m) => Lit (Maybe PTm) -> m String
prettyMaybeLit (FinLit n Nothing) = return $ show n
prettyMaybeLit (FinLit n (Just t)) = pretty (FinLit n t :: Lit PTm)
prettyMaybeLit (StringLit s) = pretty (StringLit s :: Lit PTm)
prettyMaybeLit (CharLit c) = pretty (CharLit c :: Lit PTm)
prettyMaybeLit (NatLit n) = return $ show n

instance (Monad m) => Pretty m PTm where
  -- \| Show a term value, with parentheses if it is compound.
  singlePretty v | isCompound v = pretty v >>= \p -> return $ "(" ++ p ++ ")"
  singlePretty v = pretty v

  pretty (PPi Explicit (MaybeQty Nothing) (Name "_") t1 t2) = do
    pt1 <- singlePretty t1
    pt2 <- pretty t2
    return $ pt1 ++ " -> " ++ pt2
  pretty (PPi Explicit q v t1 t2) = do
    pv <- singlePretty v
    pt1 <- pretty t1
    pt2 <- pretty t2
    return $ "(" ++ show q ++ pv ++ " : " ++ pt1 ++ ") -> " ++ pt2
  pretty (PPi Implicit q v t1 t2) = do
    pv <- pretty v
    pt1 <- pretty t1
    pt2 <- pretty t2
    return $ "[" ++ show q ++ pv ++ " : " ++ pt1 ++ "] -> " ++ pt2
  pretty (PPi Instance q v t1 t2) = do
    pv <- pretty v
    pt1 <- pretty t1
    pt2 <- pretty t2
    return $ "[[" ++ show q ++ pv ++ " : " ++ pt1 ++ "]] -> " ++ pt2
  pretty l@(PLam {}) = do
    let (vs, b) = pLamsToList l
    pvs <- mapM singlePretty vs
    pb <- pretty b
    return $ "\\" ++ intercalate " " pvs ++ " => " ++ pb
  pretty (PSigma q1 v t1 q2 t2) = do
    pv <- singlePretty v
    pt1 <- pretty t1
    pt2 <- pretty t2
    return $ "(" ++ show q1 ++ pv ++ " : " ++ pt1 ++ ") * " ++ show q2 ++ pt2
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
  pretty (PLit l) = prettyMaybeLit l
  pretty (PHole i) = do
    pi' <- pretty i
    return $ "?" ++ pi'
  pretty (PUnrepr s) = do
    ps <- singlePretty s
    return $ "unrepr " ++ ps
  pretty (PRepr s) = do
    ps <- singlePretty s
    return $ "repr " ++ ps
  pretty (PLocated _ t) = pretty t
  pretty PUnit = return "()"
  pretty (PParams t []) = pretty t
  pretty (PParams t _) = pretty t
  -- pt <- singlePretty t
  -- pps <- mapM pretty ps
  -- return $ pt ++ "@[" ++ intercalate ", " pps ++ "]"
  pretty (PList ts rest) = do
    pts <- mapM pretty ts
    rest' <- case rest of
      Nothing -> return ""
      Just r -> do
        pr <- pretty r
        return $ ", .." ++ pr
    return $ "[" ++ intercalate ", " pts ++ rest' ++ "]"
  pretty (PIf c t e) = do
    pc <- singlePretty c
    pt <- singlePretty t
    pe <- singlePretty e
    return $ "if " ++ pc ++ " " ++ curlies pt ++ " else " ++ curlies pe

instance (Monad m) => Pretty m PCtor where
  pretty (MkPCtor n q ty ts) = do
    pts <- pretty ts
    pn <- pretty n
    pty <- pretty ty
    return $ show q ++ pts ++ pn ++ " : " ++ pty

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
  pretty (MkPDef n q ty tm ts) = do
    pts <- pretty ts
    pn <- pretty n
    pty <- pretty ty
    ptm <- prettyLets (pLetToList tm)
    return $ pts ++ "def " ++ show q ++ pn ++ " : " ++ pty ++ " " ++ ptm

instance (Monad m) => Pretty m PPrim where
  pretty (MkPPrim n q ty ts) = do
    pts <- pretty ts
    pn <- pretty n
    pty <- pretty ty
    return $ pts ++ "prim " ++ show q ++ pn ++ " : " ++ pty

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
