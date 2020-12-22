{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PartialTypeSignatures      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE TypeFamilies               #-}

module Main where

import GHC
import PrelNames
import GHC.LanguageExtensions.Type
import TcRnTypes
import Data.Maybe (maybeToList)
import TcEvidence
import Data.Semigroup
import System.Environment (getArgs)
-- import TcPluginM
import IfaceEnv
import GHC.Hs
import Bag
import TcBinds
import GhcPlugins hiding ((<>))
import Control.Monad (void)
import GHC.Paths (libdir)


main :: IO ()
main = do
  -- targetFile <- head <$> getArgs
  str <- runGhc (Just libdir) $ do
    res    <- example -- targetFile
    dflags <- getSessionDynFlags
    return $ showSDoc dflags $ ppr res
  putStrLn str

example :: (GhcMonad m) => -- String ->
  m Type
example -- targetFile
  = do
  dflags <- getSessionDynFlags
  let dflags' = foldl xopt_set dflags [FlexibleInstances, ExplicitForAll, Cpp, ImplicitPrelude, MagicHash]
  void
    $          setSessionDynFlags
    $          dflags' { hscTarget = HscInterpreted
                       , ghcLink   = LinkInMemory
                       , ghcMode   = CompManager
                       }
    `gopt_set` Opt_DeferTypedHoles
  -- target <- guessTarget targetFile Nothing
  -- setTargets [target]
  -- void $ load LoadAllTargets
  -- let modBName = mkModuleName "QQQ"
  -- modSum <- getModSummary modBName
  setContext
    [ -- IIModule $ ms_mod_name modSum
    IIDecl (simpleImportDecl (moduleName pRELUDE))
    ]
  -- (t, _) <- GHC.typeKind False "forall a. Thing a"
  -- let (_, m) = splitForAllTys t
  GHC.exprType TM_Inst "(==)"
  -- let (clsTycon, tys) = tcSplitTyConApp m
  -- let Just cls = tyConClass_maybe clsTycon
  -- let computation = matchGlobalInst dflags' False cls tys
  -- withSession $ \hsc_env -> liftIO $ do
  --   (_, mb)<- runTcInteractive hsc_env computation
  --   pure mb





data WiredIn = WiredIn {
    wiredInName :: Name
  , wiredInFixity :: Maybe (Int, FixityDirection)
  , wiredInType :: HsType GhcRn
  }

withWiredIn :: TcM a -> TcM a
withWiredIn m = do
  undef <- lookupUndef
  wiredIns <- mkWiredIns
  snd <$> tcValBinds NotTopLevel (binds undef wiredIns) (sigs wiredIns) m
  
 where
  lookupUndef = do
    lookupOrig (Module (stringToUnitId "GHC.Err") (mkModuleName "GHC.Err")) (mkVarOcc "undefined")
    -- tcLookupGlobal undefName

  binds :: Name -> [WiredIn] -> [(RecFlag, LHsBinds GhcRn)]
  binds undef wiredIns = map (\w -> 
      let ext = unitNameSet undef in -- $ varName $ tyThingId undef in
      let co_fn = idHsWrapper in
      let matches = 
            let ctxt = LambdaExpr in
            let grhss = GRHSs NoExtField [L locSpan (GRHS NoExtField [] (L locSpan (HsVar NoExtField (L locSpan undef))))] (L locSpan emptyLocalBinds) in
            MG NoExtField (L locSpan [L locSpan (Match NoExtField ctxt [] grhss)]) Generated 
      in
      let b = FunBind ext (L locSpan $ wiredInName w) matches co_fn [] in
      (NonRecursive, unitBag (L locSpan b))
    ) wiredIns

  sigs wiredIns = concatMap (\w ->
      let inf = maybeToList $ fmap (\(fPrec, fDir) -> L locSpan $ FixSig NoExtField $ FixitySig NoExtField [L locSpan (wiredInName w)] $ Fixity NoSourceText fPrec fDir) $ wiredInFixity w in
      let t = 
            let ext = [] in -- TODO: What goes here? XXX
            [L locSpan $ TypeSig NoExtField [L locSpan (wiredInName w)] $ HsWC ext $ HsIB ext $ L locSpan $ wiredInType w]
      in
      inf <> t
    ) wiredIns

  locSpan = UnhelpfulSpan "Language.Haskell.Liquid.GHC.Interface: WiredIn"

  mkWiredIns = sequence [impl, dimpl]

  toName s = do
    u <- getUniqueM
    return $ mkInternalName u (mkVarOcc s) locSpan

  boolTy = do
    boolName <- lookupOrig (Module (stringToUnitId "Data.Bool") (mkModuleName "Data.Bool")) (mkVarOcc "Bool")
    return $ L locSpan $ HsTyVar NoExtField NotPromoted $ L locSpan boolName
 
  -- infixr 1 ==> :: Bool -> Bool -> Bool
  impl = do
    n <- toName "==>"
    b <- boolTy
    let ty = HsFunTy NoExtField b (L locSpan $ HsFunTy NoExtField b b)
    return $ WiredIn n (Just (1, InfixR)) ty

  -- infixr 1 <=> :: Bool -> Bool -> Bool
  dimpl = do
    n <- toName "<=>"
    b <- boolTy
    let ty = HsFunTy NoExtField b (L locSpan $ HsFunTy NoExtField b b)
    return $ WiredIn n (Just (1, InfixR)) ty
