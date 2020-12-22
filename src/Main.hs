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

import DsMonad
import GHC
import TcExpr
import DsExpr
import TcSimplify
import TcHsSyn
import Inst
import RnExpr
import TcRnDriver
import TcOrigin
import TcRnMonad
import GhcMonad (withSession)
import PrelNames
import GHC.LanguageExtensions.Type
-- import HscMain (hscParseExpr)
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
import ErrUtils (Messages, pprErrMsgBagWithLoc)
import qualified Outputable as O
main :: IO ()
main = do
  -- targetFile <- head <$> getArgs
  str <- runGhc (Just libdir) $ do
    ((_,errmsgs) ,res)    <- example -- targetFile
    dflags <- getSessionDynFlags
    let retDoc = case res of
          Just _ -> ppr res
          Nothing -> O.sep (pprErrMsgBagWithLoc errmsgs)
    return $ showSDoc dflags retDoc
  putStrLn str

example :: GhcMonad m => m (Messages, Maybe CoreExpr)
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
  setContext
    [ -- IIModule $ ms_mod_name modSum
    IIDecl (simpleImportDecl (moduleName pRELUDE))
    ]
  expr <- parseExpr "(==>)"
  (withSession $ \hsc_env -> do
               liftIO $ runTcInteractive hsc_env (withWiredIn (elabRnExpr TM_Inst expr)))

elabRnExpr
  :: TcRnExprMode -> LHsExpr GhcPs -> TcRn CoreExpr
elabRnExpr mode rdr_expr = do
    (rn_expr, _fvs) <- rnLExpr rdr_expr
    failIfErrsM
    uniq <- newUnique
    let fresh_it = itName uniq (getLoc rdr_expr)
        orig     = lexprCtOrigin rn_expr
    (tclvl, lie, (tc_expr, res_ty)) <- pushLevelAndCaptureConstraints $ do
      (_tc_expr, expr_ty) <- tcInferSigma rn_expr
      expr_ty'            <- if inst
        then snd <$> deeplyInstantiate orig expr_ty
        else return expr_ty
      return (_tc_expr, expr_ty')
    (_, _, evbs, residual, _) <- simplifyInfer tclvl
                                            infer_mode
                                            []    {- No sig vars -}
                                            [(fresh_it, res_ty)]
                                            lie
    evbs' <- perhaps_disable_default_warnings $ simplifyInteractive residual
    full_expr <- zonkTopLExpr (mkHsDictLet (EvBinds evbs') (mkHsDictLet evbs tc_expr))
    initDsTc $ dsLExpr full_expr
 where
  (inst, infer_mode, perhaps_disable_default_warnings) = case mode of
    TM_Inst    -> (True, NoRestrictions, id)
    TM_NoInst  -> (False, NoRestrictions, id)
    TM_Default -> (True, EagerDefaulting, unsetWOptM Opt_WarnTypeDefaults)




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
