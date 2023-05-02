{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Bench.Lib.TH (mkMethods, mkMain) where

import Bench.Lib.Types (MArgs (..), Result)
import Language.Haskell.TH

mkMethods :: Q Exp -> [Name] -> Q [Dec]
mkMethods code = foldr (combine . go) (return [])
  where
    go :: Name -> Q [Dec]
    go name =
      let test = mkName $ propToTest $ nameBase name
       in [d|$(varP test) = $(code) $(varE name)|]

    combine :: Q [Dec] -> Q [Dec] -> Q [Dec]
    combine qds qds' = do
      ds <- qds
      ds' <- qds'
      return (ds ++ ds')

mkMain :: IO [String] -> IO [String] -> Q [Dec]
mkMain ims ips = do
  ms <- runIO ims
  ps <- runIO ips
  let mps = concatMap (\m -> map (m,) ps) ms
  [d|
    main :: IO ()
    main = do
      args <- getArgs
      let MArgs file trials bench method mutant prop label timeout = parseArgs (head args)
          test = fromJust $ lookup (method, prop) mmap
      benchMany file trials (bench, label, mutant, prop) timeout test

    mmap :: [((String, String), IO Result)]
    mmap = $(listE (map mkPair mps))
    |]
  where
    mkPair :: (String, String) -> Q Exp
    mkPair (m, p) = do
      t <- lookupName m (propToTest p)
      [|((m, p), $(varE t))|]

    lookupName pre suf = do
      let name = pre ++ "." ++ suf
      mv <- lookupValueName name
      case mv of
        -- TODO: might want more flexible behavior here
        Nothing -> error ("could not find:" ++ name)
        Just v -> return v

propToTest :: String -> String
propToTest = ("test_" ++) . tail . dropWhile (/= '_')