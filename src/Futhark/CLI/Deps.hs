-- | @futhark deps@
module Futhark.CLI.Deps (main, irregular) where

import Futhark.Compiler
import Futhark.Util.Options
import Language.Futhark.Deps

-- | Run @futhark irregular@.
irregular :: String -> [String] -> IO ()
irregular = mainWithOptions () [] "program" $ \args () ->
  case args of
    [file] -> do
      Just $ do
        (_, imports, _) <- readProgramOrDie file
        runInterpreter IrregularConfig $ map (fileProg . snd) imports 
    _ -> Nothing

-- | Run @futhark deps@.
main :: String -> [String] -> IO ()
main = mainWithOptions () [] "program" $ \args () ->
  case args of
    [file] -> do
      Just $ do
        (_, imports, _) <- readProgramOrDie file
        runInterpreter DepsConfig $ map (fileProg . snd) imports 
    _ -> Nothing
