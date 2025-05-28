-- | @futhark deps@
module Futhark.CLI.Deps (main) where

import Futhark.Compiler
import Futhark.Util.Options
import Language.Futhark.Deps

-- | Run @futhark deps@.
main :: String -> [String] -> IO ()
main = mainWithOptions () [] "program" $ \args () ->
  case args of
    [file] -> do
      Just $ do
        (_, imports, _) <- readProgramOrDie file
        _ <- mapM (putStrLn . deps . fileProg . snd) $ imports
        pure()
    _ -> Nothing
