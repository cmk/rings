import Control.Monad
import System.Exit (exitFailure)
import System.IO (BufferMode(..), hSetBuffering, stdout, stderr)

import qualified Test.Data.Number.Tropical as NT

tests :: IO [Bool]
tests = sequence [NT.tests]

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering

  results <- tests

  unless (and results) exitFailure
