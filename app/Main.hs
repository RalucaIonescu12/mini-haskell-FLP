
module Main where

import System.IO
import System.Console.Isocline

import Exp
import Parsing
import Sugar
import Eval
import Printing
import REPLCommand
import Text.ParserCombinators.Parsec(parse) 

main
  = do
    putStr "miniHaskell> "
    hFlush stdout
    s <- getLine
    case parseFirst replCommand s of
          Nothing -> putStrLn "Cannot parse the command" >> main
          Just Quit -> return ()
          Just (Load _) -> putStrLn "Not implemented" >> main
          Just (Eval es) ->
            case parseFirst exprParser es of
              Nothing -> putStrLn "Error: cannot parse the expression" >> main 
              Just e ->
                let simpleE = desugarExp e
                    simpleE' = normalize simpleE
                    e' = sugarExp simpleE'
                 in putStrLn (showExp e') >> main
                        

