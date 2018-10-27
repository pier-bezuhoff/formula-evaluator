module Main where

import Parser (evalFile)

main :: IO ()
main = evalFile "test/example.txt"
