module Main where

import Parser

main :: IO ()
main = evalFile "test/example.txt"
