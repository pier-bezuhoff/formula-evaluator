module Main where
import Interactive (evalFile)

main :: IO ()
main = evalFile "test/example.txt"
