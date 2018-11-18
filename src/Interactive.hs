{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
module Interactive where
import qualified Data.Map as M
import Data.List
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Parseable
import Parser

type ErrS = Err String

data Err e x = Err e | X x deriving (Eq, Functor)
instance (Show e, Show x) => Show (Err e x) where
  show (Err e) = "Error: " ++ show e
  show (X x) = show x
instance Applicative (Err e) where
  pure = return
  (<*>) = ap
instance Monad (Err e) where
  return = X
  ma >>= amb = join' $ amb <$> ma where
    join' = \case
      Err s -> Err s
      X (Err s) -> Err s
      X (X x) -> X x
instance MonadError e (Err e) where
  throwError = Err
  Err e `catchError` h = h e
  X x `catchError` _ = X x


processLine :: Scope AParseable -> String -> StateT (Scope AParseable) IO ()
processLine scope line = go where
  ws = words line
  s = intercalate " " $ tail $ ws
  doCarefully s expr answer action
    | Err err <- expr = liftIO $ reportParseError s err
    | X expr' <- expr
    , Err err <- answer = liftIO $ reportEvalError s expr' err
    | otherwise = action
  infer :: Scope AParseable -> Either FreeVar ATypedExpr -> MaybeAPT
  infer scope = \case
    Left (FreeVar name) -> case M.lookup name scope of
      Nothing -> Wildcard
      Just ap -> APT $ parseableType ap
    Right (ATE (TypedExpr _ t)) -> APT t
  evalOrFree :: MonadError Error me => Scope AParseable -> Either FreeVar ATypedExpr -> me AParseable
  evalOrFree scope = \case
    Left (FreeVar name) -> case M.lookup name scope of
      Nothing -> throwError $ "unknown free var " ++ name
      Just ap -> return $ ap
    Right ate -> evalScope' scope ate
  go = case ws of
    ":tokenize" : _ -> liftIO $ print $ tokenize @ErrS s
    ":toRPN" : _ -> liftIO $ print $ toRPN @ErrS =<< tokenize s
    ":parse" : _ -> liftIO $ print $ parse @ErrS s
    ":p" : _ -> liftIO $ print $ parse @ErrS s
    ":parseRPN" : _ -> liftIO $ print $ fromRPN @ErrS =<< tokenize s
    ":evalRPN" : _ -> liftIO $ print $ evalOrFree @ErrS scope =<< fromRPN =<< tokenize s
    ":parseS" : _ -> liftIO $ print $ fromS @ErrS =<< tokenize s
    ":evalS" : _ -> liftIO $ print $ evalOrFree @ErrS scope =<< fromS =<< tokenize s
    ":type" : _ -> liftIO $ print $ infer scope <$> parse @ErrS s
    ":t" : _ -> liftIO $ print $ infer scope <$> parse @ErrS s
    ":help" : _ -> liftIO $ putStrLn help
    ":h" : _ -> liftIO $ putStrLn help
    ":?" : _ -> liftIO $ putStrLn help
    _ : "=" : _ -> let
      s = intercalate " " $ drop 2 $ ws
      expr = parse @ErrS s
      answer = evalOrFree @ErrS scope =<< expr
      X result = answer
      in doCarefully s expr answer $ put $ M.insert (head ws) result scope
    _ ->  let
      expr = parse @ErrS line
      answer = evalOrFree @ErrS scope =<< expr
      X result = answer
      in doCarefully line expr answer $ liftIO $ putStrLn $ line ++ " = " ++ show result

reportParseError :: [Char] -> [Char] -> IO ()
reportParseError s err = putStrLn $ "Error while parsing expression at \"" ++ s ++ "\"\n\t" ++ err
reportEvalError :: Show a => [Char] -> a -> [Char] -> IO ()
reportEvalError s expr err = putStrLn $ "Error while evaluating expression \"" ++ s ++ "\"\n(parsed as " ++ show expr ++ ")\n\t" ++ err
help :: [Char]
help = "Available commands:\n" ++ (intercalate "\n" $ map ('\t':) $ [
  "<expresion> -- evaluate expression",
  "<statement> -- assign expresion in statement to variable",
  ":tokenize <expression>",
  ":toRPN <expression> -- toRPN <=< tokenize",
  ":parse <expression>",
  ":parseRPN <expression>",
  ":evalRPN <expression> -- evalScope scope <=< parseRPN",
  ":type <expression> -- show its type",
  ":help or :?"
  ]) ++ "\n"

repl :: IO ()
repl = void $ runStateT processRepl fullDefaultScope where
  processRepl :: StateT (Scope AParseable) IO ()
  processRepl = do
    line <- liftIO $ getLine
    unless (line `elem` ["", "quit", "exit", ":q", ":Q", ":quit", ":exit"] || all (== ' ') line) $ do
      scope <- get
      processLine scope line
      processRepl

evalFile :: FilePath -> IO ()
evalFile filename = void $ runStateT process fullDefaultScope where
  process :: StateT (Scope AParseable) IO ()
  process = do
    content <- liftIO $ readFile filename
    forM_ (lines content) $ \line -> do
      m <- get
      processLine m line
    m <- get
    liftIO $ forM_ (M.toList m) $ \(k, v) ->
      putStrLn $ k ++ " = " ++ show v
