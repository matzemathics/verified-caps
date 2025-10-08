{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use tuple-section" #-}
module Sloc where

import Data.Functor
import Data.List (intercalate, intersperse, isPrefixOf)
import GHC.TypeLits (Mod)
import Text.Parsec (Parsec, alphaNum, char, count, many1, noneOf, notFollowedBy, parse, try, (<|>))
import Text.Parsec.Char (string)
import Text.Parsec.Prim (many)

stripComments :: String -> String
stripComments = unlines . filter (not . isPrefixOf "//" . dropWhile (' ' ==)) . lines

stripEmpty :: String -> String
stripEmpty = unlines . filter (/= "") . lines

data Token
  = Proof
  | Spec
  | Tracked
  | Ghost
  | Assert
  | Clause
  | Unknown
  deriving (Show, Eq)

data TokenTree
  = Region Char [TokenTree]
  | Token Token
  | NewLine
  | KeepGhost
  deriving (Show, Eq)

reserved :: Parsec String st Token
reserved =
  try (string "proof" $> Proof)
    <|> try (string "proof!" $> Proof)
    <|> try (string "spec" $> Spec)
    <|> try (string "ghost" $> Ghost)
    <|> try (string "tracked" $> Tracked)
    <|> try (string "assert" $> Assert)
    <|> try (string "decreases" $> Clause)
    <|> try (string "requires" $> Clause)
    <|> try (string "ensures" $> Clause)
    <|> try (string "returns" $> Clause)
    <|> try (string "invariant" $> Clause)
    <|> try (string "tokenized_state_machine!" $> Proof)

tokenTree :: Parsec String st TokenTree
tokenTree =
  (char '(' *> (Region '(' <$> many tokenTree) <* many (char ' ') <* char ')')
    <|> (char '{' *> (Region '{' <$> many tokenTree) <* many (char ' ') <* char '}')
    <|> try (many1 (char ' ') *> tokenTree)
    <|> try (Token <$> reserved <* notFollowedBy alphaNum)
    <|> try (string "#[cfg(verus_keep_ghost)]\n" $> KeepGhost)
    <|> try (many1 (noneOf [' ', '{', '}', '(', ')', '\n']) $> Token Unknown)
    <|> (char '\n' $> NewLine)

strip :: TokenTree -> [TokenTree] -> [TokenTree]
strip x (t : tt) | x == t = strip x tt
strip x (Region c r : tt) = Region c (strip x r) : strip x tt
strip x (t : tt) = t : strip x tt
strip _ [] = []

data Counts = Counts {spec :: Int, proof :: Int, exec :: Int} deriving (Show)

instance Semigroup Counts where
  a <> b =
    Counts
      { spec = spec a + spec b,
        proof = proof a + proof b,
        exec = exec a + exec b
      }

instance Monoid Counts where
  mempty = Counts 0 0 0

data Mode = MNormal | MProof | MSpec deriving (Show)

data Switch = Switch Int Mode deriving (Show)

consumeMany :: State -> [TokenTree] -> (Counts, State)
consumeMany m = (`c` m) . foldMap consumeOne

fixBase :: State -> (Counts, State)
fixBase s = (mempty, S [] (mode s) False)

switchTo :: Mode -> ResetLocation -> Counter
switchTo m r = C $ \s -> (mempty, s {modeStack = addToStack m r $ modeStack s})

addToStack :: Mode -> ResetLocation -> [(Mode, ResetLocation)] -> [(Mode, ResetLocation)]
addToStack m AtCurly ((_, AtCurly) : s) = (m, AtCurly) : s
addToStack m r s = (m, r) : s

countMode :: (Mode -> Counts) -> Counter
countMode f = C $ \m -> (f (mode m), m)

consumeOne :: TokenTree -> Counter
consumeOne NewLine = countMode uppies <> C resetTo
consumeOne (Token Proof) = switchTo MProof AfterCurly
consumeOne (Token Tracked) = switchTo MProof AtNewline
consumeOne (Token Assert) = switchTo MProof AtNewline
consumeOne (Token Spec) = switchTo MSpec AfterCurly
consumeOne (Token Ghost) = switchTo MSpec AtNewline
consumeOne (Token Clause) = switchTo MSpec AtCurly
consumeOne (Region '{' tt) =
  C encounteringCurly
    <> ignoreState (C fixBase <> C (`consumeMany` tt))
consumeOne (Region _ tt) = C (`consumeMany` tt)
consumeOne (Token _) = mempty
consumeOne KeepGhost =
  switchTo MSpec AtNewline
    <> countMode (const $ Counts 0 1 0)

ignoreState :: Counter -> Counter
ignoreState f = C $ \s -> (fst $ c f s, s)

uppies MNormal = Counts 0 0 1
uppies MProof = Counts 0 1 0
uppies MSpec = Counts 1 0 0

mode :: State -> Mode
mode (S ((m, _) : _) _ _) = m
mode (S [] b _) = b

encounteringCurly :: State -> (Counts, State)
encounteringCurly (S ((_, AtCurly) : r) m _) =
  (mempty, S r m True)
encounteringCurly s = (mempty, s {encounteredCurly = True})

resetTo :: State -> (Counts, State)
resetTo s@(S ((_, AtCurly) : _) _ _) = (mempty, s)
resetTo s@(S ((_, AfterCurly) : _) _ False) = (mempty, s)
resetTo (S (_ : st) m b) = (mempty, S st m False)
resetTo (S [] m b) = (mempty, S [] m False)

data ResetLocation = AtCurly | AfterCurly | AtNewline deriving (Show)

data State = S
  { modeStack :: [(Mode, ResetLocation)],
    base :: Mode,
    encounteredCurly :: Bool
  }
  deriving (Show)

newtype Counter = C {c :: State -> (Counts, State)}

instance Semigroup Counter where
  (C a) <> (C b) = C $ \x ->
    let (c, m) = a x
        (c', m') = b m
     in (c <> c', m')

instance Monoid Counter where
  mempty = C $ \m -> (mempty, m)