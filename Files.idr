module Files
import NGram

Token : Type
Token = String

tokens : String -> List Token
tokens "" = []
tokens str with (break isSpace str)
  tokens str | (a, b) = a :: tokens (assert_smaller str (dropSome b)) where
    dropSome : String -> String
    dropSome str with (span isSpace str)
      | (_, nonspace) = nonspace

learnFromCorpus : String -> Trie String (Nat, Nat)
learnFromCorpus str = probs {n=4} (ngrams 4 (tokens str))
