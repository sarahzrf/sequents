module Parse where

import Prelude
import Text.Parsing.StringParser
import Text.Parsing.StringParser.CodePoints
import Text.Parsing.StringParser.Combinators
import Text.Parsing.StringParser.Expr
import Control.Lazy
import Control.Alternative
import Data.List

import Derivation

-- TODO improve parser
-- e.g., notice garbage at end

formParser :: Unit -> Parser Form
formParser _ = skipSpaces *> buildExprParser table (defer expr) <* skipSpaces

table :: OperatorTable Form
table = [
  [Prefix (Neg <$ spaced "~")],
  [Infix (Conj <$ spaced "/\\") AssocRight,
   Infix (Disj <$ spaced "\\/") AssocRight],
  [Infix (Impl <$ spaced "->") AssocRight]]
  where spaced op = try $ skipSpaces *> string op <* skipSpaces

expr :: Unit -> Parser Form
expr _ = char '(' *> defer formParser <* char ')' <|> Atom <$> regex "\\w+"

sequentParser :: Parser Sequent
sequentParser = (|-) <$> forms <*> (string "|-" *> forms)
  where forms = map toUnfoldable $
    skipSpaces *> (formParser unit `sepBy` char ',') <* skipSpaces

