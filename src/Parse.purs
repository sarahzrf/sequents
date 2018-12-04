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
  [Prefix (Neg <$ spaced "~"), Prefix (Ofc <$ spaced "!"),
   Prefix (Ynot <$ spaced "?")],
  [Infix (Tens <$ spaced "*") AssocRight,
   Infix (Par <$ spaced "@") AssocRight],
  [Infix (Plus <$ spaced "+") AssocRight,
   Infix (With <$ spaced "&") AssocRight]]
  where spaced op = try $ skipSpaces *> string op <* skipSpaces

expr :: Unit -> Parser Form
expr _ = char '(' *> defer formParser <* char ')' <|>
  One  <$ string "1" <|>
  Bot  <$ string "F" <|>
  Zero <$ string "0" <|>
  Top  <$ string "T" <|>
  Atom <$> regex "\\w+"

sequentParser :: Parser Sequent
sequentParser = (|-) <$> forms <*> (string "|-" *> forms)
  where forms = map toUnfoldable $
    skipSpaces *> (formParser unit `sepBy` char ',') <* skipSpaces

