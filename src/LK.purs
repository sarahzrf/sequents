module LK where

import Prelude
import Data.Array
import Data.Maybe

import Spork.Html (Html)
import Spork.Html as H

import Text.Parsing.StringParser
import Text.Parsing.StringParser.CodePoints
import Text.Parsing.StringParser.Expr
import Control.Lazy
import Control.Alternative

import Derivation

data Form = Atom String | Impl Form Form | Conj Form Form
          | Disj Form Form | Neg Form

derive instance eqForm :: Eq Form

pickRule :: RuleChoice Form -> ExplodedSequent Form -> PickAction Form
-- contraction
pickRule (RC {button: RightButton} _) (LeftNG {before, new, after, cqts}) =
  Obligations [before <> [new, new] <> after |- cqts]
pickRule (RC {button: RightButton} _) (RightNG {ants, before, new, after}) =
  Obligations [ants |- before <> [new, new] <> after]
-- weakening
pickRule (RC {button: MiddleButton} _) (LeftNG {before, new, after, cqts}) =
  Obligations [before <> after |- cqts]
pickRule (RC {button: MiddleButton} _) (RightNG {ants, before, new, after}) =
  Obligations [ants |- before <> after]
-- atoms have no rules
pickRule (RC {button: LeftButton} _) eseq | Atom _ <- enew eseq = NoRule
-- main logical rules
pickRule (RC {button: LeftButton, mpart} _)
  (LeftNG {before, new, after, cqts}) =
  case new of
    Conj l r -> case mpart of
      Nothing -> NoRule
      Just part -> Obligations [before <> [byPart l r part] <> after |- cqts]
    Disj l r -> Obligations [before <> [l] <> after |- cqts,
                             before <> [r] <> after |- cqts]
    Neg b -> Obligations [before <> after |- cqts `snoc` b]
    _ -> WrongMode -- only Impl; Atom was ruled out above
pickRule (RC {button: LeftButton, mpart} _)
  (RightNG {ants, before, new, after}) =
  case new of
    Atom _ -> NoRule -- impossible, but the compiler doesn't realize that
    Impl l r -> Obligations [ants `snoc` l |- before <> [r] <> after]
    Conj l r -> Obligations [ants |- before <> [l] <> after,
                             ants |- before <> [r] <> after]
    Disj l r -> case mpart of
      Nothing -> NoRule
      Just part -> Obligations [ants |- before <> [byPart l r part] <> after]
    Neg b -> Obligations [ants `snoc` b |- before <> after]
pickRule (RC {button: LeftButton} _)
    (LeftG {before, new: Impl l r, after, cqts}) =
  Obligations [before.group1 <> after.group1 |- l `cons` cqts.group1,
               before.group2 <> [r] <> after.group2 |- cqts.group2]
pickRule _ _ = WrongMode


renderForm :: SeqIx -> TaggedForm RenderTag Form -> Html (NodeAction Form)
renderForm seqix {form, tag} =
  let p mpart b = PickedForm {click: {button: b, mpart}, seqix, inst: Nothing}
      pp = [ppFormH (-1) form]
  in case tag of
    SideFormR1 -> clickable ["side1"] (p Nothing) pp
    SideFormR2 -> clickable ["side2"] (p Nothing) pp
    _ ->
      let clss = if tag == NewFormR then ["new"] else []
      in case seqix.side, form of
        LHS, Conj l r -> clickable clss (p Nothing) [
          clickable [] (p (Just Part1)) [ppFormH 3 l], H.text " ∧ ",
          clickable [] (p (Just Part2)) [ppFormH 2 r]]
        RHS, Disj l r -> clickable clss (p Nothing) [
          clickable [] (p (Just Part1)) [ppFormH 2 l], H.text " ∨ ",
          clickable [] (p (Just Part2)) [ppFormH 1 r]]
        _, _ -> clickable clss (p Nothing) pp

-- precedence logic totally ripped off from
-- https://stackoverflow.com/a/35403826
ppForm :: Int -> Form -> String
ppForm prec form = case form of
  Atom a -> a
  Impl l r -> p 0 $ ppForm 1 l <> " → " <> ppForm 0 r
  Conj l r -> p 2 $ ppForm 3 l <> " ∧ " <> ppForm 2 r
  Disj l r -> p 1 $ ppForm 2 l <> " ∨ " <> ppForm 1 r
  Neg b -> p 3 $ "¬" <> ppForm 3 b
  where p prec' s | prec <= prec' = s
                  | otherwise = "(" <> s <> ")"

ppFormH :: forall act. Int -> Form -> Html act
ppFormH prec = H.text <<< ppForm prec


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


instance lkCalculus :: Calculus Form where
  pickRule = pickRule
  formParser = formParser
  equiv = (==)
  okInitial = const true
instance lkRender :: RenderForm Form where
  renderForm = renderForm

