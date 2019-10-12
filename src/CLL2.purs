module CLL2 where

import Prelude
import Data.Array
import Data.Maybe

import Spork.Html (Html)
import Spork.Html as H
import Web.UIEvent.KeyboardEvent as KE

import Text.Parsing.StringParser
import Text.Parsing.StringParser.CodePoints
import Text.Parsing.StringParser.Expr
import Control.Lazy
import Control.Alternative

import Derivation

-- Short for Formula.
data Form
    = Atom String | Neg Form
    | Tens Form Form | Par  Form Form | One  | Bot
    | Plus Form Form | With Form Form | Zero | Top
    | Ofc Form | Ynot Form
    | Impl Form Form
    | Forall2 String Form | Exists2 String Form


derive instance eqForm :: Eq Form

freeInForm :: String -> Form -> Boolean
freeInForm a form = case form of
  Atom a' -> a == a'
  Neg b -> freeInForm a b
  Tens l r -> freeInForm a l || freeInForm a r
  Par  l r -> freeInForm a l || freeInForm a r
  One -> false
  Bot -> false
  Plus l r -> freeInForm a l || freeInForm a r
  With l r -> freeInForm a l || freeInForm a r
  Zero -> false
  Top  -> false
  Ofc  b -> freeInForm a b
  Ynot b -> freeInForm a b
  Impl l r -> freeInForm a l || freeInForm a r
  Forall2 a' b -> if a == a' then false else freeInForm a b
  Exists2 a' b -> if a == a' then false else freeInForm a b

freshen :: String -> Array Form -> String
freshen a from | all (not <<< freeInForm a) from = a
               | otherwise = freshen (a <> "'") from

subst :: Form -> String -> Form -> Form
subst arg a into = case into of
  Atom a' -> if a' == a then arg else into
  Neg b -> Neg (subst arg a b)
  Tens l r -> Tens (subst arg a l) (subst arg a r)
  Par  l r -> Par  (subst arg a l) (subst arg a r)
  One -> One
  Bot -> Bot
  Plus l r -> Plus (subst arg a l) (subst arg a r)
  With l r -> With (subst arg a l) (subst arg a r)
  Zero -> Zero
  Top  -> Top
  Ofc  b -> Ofc (subst arg a b)
  Ynot b -> Ynot (subst arg a b)
  Impl l r -> Impl (subst arg a l) (subst arg a r)
  Forall2 a' b | a' == a -> into
               | otherwise ->
                 let a'' = freshen a' [arg]
                 in Forall2 a'' (subst arg a (subst (Atom a'') a' b))
  Exists2 a' b | a' == a -> into
               | otherwise ->
                 let a'' = freshen a' [arg]
                 in Exists2 a'' (subst arg a (subst (Atom a'') a' b))

-- alpha equivalence
aeq :: Form -> Form -> Boolean
aeq form1 form2 = case form1, form2 of
  Atom a, Atom a' -> a == a'
  Neg b, Neg b' -> aeq b b'
  Tens l r, Tens l' r' -> aeq l l' && aeq r r'
  Par  l r, Par  l' r' -> aeq l l' && aeq r r'
  One, One -> true
  Bot, Bot -> true
  Plus l r, Plus l' r' -> aeq l l' && aeq r r'
  With l r, With l' r' -> aeq l l' && aeq r r'
  Zero, Zero -> true
  Top,  Top  -> true
  Ofc  b, Ofc  b' -> aeq b b'
  Ynot b, Ynot b' -> aeq b b'
  Impl l r, Impl l' r' -> aeq l l' && aeq r r'
  Forall2 a b, Forall2 a' b' ->
    let a'' = freshen a [b, b', Atom a, Atom a']
    in aeq (subst (Atom a'') a b) (subst (Atom a'') a' b')
  Exists2 a b, Exists2 a' b' ->
    let a'' = freshen a [b, b', Atom a, Atom a']
    in aeq (subst (Atom a'') a b) (subst (Atom a'') a' b')
  _, _ -> false

-- Useful below.
isOfc :: Form -> Boolean
isOfc (Ofc _) = true
isOfc _ = false

isYnot :: Form -> Boolean
isYnot (Ynot _) = true
isYnot _ = false

pickRule :: RuleChoice Form -> ExplodedSequent Form -> PickAction Form
pickRule (RC {button: MiddleButton} _) _ = NoRule
pickRule (RC {button: RightButton} _) eseq = case eseq of
  LeftNG  o@{before, new: new@(Ofc b), after, cqts} ->
    Obligations [before <> [new, new] <> after |- cqts]
  RightNG o@{ants, before, new: new@(Ynot b), after} ->
    Obligations [ants |- before <> [new, new] <> after]
  LeftG  o@{new: Ofc b} -> WrongMode
  RightG o@{new: Ynot b} -> WrongMode
  _ -> NoRule
-- atoms have no rules
pickRule (RC {button: LeftButton} _) eseq | Atom _ <- enew eseq = NoRule
pickRule (RC {button: LeftButton, mpart} inst)
    (LeftNG {before, new, after, cqts}) =
  case new of
    Atom _ -> NoRule -- already covered above, but compiler doesn't know
    Neg b -> Obligations [before <> after |- cqts `snoc` b]
    Tens l r -> Obligations [before <> [l, r] <> after |- cqts]
    Par  l r -> WrongMode
    One -> Obligations [before <> after |- cqts]
    Bot | [before, after, cqts] == [[], [], []] -> Obligations []
        | otherwise -> NoRule
    Plus l r -> Obligations [before <> [l] <> after |- cqts,
                             before <> [r] <> after |- cqts]
    With l r -> case mpart of
      Nothing -> NoRule
      Just part -> Obligations [before <> [byPart l r part] <> after |- cqts]
    Zero -> Obligations []
    Top -> NoRule
    Ofc b -> case mpart of
      Nothing -> NoRule
      Just Part1 -> Obligations [before <> after |- cqts]
      Just Part2 -> Obligations [before <> [b] <> after |- cqts]
    Ynot b | all isOfc (before <> after) && all isYnot cqts ->
             Obligations [before <> [b] <> after |- cqts]
           | otherwise -> NoRule
    Impl _ _ -> WrongMode
    Forall2 a b -> case inst of
      Nothing -> NoRule
      Just arg -> Obligations [before <> [subst arg a b] <> after |- cqts]
    Exists2 a b ->
      let fresh = Atom (freshen a (before <> [new] <> after <> cqts))
      in Obligations [before <> [subst fresh a b] <> after |- cqts]
pickRule (RC {button: LeftButton, mpart} inst)
  (RightNG {ants, before, new, after}) =
  case new of
    Atom _ -> NoRule -- already covered above, but compiler doesn't know
    Neg b -> Obligations [ants `snoc` b |- before <> after]
    Tens l r -> WrongMode
    Par  l r -> Obligations [ants |- before <> [l, r] <> after]
    One | [ants, before, after] == [[], [], []] -> Obligations []
        | otherwise -> NoRule
    Bot -> Obligations [ants |- before <> after]
    Plus l r -> case mpart of
      Nothing -> NoRule
      Just part -> Obligations [ants |- before <> [byPart l r part] <> after]
    With l r -> Obligations [ants |- before <> [l] <> after,
                             ants |- before <> [r] <> after]
    Zero -> NoRule
    Top -> Obligations []
    Ofc b | all isOfc ants && all isYnot (before <> after) ->
            Obligations [ants |- before <> [b] <> after]
          | otherwise -> NoRule
    Ynot b -> case mpart of
      Nothing -> NoRule
      Just Part1 -> Obligations [ants |- before <> after]
      Just Part2 -> Obligations [ants |- before <> [b] <> after]
    Impl l r -> Obligations [ants `snoc` l |- before <> [r] <> after]
    Forall2 a b ->
      let fresh = Atom (freshen a (ants <> before <> [new] <> after))
      in Obligations [ants |- before <> [subst fresh a b] <> after]
    Exists2 a b -> case inst of
      Nothing -> NoRule
      Just arg -> Obligations [ants |- before <> [subst arg a b] <> after]
pickRule (RC {button: LeftButton} _) (LeftG {before, new, after, cqts}) =
  case new of
    Par l r -> Obligations [
      before.group1 <> [l] <> after.group1 |- cqts.group1,
      before.group2 <> [r] <> after.group2 |- cqts.group2]
    Impl l r -> Obligations [
      before.group1 <> after.group1 |- cqts.group1 `snoc` l,
      before.group2 <> [r] <> after.group2 |- cqts.group2]
    _ -> WrongMode
pickRule (RC {button: LeftButton} _)
  (RightG {ants, before, new: Tens l r, after}) =
  Obligations [ants.group1 |- before.group1 <> [l] <> after.group1,
               ants.group2 |- before.group2 <> [r] <> after.group2]
pickRule _ _ = WrongMode


renderForm :: SeqIx -> TaggedForm RenderTag Form -> Html (NodeAction Form)
renderForm seqix {form, tag} =
  let p mpart b = PickedForm {click: {button: b, mpart}, seqix, inst: Nothing}
      clickedQuantifier b = case b of
        LeftButton -> NeedInstantiation seqix
        _ -> p Nothing b
      key ev = case KE.key ev of
        "Enter" -> Just Submit
        "Escape" ->
          Just (ClickedTurnstile {button: RightButton, mpart: Nothing})
        _ -> Nothing
      pp = [ppFormH (-3) form]
  in case tag of
    SideFormR1 -> clickable ["side1"] (p Nothing) pp
    SideFormR2 -> clickable ["side2"] (p Nothing) pp
    HasInput s -> H.span [] [
      H.span [H.classes ["dropdown"]] [
        -- TODO Is there any way to get this to have focus when it's created
        -- without having to completely change the type of the update function
        -- to allow effects???
        H.input [H.value s, H.onValueInput (H.always Input), H.onKeyDown key],
        H.button [H.onClick (H.always (const Submit))] [H.text "Instantiate"]],
      renderForm seqix {form, tag: NewFormR}]
    _ ->
      let clss = if tag == NewFormR then ["new"] else []
      in case seqix.side, form of
        LHS, With l r -> clickable clss (p Nothing) [
          clickable [] (p (Just Part1)) [ppFormH 3 l], H.text " & ",
          clickable [] (p (Just Part2)) [ppFormH 2 r]]
        RHS, Plus l r -> clickable clss (p Nothing) [
          clickable [] (p (Just Part1)) [ppFormH 1 l], H.text " ⊕ ",
          clickable [] (p (Just Part2)) [ppFormH 0 r]]
        LHS, Ofc b -> clickable clss (p Nothing) [
          clickable [] (p (Just Part1)) [H.text "!"],
          clickable [] (p (Just Part2)) [ppFormH 4 b]]
        RHS, Ynot b -> clickable clss (p Nothing) [
          clickable [] (p (Just Part1)) [H.text "?"],
          clickable [] (p (Just Part2)) [ppFormH 4 b]]
        LHS, Forall2 a b -> clickable clss clickedQuantifier pp
        RHS, Exists2 a b -> clickable clss clickedQuantifier pp
        _, _ -> clickable clss (p Nothing) pp

-- precedence logic totally ripped off from
-- https://stackoverflow.com/a/35403826
ppForm :: Int -> Form -> String
ppForm prec form = case form of
  Atom a -> a
  Neg b -> p 4 $ "¬" <> ppForm 4 b -- wrong symbol?
  Tens l r -> p 3 $ ppForm 4 l <> " ⊗ " <> ppForm 3 r
  Par  l r -> p 1 $ ppForm 2 l <> " ⅋ " <> ppForm 1 r
  One -> "1"
  Bot -> "⊥"
  Plus l r -> p 0 $ ppForm 1 l <> " ⊕ " <> ppForm 0 r
  With l r -> p 2 $ ppForm 3 l <> " & " <> ppForm 2 r
  Zero -> "0"
  Top  -> "⊤"
  Ofc  b -> p 4 $ "!" <> ppForm 4 b
  Ynot b -> p 4 $ "?" <> ppForm 4 b
  Impl l r -> p (-1) $ ppForm 0 l <> " ⊸ " <> ppForm (-1) r
  Forall2 a b -> p (-2) $ "∀" <> a <> "." <> ppForm (-2) b
  Exists2 a b -> p (-2) $ "∃" <> a <> "." <> ppForm (-2) b
  where p prec' s | prec <= prec' = s
                  | otherwise = "(" <> s <> ")"

ppFormH :: forall act. Int -> Form -> Html act
ppFormH prec = H.text <<< ppForm prec


formParser :: Unit -> Parser Form
formParser _ = skipSpaces *> buildExprParser table (defer expr) <* skipSpaces

table :: OperatorTable Form
table = [
  [Prefix (Neg <$ spaced "~"), Prefix (Ofc <$ spaced "!"),
   Prefix (Ynot <$ spaced "?")],
  [Infix (Tens <$ spaced "*") AssocRight,
   Infix (Par <$ spaced "@") AssocRight],
  [Infix (Plus <$ spaced "+") AssocRight,
   Infix (With <$ spaced "&") AssocRight],
  [Infix (Impl <$ spaced "-o") AssocRight],
  [Prefix (Forall2 <$ spaced "forall" <*> regex "\\w[\\w']*" <* spaced ","),
   Prefix (Exists2 <$ spaced "exists" <*> regex "\\w[\\w']*"  <* spaced ",")]]
  where spaced op = try $ skipSpaces *> string op <* skipSpaces

expr :: Unit -> Parser Form
expr _ = char '(' *> defer formParser <* char ')' <|>
  One  <$ string "1" <|>
  Bot  <$ string "F" <|>
  Zero <$ string "0" <|>
  Top  <$ string "T" <|>
  Atom <$> regex "\\w[\\w']*"


instance cllCalculus :: Calculus Form where
  pickRule = pickRule
  formParser = formParser
  equiv = aeq
instance cllRender :: RenderForm Form where
  renderForm = renderForm

