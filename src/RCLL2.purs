module RCLL2 where

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
    = Atom String | NegAtom String
    | Tens Form Form | Par  Form Form | One  | Bot
    | Plus Form Form | With Form Form | Zero | Top
    | Ofc Form | Ynot Form
    | Forall2 String Form | Exists2 String Form

neg :: Form -> Form
neg form = case form of
  Atom a -> NegAtom a
  NegAtom a -> Atom a
  Tens l r -> Par (neg l) (neg r)
  Par  l r -> Tens (neg l) (neg r)
  One -> Bot
  Bot -> One
  Plus l r -> With (neg l) (neg r)
  With l r -> Plus (neg l) (neg r)
  Zero -> Top
  Top  -> Zero
  Ofc  b -> Ynot (neg b)
  Ynot b -> Ofc (neg b)
  Forall2 a b -> Exists2 a (neg b)
  Exists2 a b -> Forall2 a (neg b)

impl :: Form -> Form -> Form
impl l r = Par (neg l) r


derive instance eqForm :: Eq Form

freeInForm :: String -> Form -> Boolean
freeInForm a form = case form of
  Atom a' -> a == a'
  NegAtom a' -> a == a'
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
  Forall2 a' b -> if a == a' then false else freeInForm a b
  Exists2 a' b -> if a == a' then false else freeInForm a b

freshen :: String -> Array Form -> String
freshen a from | all (not <<< freeInForm a) from = a
               | otherwise = freshen (a <> "'") from

subst :: Form -> String -> Form -> Form
subst arg a into = case into of
  Atom a' -> if a' == a then arg else into
  NegAtom a' -> if a' == a then neg arg else into
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
  NegAtom a, NegAtom a' -> a == a'
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
  Forall2 a b, Forall2 a' b' ->
    let a'' = freshen a [b, b', Atom a, Atom a']
    in aeq (subst (Atom a'') a b) (subst (Atom a'') a' b')
  Exists2 a b, Exists2 a' b' ->
    let a'' = freshen a [b, b', Atom a, Atom a']
    in aeq (subst (Atom a'') a b) (subst (Atom a'') a' b')
  _, _ -> false

-- Useful below.
isYnot :: Form -> Boolean
isYnot (Ynot _) = true
isYnot _ = false

hasAnts :: forall form. ExplodedSequent form -> Boolean
hasAnts = case _ of
  LeftNG  _      -> true
  RightNG {ants} -> not (null ants)
  LeftG   _      -> true
  RightG  {ants} -> not (null ants.group1) || not (null ants.group2)

-- TODO Fiddle with the architecture so that we can have the Axiom for
-- non-atoms if we'd like, and by clicking on the turnstile like in the other
-- systems.
pickRule :: RuleChoice Form -> ExplodedSequent Form -> PickAction Form
pickRule _ eseq | hasAnts eseq = NoRule
pickRule (RC {button: MiddleButton} _) _ = NoRule
pickRule (RC {button: RightButton} _) eseq = case eseq of
  RightNG o@{before, new: new@(Ynot b), after} ->
    Obligations [[] |- before <> [new, new] <> after]
  RightG o@{new: Ynot b} -> WrongMode
  _ -> NoRule
pickRule (RC {button: LeftButton, mpart} inst) (RightNG {before, new, after}) =
  case new of
    Atom a | before <> after == [NegAtom a] -> Obligations []
           | otherwise -> NoRule
    NegAtom _ -> NoRule
    Tens l r -> WrongMode
    Par  l r -> Obligations [[] |- before <> [l, r] <> after]
    One | [before, after] == [[], []] -> Obligations []
        | otherwise -> NoRule
    Bot -> Obligations [[] |- before <> after]
    Plus l r -> case mpart of
      Nothing -> NoRule
      Just part -> Obligations [[] |- before <> [byPart l r part] <> after]
    With l r -> Obligations [[] |- before <> [l] <> after,
                             [] |- before <> [r] <> after]
    Zero -> NoRule
    Top -> Obligations []
    Ofc b | all isYnot (before <> after) ->
            Obligations [[] |- before <> [b] <> after]
          | otherwise -> NoRule
    Ynot b -> case mpart of
      Nothing -> NoRule
      Just Part1 -> Obligations [[] |- before <> after]
      Just Part2 -> Obligations [[] |- before <> [b] <> after]
    Forall2 a b ->
      let fresh = Atom (freshen a (before <> [new] <> after))
      in Obligations [[] |- before <> [subst fresh a b] <> after]
    Exists2 a b -> case inst of
      Nothing -> NoRule
      Just arg -> Obligations [[] |- before <> [subst arg a b] <> after]
pickRule (RC {button: LeftButton} _) (RightG {before, new: Tens l r, after}) =
  Obligations [[] |- before.group1 <> [l] <> after.group1,
               [] |- before.group2 <> [r] <> after.group2]
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
      in case form of
        Plus l r -> clickable clss (p Nothing) [
          clickable [] (p (Just Part1)) [ppFormH 1 l], H.text " ⊕ ",
          clickable [] (p (Just Part2)) [ppFormH 0 r]]
        Ynot b -> clickable clss (p Nothing) [
          clickable [] (p (Just Part1)) [H.text "?"],
          clickable [] (p (Just Part2)) [ppFormH 4 b]]
        Exists2 a b -> clickable clss clickedQuantifier pp
        _ -> clickable clss (p Nothing) pp

-- precedence logic totally ripped off from
-- https://stackoverflow.com/a/35403826
ppForm :: Int -> Form -> String
ppForm prec form = case form of
  Atom a -> a
  NegAtom a -> "¬" <> a -- wrong symbol?
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
  [Prefix (neg <$ spaced "~"), Prefix (Ofc <$ spaced "!"),
   Prefix (Ynot <$ spaced "?")],
  [Infix (Tens <$ spaced "*") AssocRight,
   Infix (Par <$ spaced "@") AssocRight],
  [Infix (Plus <$ spaced "+") AssocRight,
   Infix (With <$ spaced "&") AssocRight],
  [Infix (impl <$ spaced "-o") AssocRight],
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
  okInitial (Entails ants _) = null ants
instance cllRender :: RenderForm Form where
  renderForm = renderForm

