module Derivation where

import Prelude
import Data.Array hiding (init)
import Data.Maybe
import Data.Monoid
import Data.Tuple
import Partial.Unsafe
import Data.Function

import Spork.Html (Html)
import Spork.Html as H
import Web.UIEvent.MouseEvent as ME
import Web.UIEvent.KeyboardEvent as KE

import Text.Parsing.StringParser
import Text.Parsing.StringParser.CodePoints
import Text.Parsing.StringParser.Combinators
import Text.Parsing.StringParser.Expr
import Data.Either
import Control.Lazy
import Control.Alternative
import Data.List as L

-- MODEL

-- Short for Formula.
data Form
    = Atom String | Neg Form
    | Tens Form Form | Par  Form Form | One  | Bot
    | Plus Form Form | With Form Form | Zero | Top
    | Ofc Form | Ynot Form
    | Impl Form Form
    | Forall2 String Form | Exists2 String Form
-- We will need to tag our formulas for UI reasons when they are stored as
-- application state.
type Forms = Array Form
type TaggedForm tag = {form :: Form, tag :: tag}
type TaggedForms tag = Array (TaggedForm tag)
data TaggedSequent tag = Entails (TaggedForms tag) (TaggedForms tag)
type Sequent = TaggedSequent Unit

derive instance eqForm :: Eq Form

unitaggedEntails :: Forms -> Forms -> Sequent
unitaggedEntails = Entails `on` map {form: _, tag: unit}
infix 4 unitaggedEntails as |-

data SeqSide = LHS | RHS
type SeqIx = {side :: SeqSide, ix :: Int}

derive instance eqSeqSide :: Eq SeqSide

-- "ants" = "antecedents", "cqts" = "consequents"
mapTagsI :: forall tag tag'. (SeqIx -> tag -> tag') ->
  TaggedSequent tag -> TaggedSequent tag'
mapTagsI f (Entails ants cqts) = Entails (go LHS ants) (go RHS cqts)
  where go side = mapWithIndex (\ix p -> p{tag = f {side, ix} p.tag})

mapTags :: forall tag tag'. (tag -> tag') ->
  TaggedSequent tag -> TaggedSequent tag'
mapTags = mapTagsI <<< const

-- If we have some end-sequent G |- D, then in general there are four things
-- we might need in order to specify a choice of (non-Cut, non-Ax)
-- fully-instantiated rule producing G |- D:
-- 1. Which formula in the sequent is being introduced.
-- 2. Which rule is being used to introduce it.
-- 3. For some rules, a division of the side formulas into subparts to be
--    distributed between the premises of the rule.
-- 4. For some of the quantifier rules, something to instantiate the bound
--    variable with.
--
-- We indicate #1 by clicking on the formula. Since there are in general only a
-- few candidate rules once the connective being introduced is known, we can
-- indicate #2 by the combination of which mouse button is used and where on
-- the formula we click. For #3, we will only be considering rules with exactly
-- two metavariables on each side for groups of side formulas, so we will allow
-- side formulas to be toggled between the two groups by clicking on them
-- subsequent to clicking on the connective to be introduced. For #4, we'll
-- open a little dropdown textbox below the formula being introduced (once it
-- has been clicked to select it) and let the user enter something.

-- We'll represent data #1 and #2 using tags on the formulas in the sequent.

-- Tags for the formulas of a sequent which is the conclusion of a rule that
-- does [N]ot require [G]rouping of the formulas in its conclusion. There
-- should always be exactly one formula tagged with NewFormNG, and we will
-- assume so below. Maybe refactor so that this is statically enforced?
data NGTag = NewFormNG | SideFormNG
-- Tags for the formulas of a sequent which is the conclusion of a rule that
-- *does* require [G]rouping of the formulas in its conclusion. Above note
-- about NewFormNG also applies to NewFormG.
data GTag = NewFormG | SideFormG1 | SideFormG2

derive instance eqNGTag :: Eq NGTag
derive instance eqGTag :: Eq GTag

-- Eliminators for convenience.
ngTag :: forall a. a -> a -> NGTag -> a
ngTag new side NewFormNG  = new
ngTag new side SideFormNG = side

gTag :: forall a. a -> a -> a -> GTag -> a
gTag new side1 side2 NewFormG   = new
gTag new side1 side2 SideFormG1 = side1
gTag new side1 side2 SideFormG2 = side2

-- Data #2.
data Button = LeftButton | MiddleButton | RightButton
-- Typically Part1 is the left operand of a connective and Part2 is the right
-- operand.
data FormPart = Part1 | Part2
-- We will only bother to store a part in cases where we know that the
-- information will be used, like for clicks on conjunction antecedents. We
-- will also have Nothing if the click was, e.g., on the connective itself
-- rather than one of the operands.
type Click = {button :: Button, mpart :: Maybe FormPart}
-- The UI code will send a Click whenever the user actually clicks, but in some
-- cases those clicks will mean something like toggling or canceling rather
-- than an actual choice of rule. A Click will be put into this type if we have
-- processed it to the point of knowing that it will serve to pick a rule.
-- The second field contains the formula with which to instantiate a quantifier
-- rule, if one has been given.
data RuleChoice = RC Click (Maybe Form)

-- Eliminator for convenience.
byPart :: forall a. a -> a -> FormPart -> a
byPart x y Part1 = x
byPart x y Part2 = y

type GroupedForms = {group1 :: Forms, group2 :: Forms}
-- A sequent which has been decomposed according to the tags and positions of
-- its constituent formulas. This provides a much more convenient encoding of
-- data #1 and #3 than tags do. It also provides a single type, whereas grouped
-- vs non-grouped tagged sequents have different types.
data ExplodedSequent
  -- An ungrouped sequent whose new formula is on the left.
  = LeftNG {before :: Forms, new :: Form, after :: Forms, cqts :: Forms}
  -- An ungrouped sequent whose new formula is on the right.
  -- "ants" = "antecedents"
  | RightNG {ants :: Forms, before :: Forms, new :: Form, after :: Forms}
  -- A grouped sequent whose new formula is on the left.
  | LeftG {before :: GroupedForms, new :: Form, after :: GroupedForms,
           cqts :: GroupedForms}
  -- A grouped sequent whose new formula is on the right.
  | RightG {ants :: GroupedForms,
            before :: GroupedForms, new :: Form, after :: GroupedForms}

enew :: ExplodedSequent -> Form
enew = case _ of
  LeftNG  {new} -> new
  RightNG {new} -> new
  LeftG   {new} -> new
  RightG  {new} -> new

-- Functions for processing tagged sequents into exploded ones.

explodeNG :: TaggedSequent NGTag -> ExplodedSequent
explodeNG (Entails ants cqts) =
  case splitAtNew ants, splitAtNew cqts of
    Just {init, head, tail}, _ ->
      LeftNG {before: untag init, new: head.form, after: untag tail,
              cqts: untag cqts}
    Nothing, Just {init, head, tail} ->
      RightNG {ants: untag ants,
               before: untag init, new: head.form, after: untag tail}
    Nothing, Nothing -> unsafeCrashWith "no new formula?!"
  where splitAtNew forms
          | {init, rest} <- span (\{tag} -> tag /= NewFormNG) forms,
            Just {head, tail} <- uncons rest,
            head.tag == NewFormNG = Just {init, head, tail}
          | otherwise = Nothing
        untag = map _.form

explodeG :: TaggedSequent GTag -> ExplodedSequent
explodeG (Entails ants cqts) =
  case splitAtNew ants, splitAtNew cqts of
    Just {init, head, tail}, _ ->
      LeftG {before: group init, new: head.form, after: group tail,
             cqts: group cqts}
    Nothing, Just {init, head, tail} ->
      RightG {ants: group ants,
              before: group init, new: head.form, after: group tail}
    Nothing, Nothing -> unsafeCrashWith "no new formula?!"
  where splitAtNew forms
          | {init, rest} <- span (\{tag} -> tag /= NewFormG) forms,
            Just {head, tail} <- uncons rest,
            head.tag == NewFormG = Just {init, head, tail}
          | otherwise = Nothing
        group forms = let p = partition (\{tag} -> tag == SideFormG1) forms
                      in {group1: untag p.yes, group2: untag p.no}
        untag = map _.form

-- Useful below.
isOfc :: Form -> Boolean
isOfc (Ofc _) = true
isOfc _ = false

isYnot :: Form -> Boolean
isYnot (Ynot _) = true
isYnot _ = false

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

-- Here's the real meat of the sequent calculus logic.
-- The next function takes a provoking click and an exploded sequent, and it
-- replies with one of:
data PickAction
    -- There is no rule with a suitable conclusion.
    = NoRule
    -- There is a rule with a suitable conclusion, but it expects grouping and
    -- none was given (or vice versa).
    | WrongMode
    -- There is a rule with a suitable conclusion, and here are its premises.
    | Obligations (Array Sequent)
pickRule :: RuleChoice -> ExplodedSequent -> PickAction
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

-- Model is a recursive type---each sub-derivation will be a Model, not just
-- the root one. So the choice of mode only indicates the interaction state of
-- the *root* of the derivation described by the value.
data Model
  -- A derivation for which we have not yet picked a rule to apply. In this
  -- mode, clicking on a formula indicates an attempt to introduce it.
  = Assertion Sequent
  -- A derivation where a quantifier formula has been selected to introduce
  -- whose rule will need a choice of formula for instantiation, so a text box
  -- is being shown to allow the user to enter one.
  | Instantiating {conc :: Sequent, seqix :: SeqIx, input :: String}
  -- A derivation whose end-sequent is the conclusion of a rule.
  | Conclusion {subprfs :: Array Model,
                rule :: RuleChoice, wconc :: Conclusion}
data Conclusion
  -- The conclusion of a rule that does not require grouping. In this mode,
  -- clicking on a formula works like in Assertion, and will probably cause us
  -- to change to a new rule.
  = ConcNG (TaggedSequent NGTag)
  -- The conclusion of a rule that *does* require grouping. In this mode,
  -- clicking on a formula toggles its grouping.
  | ConcG (TaggedSequent GTag)

unitaggedConc :: Model -> Sequent
unitaggedConc (Assertion conc) = conc
unitaggedConc (Instantiating {conc}) = conc
unitaggedConc (Conclusion {wconc: ConcNG conc}) = mapTags (const unit) conc
unitaggedConc (Conclusion {wconc: ConcG  conc}) = mapTags (const unit) conc

complete :: Model -> Boolean
complete (Assertion _) = false
complete (Instantiating _) = false
complete (Conclusion {subprfs}) = all complete subprfs

-- UPDATE

data NodeAction = ClickedTurnstile Click |
  PickedForm {click :: Click, seqix :: SeqIx, inst :: Maybe Form} |
  -- Clicking a quantifier that needs a formula to instantiate with will
  -- produce a NeedInstantiation rather than a PickedForm. Subsequently,
  -- interaction with the spawned text box and button will produce Input and
  -- Submit actions.
  NeedInstantiation SeqIx | Input String | Submit
data Action = ChildAction Int Action | NAction NodeAction

update :: Model -> Action -> Model
update prf (NAction nact) = updateNode prf nact
update (Conclusion o@{subprfs}) (ChildAction ix act) =
  Conclusion o{subprfs =
    fromMaybe subprfs (modifyAt ix (flip update act) subprfs)}
update prf _ = prf

updateNode :: Model -> NodeAction -> Model
updateNode prf (ClickedTurnstile {button: MiddleButton}) = prf
updateNode prf (ClickedTurnstile {button: RightButton}) =
  Assertion (unitaggedConc prf)
updateNode prf (ClickedTurnstile click@{button: LeftButton})
  | conc@(Entails [ant] [cqt]) <- unitaggedConc prf,
    ant == cqt =
    Conclusion {subprfs: [], rule: RC click Nothing,
    wconc: ConcNG (Entails [ant{tag = SideFormNG}] [cqt{tag = NewFormNG}])}
  | otherwise = prf
-- Necessary assumption for invariant to be preserved: seqix exists in the
-- end-sequent.
-- ...is that actually safe to assume?...
-- TODO There are a few kinds of interaction to add (left-clicking the new
-- formula should cancel, etc).
updateNode prf (PickedForm {click, seqix, inst}) = fromMaybe prf $ case prf of
  Conclusion {rule, wconc: ConcG conc} ->
    let chtag seqix' = if seqix' == seqix
          then gTag NewFormG SideFormG2 SideFormG1 else identity
    -- Note that we reuse the saved rule choice rather than wrapping the new
    -- click, since the new click is a toggle and not a rule choice.
    in applyRule rule (ConcG (mapTagsI chtag conc))
  -- Clicking does the same thing in Assertion, Instantiating, and ConcNG.
  _ ->
    let chtag seqix' _ = if seqix' == seqix then NewFormNG else SideFormNG
    in applyRule (RC click inst) (ConcNG (mapTagsI chtag (unitaggedConc prf)))
updateNode prf (NeedInstantiation seqix) =
  Instantiating {conc: unitaggedConc prf, seqix, input: ""}
updateNode prf (Input s) = case prf of
  Instantiating o -> Instantiating o{input = s}
  _ -> prf -- Shouldn't happen?
updateNode prf Submit = case prf of
  Instantiating {conc, seqix, input}
    | Right form <- runParser (formParser unit) input ->
      let nact' = PickedForm {click: {button: LeftButton, mpart: Nothing},
                              seqix, inst: Just form}
      in updateNode prf nact'
  _ -> prf

applyRule :: RuleChoice -> Conclusion -> Maybe Model
applyRule rule wconc = case pickRule rule exploded of
  NoRule -> Nothing
  WrongMode -> applyRule rule omode
  Obligations obs -> Just $
    Conclusion {subprfs: map Assertion obs, rule, wconc}
  where Tuple exploded omode = case wconc of
          ConcNG conc -> Tuple (explodeNG conc) $
            ConcG (mapTags (ngTag NewFormG SideFormG1) conc)
          ConcG conc -> Tuple (explodeG conc) $
            ConcNG (mapTags (gTag  NewFormNG SideFormNG SideFormNG) conc)

-- VIEW

-- We'll translate all tags into this one sum type for the benefit of the
-- renderForm function.
data RenderTag
  = NewFormR | SideFormR | SideFormR1 | SideFormR2
  -- This tag indicates that the formula has a textbox with the given input
  -- associated to it.
  | HasInput String

derive instance eqRenderTag :: Eq RenderTag

renderDerivation :: Model -> Html Action
renderDerivation prf =
  H.div [H.classes ["derivation", guard (complete prf) "complete"]]
  case prf of
    Assertion conc -> [renderConc (mapTags (const SideFormR) conc)]
    Instantiating {conc, seqix, input} ->
      let chtag seqix' = if seqix' == seqix
            then const (HasInput input) else const SideFormR
       in [renderConc (mapTagsI chtag conc)]
    Conclusion {subprfs, wconc} -> [
      let rsp ix subprf = map (ChildAction ix) (renderDerivation subprf)
      in H.div [] (mapWithIndex rsp subprfs),
      H.hr [],
      let conc = case wconc of
            ConcNG conc -> mapTags (ngTag NewFormR SideFormR) conc
            ConcG  conc -> mapTags (gTag  NewFormR SideFormR1 SideFormR2) conc
      in renderConc conc]
  where renderConc = map NAction <<< renderSequent

-- TODO inefficient!!!
intersperse :: forall a. a -> Array a -> Array a
intersperse sep arr = case uncons arr of
  Nothing -> []
  Just {head, tail: []} -> [head]
  Just {head, tail} -> [head, sep] <> intersperse sep tail

clickable :: forall act.
  Array String -> (Button -> act) -> Array (Html act) -> Html act
clickable clss act = H.span [H.classes (["clickable"] <> clss),
  H.onMouseDown (map act <<< buttonFor)]
  where buttonFor e = case ME.button e, ME.ctrlKey e of
          0, false -> Just LeftButton
          0, true -> Just MiddleButton
          1, _ -> Just MiddleButton
          2, _ -> Just RightButton
          _, _ -> Nothing

renderSequent :: TaggedSequent RenderTag -> Html NodeAction
renderSequent seq@(Entails ants cqts) =
  H.span [] (half LHS ants <> [turnstile] <> half RHS cqts)
  where half side = intersperse (H.text ", ") <<<
          mapWithIndex (\ix -> renderForm {side, ix})
        turnstile = clickable []
          (ClickedTurnstile <<< {button: _, mpart: Nothing})
          [H.text " ⊢ "]

renderForm :: SeqIx -> TaggedForm RenderTag -> Html NodeAction
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

sequentParser :: Parser Sequent
sequentParser = (|-) <$> forms <*> (string "|-" *> forms)
  where forms = map L.toUnfoldable $
    skipSpaces *> (formParser unit `sepBy` char ',') <* skipSpaces

