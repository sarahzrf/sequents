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
import Web.UIEvent.MouseEvent as E

-- MODEL

-- Short for Formula.
data Form = Atom String | Impl Form Form | Conj Form Form
          | Disj Form Form | Neg Form
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

-- If we have some end-sequent G |- D, then in general there are three things
-- we might need in order to specify a choice of (non-Cut, non-Ax)
-- fully-instantiated rule producing G |- D:
-- 1. Which formula in the sequent is being introduced.
-- 2. Which rule is being used to introduce it.
-- 3. For some rules, a division of the side formulas into subparts to be
--    distributed between the premises of the rule.
--
-- We indicate #1 by clicking on the formula. Since there are in general only a
-- few candidate rules once the connective being introduced is known, we can
-- indicate #2 by the combination of which mouse button is used and where on
-- the formula we click. For #3, we will only be considering rules with exactly
-- two metavariables on each side for groups of side formulas, so we will allow
-- side formulas to be toggled between the two groups by clicking on them
-- subsequent to clicking on the connective to be introduced.

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
-- than an actual choice of rule. A Click will be put into this newtype if we
-- have processed it to the point of knowing that it will serve to pick a rule.
newtype RuleChoice = RC Click

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
-- contraction
pickRule (RC {button: RightButton}) (LeftNG {before, new, after, cqts}) =
  Obligations [before <> [new, new] <> after |- cqts]
pickRule (RC {button: RightButton}) (RightNG {ants, before, new, after}) =
  Obligations [ants |- before <> [new, new] <> after]
-- weakening
pickRule (RC {button: MiddleButton}) (LeftNG {before, new, after, cqts}) =
  Obligations [before <> after |- cqts]
pickRule (RC {button: MiddleButton}) (RightNG {ants, before, new, after}) =
  Obligations [ants |- before <> after]
-- atoms have no rules
pickRule (RC {button: LeftButton}) eseq | Atom _ <- enew eseq = NoRule
-- main logical rules
pickRule (RC {button: LeftButton, mpart}) (LeftNG {before, new, after, cqts}) =
  case new of
    Conj l r -> case mpart of
      Nothing -> NoRule
      Just part -> Obligations [before <> [byPart l r part] <> after |- cqts]
    Disj l r -> Obligations [before <> [l] <> after |- cqts,
                             before <> [r] <> after |- cqts]
    Neg b -> Obligations [before <> after |- cqts `snoc` b]
    _ -> WrongMode -- only Impl; Atom was ruled out above
pickRule (RC {button: LeftButton, mpart})
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
pickRule (RC {button: LeftButton})
    (LeftG {before, new: Impl l r, after, cqts}) =
  Obligations [before.group1 <> after.group1 |- l `cons` cqts.group1,
               before.group2 <> [r] <> after.group2 |- cqts.group2]
pickRule _ _ = WrongMode

-- Intuitionistic version!
pickRuleInt :: RuleChoice -> ExplodedSequent -> PickAction
pickRuleInt rule eseq = case pickRule rule eseq of
  pa@(Obligations seqs)
    | all (\(Entails _ cqts) -> length cqts <= 1) seqs -> pa
    | otherwise -> NoRule
  pa -> pa

-- Model is a recursive type---each sub-derivation will be a Model, not just
-- the root one. So the choice of mode only indicates the interaction state of
-- the *root* of the derivation.
data Model
  -- A derivation for which we have not yet picked a rule to apply. In this
  -- mode, clicking on a formula indicates an attempt to introduce it.
  = Assertion Sequent
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
unitaggedConc (Conclusion {wconc: ConcNG conc}) = mapTags (const unit) conc
unitaggedConc (Conclusion {wconc: ConcG  conc}) = mapTags (const unit) conc

complete :: Model -> Boolean
complete (Assertion _) = false
complete (Conclusion {subprfs}) = all complete subprfs

-- UPDATE

data NodeAction = ClickedTurnstile Click |
  ClickedForm {click :: Click, seqix :: SeqIx}
data Action = ChildAction Int Action | NAction NodeAction

update :: Model -> Action -> Model
update prf (NAction nact) = updateNode prf nact
update prf@(Assertion _) _ = prf
update (Conclusion o@{subprfs}) (ChildAction ix act) =
  Conclusion o{subprfs =
    fromMaybe subprfs (modifyAt ix (flip update act) subprfs)}

updateNode :: Model -> NodeAction -> Model
updateNode prf (ClickedTurnstile {button: MiddleButton}) = prf
updateNode prf (ClickedTurnstile {button: RightButton}) =
  Assertion (unitaggedConc prf)
updateNode prf (ClickedTurnstile click@{button: LeftButton})
  | conc@(Entails [ant] [cqt]) <- unitaggedConc prf,
    ant == cqt =
    Conclusion {subprfs: [], rule: RC click,
    wconc: ConcNG (Entails [ant{tag = SideFormNG}] [cqt{tag = NewFormNG}])}
  | otherwise = prf
-- Necessary assumption for invariant to be preserved: seqix exists in the
-- end-sequent.
-- ...is that actually safe to assume?...
-- TODO There are a few kinds of interaction to add (left-clicking the nw
-- formula should cancel, etc).
updateNode prf nact@(ClickedForm {click, seqix}) = fromMaybe prf $ case prf of
  Conclusion {rule, wconc: ConcG conc} ->
    let chtag seqix' = if seqix' == seqix
          then gTag NewFormG SideFormG2 SideFormG1 else identity
    -- Note that we reuse the saved rule choice rather than wrapping the new
    -- click, since the new click is a toggle and not a rule choice.
    in applyRule rule (ConcG (mapTagsI chtag conc))
  -- Clicking does the same thing in Assertion and ConcNG.
  _ ->
    let chtag seqix' _ = if seqix' == seqix then NewFormNG else SideFormNG
    in applyRule (RC click) (ConcNG (mapTagsI chtag (unitaggedConc prf)))

applyRule :: RuleChoice -> Conclusion -> Maybe Model
applyRule rule wconc = case pickRuleInt rule exploded of
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
data RenderTag = NewFormR | SideFormR | SideFormR1 | SideFormR2

derive instance eqRenderTag :: Eq RenderTag

renderDerivation :: Model -> Html Action
renderDerivation prf =
  H.div [H.classes ["derivation", guard (complete prf) "complete"]]
  case prf of
    Assertion conc ->
      [map NAction (renderSequent (mapTags (const SideFormR) conc))]
    Conclusion {subprfs, wconc} -> [
      let rsp ix subprf = map (ChildAction ix) (renderDerivation subprf)
      in H.div [] (mapWithIndex rsp subprfs),
      H.hr [],
      let conc = case wconc of
            ConcNG conc -> mapTags (ngTag NewFormR SideFormR) conc
            ConcG  conc -> mapTags (gTag  NewFormR SideFormR1 SideFormR2) conc
      in map NAction (renderSequent conc)]

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
  where buttonFor e = case E.button e, E.ctrlKey e of
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
  let p mpart = \b -> ClickedForm {click: {button: b, mpart}, seqix}
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

