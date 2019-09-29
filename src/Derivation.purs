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

import Text.Parsing.StringParser
import Data.Either

-- TODO Edit the comments to reflect the reorganization with typeclasses and
-- separate modules.

-- MODEL

-- We will need to tag our formulas for UI reasons when they are stored as
-- application state.
type TaggedForm tag form = {form :: form, tag :: tag}
type TaggedForms tag form = Array (TaggedForm tag form)
data TaggedSequent tag form =
  Entails (TaggedForms tag form) (TaggedForms tag form)
type Sequent form = TaggedSequent Unit form

derive instance functorTaggedSequent :: Functor (TaggedSequent tag)

unitaggedEntails :: forall form. Array form -> Array form -> Sequent form
unitaggedEntails = Entails `on` map {form: _, tag: unit}
infix 4 unitaggedEntails as |-

data SeqSide = LHS | RHS
type SeqIx = {side :: SeqSide, ix :: Int}

derive instance eqSeqSide :: Eq SeqSide

-- "ants" = "antecedents", "cqts" = "consequents"
mapTagsI :: forall tag tag' form. (SeqIx -> tag -> tag') ->
  TaggedSequent tag form -> TaggedSequent tag' form
mapTagsI f (Entails ants cqts) = Entails (go LHS ants) (go RHS cqts)
  where go side = mapWithIndex (\ix p -> p{tag = f {side, ix} p.tag})

mapTags :: forall tag tag' form. (tag -> tag') ->
  TaggedSequent tag form -> TaggedSequent tag' form
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
data RuleChoice form = RC Click (Maybe form)

derive instance functorRuleChoice :: Functor RuleChoice

-- Eliminator for convenience.
byPart :: forall a. a -> a -> FormPart -> a
byPart x y Part1 = x
byPart x y Part2 = y

type GroupedForms form = {group1 :: Array form, group2 :: Array form}
-- A sequent which has been decomposed according to the tags and positions of
-- its constituent formulas. This provides a much more convenient encoding of
-- data #1 and #3 than tags do. It also provides a single type, whereas grouped
-- vs non-grouped tagged sequents have different types.
data ExplodedSequent form
  -- An ungrouped sequent whose new formula is on the left.
  = LeftNG {before :: Array form, new :: form, after :: Array form,
            cqts :: Array form}
  -- An ungrouped sequent whose new formula is on the right.
  -- "ants" = "antecedents"
  | RightNG {ants :: Array form,
             before :: Array form, new :: form, after :: Array form}
  -- A grouped sequent whose new formula is on the left.
  | LeftG {before :: GroupedForms form, new :: form,
           after :: GroupedForms form, cqts :: GroupedForms form}
  -- A grouped sequent whose new formula is on the right.
  | RightG {ants :: GroupedForms form, before :: GroupedForms form,
            new :: form, after :: GroupedForms form}

derive instance functorExplodedSequent :: Functor ExplodedSequent

enew :: forall form. ExplodedSequent form -> form
enew = case _ of
  LeftNG  {new} -> new
  RightNG {new} -> new
  LeftG   {new} -> new
  RightG  {new} -> new

-- Functions for processing tagged sequents into exploded ones.

explodeNG :: forall form. TaggedSequent NGTag form -> ExplodedSequent form
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

explodeG :: forall form. TaggedSequent GTag form -> ExplodedSequent form
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
data PickAction form
    -- There is no rule with a suitable conclusion.
    = NoRule
    -- There is a rule with a suitable conclusion, but it expects grouping and
    -- none was given (or vice versa).
    | WrongMode
    -- There is a rule with a suitable conclusion, and here are its premises.
    | Obligations (Array (Sequent form))

derive instance functorPickAction :: Functor PickAction

class Eq form <= Calculus form where
  pickRule :: RuleChoice form -> ExplodedSequent form -> PickAction form
  formParser :: Unit -> Parser form

-- Model is a recursive type---each sub-derivation will be a Model, not just
-- the root one. So the choice of mode only indicates the interaction state of
-- the *root* of the derivation described by the value.
data Model form
  -- A derivation for which we have not yet picked a rule to apply. In this
  -- mode, clicking on a formula indicates an attempt to introduce it.
  = Assertion (Sequent form)
  -- A derivation where a quantifier formula has been selected to introduce
  -- whose rule will need a choice of formula for instantiation, so a text box
  -- is being shown to allow the user to enter one.
  | Instantiating {conc :: Sequent form, seqix :: SeqIx, input :: String}
  -- A derivation whose end-sequent is the conclusion of a rule.
  | Conclusion {subprfs :: Array (Model form),
                rule :: (RuleChoice form), wconc :: (Conclusion form)}
data Conclusion form
  -- The conclusion of a rule that does not require grouping. In this mode,
  -- clicking on a formula works like in Assertion, and will probably cause us
  -- to change to a new rule.
  = ConcNG (TaggedSequent NGTag form)
  -- The conclusion of a rule that *does* require grouping. In this mode,
  -- clicking on a formula toggles its grouping.
  | ConcG (TaggedSequent GTag form)

unitaggedConc :: forall form. Model form -> Sequent form
unitaggedConc (Assertion conc) = conc
unitaggedConc (Instantiating {conc}) = conc
unitaggedConc (Conclusion {wconc: ConcNG conc}) = mapTags (const unit) conc
unitaggedConc (Conclusion {wconc: ConcG  conc}) = mapTags (const unit) conc

complete :: forall form. Model form -> Boolean
complete (Assertion _) = false
complete (Instantiating _) = false
complete (Conclusion {subprfs}) = all complete subprfs

-- UPDATE

data NodeAction form = ClickedTurnstile Click |
  PickedForm {click :: Click, seqix :: SeqIx, inst :: Maybe form} |
  -- Clicking a quantifier that needs a formula to instantiate with will
  -- produce a NeedInstantiation rather than a PickedForm. Subsequently,
  -- interaction with the spawned text box and button will produce Input and
  -- Submit actions.
  NeedInstantiation SeqIx | Input String | Submit
data Action form = ChildAction Int (Action form) | NAction (NodeAction form)

derive instance functorNodeAction :: Functor NodeAction

update :: forall form. Calculus form => Model form -> Action form -> Model form
update prf (NAction nact) = updateNode prf nact
update (Conclusion o@{subprfs}) (ChildAction ix act) =
  Conclusion o{subprfs =
    fromMaybe subprfs (modifyAt ix (flip update act) subprfs)}
update prf _ = prf

updateNode :: forall form. Calculus form =>
  Model form -> NodeAction form -> Model form
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

applyRule :: forall form. Calculus form =>
  RuleChoice form -> Conclusion form -> Maybe (Model form)
applyRule rule wconc = case pickRule rule exploded of
  NoRule -> Nothing
  WrongMode -> applyRule rule omode
  Obligations obs -> Just $
    Conclusion {subprfs: map Assertion obs, rule, wconc}
  where Tuple exploded omode = case wconc of
          ConcNG conc -> Tuple (explodeNG conc) $
            ConcG (mapTags (ngTag NewFormG SideFormG2) conc)
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

class RenderForm form where
  renderForm :: SeqIx -> TaggedForm RenderTag form -> Html (NodeAction form)

renderDerivation :: forall form. RenderForm form =>
  Model form -> Html (Action form)
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

renderSequent :: forall form. RenderForm form =>
  TaggedSequent RenderTag form -> Html (NodeAction form)
renderSequent seq@(Entails ants cqts) =
  H.span [] (half LHS ants <> [turnstile] <> half RHS cqts)
  where half side = intersperse (H.text ", ") <<<
          mapWithIndex (\ix -> renderForm {side, ix})
        turnstile = clickable []
          (ClickedTurnstile <<< {button: _, mpart: Nothing})
          [H.text " ⊢ "]

