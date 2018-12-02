module Main where

import Prelude
import Data.Array hiding (init)
import Data.Maybe
import Data.Monoid
import Data.Tuple
import Partial.Unsafe
import Data.Function

import Effect (Effect)
import Spork.Html (Html)
import Spork.Html as H
import Spork.PureApp as PureApp


main :: Effect Unit
main = void $ PureApp.makeWithSelector app "body"
  where app = {init, update, render}

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

unitag :: forall tag. TaggedSequent tag -> Sequent
-- "ants" = "antecedents", "cqts" = "consequents"
unitag (Entails ants cqts) = Entails (u ants) (u cqts)
  where u = map _{tag = unit}

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

-- Data #2.
data Button = LeftButton | RightButton
-- Typically Part1 is the left operand of a connective and Part2 is the right
-- operand. In cases like negation where this never matters, we'll just use
-- Part1.
data FormPart = Part1 | Part2
type Click = {button :: Button, part :: FormPart}

-- a utility
byPart :: forall a. FormPart -> a -> a -> a
byPart Part1 x y = x
byPart Part2 x y = y

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
data PickAction = NoRule | WrongMode | Obligations (Array Sequent)
pickRule :: Click -> ExplodedSequent -> PickAction
-- contraction
pickRule {button: RightButton} (LeftNG {before, new, after, cqts}) =
  Obligations [before <> [new, new] <> after |- cqts]
pickRule {button: RightButton} (RightNG {ants, before, new, after}) =
  Obligations [ants |- before <> [new, new] <> after]
-- atoms have no rules
pickRule {button: LeftButton} eseq | Atom _ <- enew eseq = NoRule
-- main logical rules
pickRule {button: LeftButton, part} (LeftNG {before, new, after, cqts}) =
  case new of
    Conj l r -> Obligations [before <> [byPart part l r] <> after |- cqts]
    Disj l r -> Obligations [before <> [l] <> after |- cqts,
                             before <> [r] <> after |- cqts]
    Neg b -> Obligations [before <> after |- cqts `snoc` b]
    _ -> WrongMode -- only Impl; Atom was ruled out above
pickRule {button: LeftButton, part} (RightNG {ants, before, new, after}) =
  case new of
    Atom _ -> NoRule -- impossible, but the compiler doesn't realize that
    Impl l r -> Obligations [ants `snoc` l |- before <> [r] <> after]
    Conj l r -> Obligations [ants |- before <> [l] <> after,
                             ants |- before <> [r] <> after]
    Disj l r -> Obligations [ants |- before <> [byPart part l r] <> after]
    Neg b -> Obligations [ants `snoc` b |- before <> after]
pickRule {button: LeftButton} (LeftG {before, new: Impl l r, after, cqts}) =
  Obligations [before.group1 <> after.group1 |- l `cons` cqts.group1,
               before.group2 <> [r] <> after.group2 |- cqts.group2]
pickRule _ _ = WrongMode

-- Model is a recursive type---each sub-derivation will be a Model, not just
-- the root one. So the choice of mode only indicates the interaction state of
-- the *root* of the derivation.
data Model
  -- A derivation for which we have not yet picked a rule to apply. In this
  -- mode, clicking on a formula indicates an attempt to introduce it.
  = Assertion Sequent
  -- A derivation whose end-sequent is the conclusion of a rule.
  | Conclusion {subprfs :: Array Model, click :: Click, wconc :: Conclusion}
data Conclusion
  -- The conclusion of a rule that does not require grouping. In this mode,
  -- clicking on a formula works like in Assertion, and will probably cause us
  -- to change to a new rule.
  = ConcNG (TaggedSequent NGTag)
  -- The conclusion of a rule that *does* require grouping. In this mode,
  -- clicking on a formula toggles its grouping.
  | ConcG (TaggedSequent GTag)

init :: Model
init = Assertion $
  [] |- [((Atom "P" `Impl` Atom "Q") `Impl` Atom "P") `Impl` Atom "P"]
  {-
  [Atom "P" `Conj` (Neg (Atom "P") `Disj` Neg (Neg (Atom "Q")))]
  |- [Atom "Q"]
  -}

unitaggedConc :: Model -> Sequent
unitaggedConc (Assertion conc) = conc
unitaggedConc (Conclusion {wconc: ConcNG conc}) = unitag conc
unitaggedConc (Conclusion {wconc: ConcG conc}) = unitag conc

complete :: Model -> Boolean
complete (Assertion _) = false
complete (Conclusion {subprfs}) = all complete subprfs

-- UPDATE

data SeqSide = LHS | RHS
data NodeAction = ClickedTurnstile Click |
  ClickedForm {click :: Click, side :: SeqSide, ix :: Int}
data Action = ChildAction Int Action | NAction NodeAction

derive instance eqSeqSide :: Eq SeqSide

update :: Model -> Action -> Model
update prf (NAction nact) = updateNode prf nact
update prf@(Assertion _) _ = prf
update (Conclusion o@{subprfs}) (ChildAction ix act) =
  Conclusion o{subprfs =
    fromMaybe subprfs (modifyAt ix (flip update act) subprfs)}

updateNode :: Model -> NodeAction -> Model
updateNode prf (ClickedTurnstile {button: RightButton}) =
  Assertion (unitaggedConc prf)
updateNode prf (ClickedTurnstile click@{button: LeftButton})
  | conc@(Entails ants cqts) <- unitaggedConc prf,
    any (_ `elem` ants) cqts =
    -- TODO Find a proper new formula!!! This breaks invariant!!!
    let retag = map _{tag = SideFormNG} in
    Conclusion {subprfs: [], click,
                wconc: ConcNG (Entails (retag ants) (retag cqts))}
  | otherwise = prf
-- Necessary assumption for invariant to be preserved: ix exists on the
-- appropriate side of the end-sequent.
updateNode prf nact@(ClickedForm {click, side, ix}) = case prf of
  Assertion conc@(Entails ants cqts) ->
    let retag side' ix' p | ix' == ix, side' == side = p{tag = NewFormNG}
                          | otherwise = p{tag = SideFormNG}
        ants' = mapWithIndex (retag LHS) ants
        cqts' = mapWithIndex (retag RHS) cqts
        conc' = Entails ants' cqts'
    in fromMaybe prf (applyRule click (ConcNG conc'))
  Conclusion {wconc: wconc@(ConcNG (Entails ants cqts))} ->
    let retag side' ix' p | ix' == ix, side' == side = p{tag = NewFormNG}
                          | otherwise = p{tag = SideFormNG}
        ants' = mapWithIndex (retag LHS) ants
        cqts' = mapWithIndex (retag RHS) cqts
        conc' = Entails ants' cqts'
    in fromMaybe prf (applyRule click (ConcNG conc'))
  Conclusion {click: oclick, wconc: ConcG (Entails ants cqts)} ->
    let toggle side' ix' p | ix' == ix, side' == side = p{tag =
                             case p.tag of SideFormG1 -> SideFormG2
                                           SideFormG2 -> SideFormG1
                                           NewFormG -> NewFormG}
                           | otherwise = p
        ants' = mapWithIndex (toggle LHS) ants
        cqts' = mapWithIndex (toggle RHS) cqts
        conc' = Entails ants' cqts'
    in fromMaybe prf (applyRule oclick (ConcG conc'))

applyRule :: Click -> Conclusion -> Maybe Model
applyRule click wconc@(ConcNG conc) = case pickRule click (explodeNG conc) of
  NoRule -> Nothing
  WrongMode ->
    let Entails ants cqts = conc
        chtag p@{tag: NewFormNG} = p{tag = NewFormG}
        chtag p@{tag: SideFormNG} = p{tag = SideFormG1}
    in applyRule click (ConcG (Entails (map chtag ants) (map chtag cqts)))
  Obligations obs -> Just $
    Conclusion {subprfs: map Assertion obs, click, wconc}
applyRule click wconc@(ConcG conc) = case pickRule click (explodeG conc) of
  NoRule -> Nothing
  WrongMode ->
    let Entails ants cqts = conc
        chtag p@{tag: NewFormG} = p{tag = NewFormNG}
        chtag p = p{tag = SideFormNG}
    in applyRule click (ConcNG (Entails (map chtag ants) (map chtag cqts)))
  Obligations obs -> Just $
    Conclusion {subprfs: map Assertion obs, click, wconc}

-- VIEW

-- TODO use tags in rendering
renderDerivation :: Model -> Html Action
renderDerivation prf =
  H.div [H.classes ["derivation", guard (complete prf) "complete"]]
  case prf of
    Assertion conc -> [map NAction (renderSequent conc)]
    Conclusion {subprfs, click, wconc} -> [
      let rsp ix subprf = map (ChildAction ix) (renderDerivation subprf)
      in H.div [] (mapWithIndex rsp subprfs),
      H.hr [], map NAction (renderSequent (unitaggedConc prf))]

-- TODO inefficient!!!
intersperse :: forall a. a -> Array a -> Array a
intersperse sep arr = case uncons arr of
  Nothing -> []
  Just {head, tail: []} -> [head]
  Just {head, tail} -> [head, sep] <> intersperse sep tail

clickable :: forall act. (Button -> act) -> Html act -> Html act
clickable act body =
  H.span [H.classes ["clickable"],
    H.on "contextmenu" (const (Just (act RightButton))),
    H.onClick (const (Just (act LeftButton)))] [body]

renderSequent :: Sequent -> Html NodeAction
renderSequent seq@(Entails ants cqts) =
  H.span [] (half LHS ants <> [turnstile] <> half RHS cqts)
  where half side = intersperse (H.text ", ") <<<
          mapWithIndex (renderForm side) <<< map _.form
        turnstile = clickable (ClickedTurnstile <<< {button: _, part: Part1})
          (H.text " ⊢ ")

renderForm :: SeqSide -> Int -> Form -> Html NodeAction
renderForm side ix form =
  let p part = \b -> ClickedForm {click: {button: b, part}, side, ix}
  in case side, form of
    -- TODO right-click on the middle too...
    LHS, Conj l r -> H.span [] [
      clickable (p Part1) (ppFormH l), H.text " ∧ ",
      clickable (p Part2) (ppFormH r)]
    RHS, Disj l r -> H.span [] [
      clickable (p Part1) (ppFormH l), H.text " ∨ ",
      clickable (p Part2) (ppFormH r)]
    _, _ -> clickable (p Part1) (ppFormH form)

-- TODO precedence
ppForm :: Form -> String
ppForm p = case p of
  Atom a -> a
  Impl l r -> ppForm l <> " → " <> ppForm r
  Conj l r -> ppForm l <> " ∧ " <> ppForm r
  Disj l r -> ppForm l <> " ∨ " <> ppForm r
  Neg b -> "¬" <> ppForm b

ppFormH :: forall act. Form -> Html act
ppFormH = H.text <<< ppForm


render :: Model -> Html Action
render = renderDerivation

