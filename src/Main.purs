module Main where

import Prelude
import Data.Array hiding (init)
import Data.Maybe
import Data.Monoid
import Data.Tuple

import Effect (Effect)
import Spork.Html (Html)
import Spork.Html as H
import Spork.PureApp as PureApp

main :: Effect Unit
main = void $ PureApp.makeWithSelector app "body"
  where app = {init, update, render}


-- MODEL

data Prop = Atom String | Conj Prop Prop | Disj Prop Prop | Neg Prop
type Props = Array Prop
data Sequent = Entails Props Props
data Proof = Assertion Sequent | Justification (Array Proof) Sequent
type Model = Proof

derive instance eqProp :: Eq Prop

infix 4 Entails as |-

init :: Model
init = Assertion $
  [Atom "P" `Conj` (Neg (Atom "P") `Disj` Neg (Neg (Atom "Q")))] |- [Atom "Q"]

endSeq :: Proof -> Sequent
endSeq (Assertion end) = end
endSeq (Justification _ end) = end

complete :: Proof -> Boolean
complete (Assertion _) = false
complete (Justification subprfs _) = all complete subprfs

data Side = LHS | RHS
data SeqFocused foc = SF {
  side :: Side,
  before :: Props, foc :: foc, after :: Props,
  oside :: Props}

derive instance functorSequentFocused :: Functor SeqFocused

reassemble :: SeqFocused Props -> Sequent
reassemble (SF {side, before, foc, after, oside}) = case side of
  LHS -> before <> foc <> after |- oside
  RHS -> oside |- before <> foc <> after

-- TODO inefficient!!!
focuses :: Sequent -> Tuple (Array (SeqFocused Prop)) (Array (SeqFocused Prop))
focuses (Entails ants sucs) = Tuple (half LHS sucs ants) (half RHS ants sucs)
  where half side oside =
          let go before rest = case uncons rest of
                Nothing -> []
                Just {head, tail} ->
                  SF {side, before, foc: head, after: tail, oside} :
                  go (snoc before head) tail
          in go []


-- UPDATE

data NodeAction = ClearAbove | Obligations (Array Sequent)
data Action = ChildAction Int Action | NAction NodeAction

updateNode :: Model -> NodeAction -> Model
updateNode prf ClearAbove = Assertion (endSeq prf)
updateNode prf (Obligations prems) =
  Justification (map Assertion prems) (endSeq prf)

update :: Model -> Action -> Model
update prf (NAction nact) = updateNode prf nact
update prf@(Assertion _) (ChildAction _ _) = prf
update (Justification subprfs end) (ChildAction ix act) =
  Justification (fromMaybe subprfs (modifyAt ix (flip update act) subprfs)) end


-- VIEW

renderDerivation :: Proof -> Html Action
renderDerivation prf =
  H.div [H.classes ["derivation", guard (complete prf) "complete"]]
  case prf of
    Assertion end -> [map NAction (renderSequent end)]
    Justification subprfs end -> [
      let rsp ix subprf = map (ChildAction ix) (renderDerivation subprf)
      in H.div [] (mapWithIndex rsp subprfs),
      H.hr [], map NAction (renderSequent end)]

-- TODO inefficient!!!
intersperse :: forall a. a -> Array a -> Array a
intersperse sep arr = case uncons arr of
  Nothing -> []
  Just {head, tail: []} -> [head]
  Just {head, tail} -> [head, sep] <> intersperse sep tail

clickable :: forall act. act -> Html act -> Html act
clickable act body =
  H.span [H.classes ["clickable"], H.onClick (const (Just act))] [body]

rclickable :: forall act. act -> Html act -> Html act
rclickable act body = H.span [H.on "contextmenu" (const (Just act))] [body]

renderSequent :: Sequent -> Html NodeAction
renderSequent seq@(Entails ants sucs) =
    H.span [] (half focsL <> [vdashActs (H.text " ⊢ ")] <> half focsR)
  where Tuple focsL focsR = focuses seq
        half = intersperse (H.text ", ") <<<
          map (map (Obligations <<< map reassemble) <<< renderProp)
        vdashActs = rclickable ClearAbove <<<
          if any (_ `elem` ants) sucs
            then clickable (Obligations []) else identity

-- interacting with this node can produce an array of obligations, with each
-- obligation in focused form
renderProp :: SeqFocused Prop -> Html (Array (SeqFocused Props))
renderProp sf@(SF {side, foc}) =
  rclickable [[foc, foc] <$ sf] case side, foc of
    _, Atom _ -> H.span [] [ppPropH foc]
    LHS, Conj l r -> H.span [] [
      clickable [[l] <$ sf] (ppPropH l), H.text " ∧ ",
      clickable [[r] <$ sf] (ppPropH r)]
    RHS, Disj l r -> H.span [] [
      clickable [[l] <$ sf] (ppPropH l), H.text " ∨ ",
      clickable [[r] <$ sf] (ppPropH r)]
    LHS, Disj l r -> clickable [[l] <$ sf, [r] <$ sf] (ppPropH foc)
    RHS, Conj l r -> clickable [[l] <$ sf, [r] <$ sf] (ppPropH foc)
    _, Neg b -> let SF c = [] <$ sf
                in clickable [SF c{oside = c.oside `snoc` b}] (ppPropH foc)

-- TODO precedence
ppProp :: Prop -> String
ppProp p = case p of
  Atom a -> a
  Conj l r -> ppProp l <> " ∧ " <> ppProp r
  Disj l r -> ppProp l <> " ∨ " <> ppProp r
  Neg b -> "¬" <> ppProp b

ppPropH :: forall act. Prop -> Html act
ppPropH = H.text <<< ppProp


render :: Model -> Html Action
render = renderDerivation

