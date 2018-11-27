module Main where

import Prelude
import Data.Array hiding (init)
import Data.Maybe

import Effect (Effect)
import Spork.Html (Html)
import Spork.Html as H
import Spork.PureApp as PureApp

main :: Effect Unit
main = void $ PureApp.makeWithSelector app "body"
  where app = {init, update, render}


-- MODEL

data Prop = Atom String | Conj Prop Prop | Disj Prop Prop | Neg Prop
data Sequent = Entails (Array Prop) (Array Prop)
data Proof = Assertion Sequent | Justification (Array Proof) Sequent

derive instance eqProp :: Eq Prop

infix 4 Entails as |-

type Model = Proof

init :: Model
-- init = Assertion $ [Atom "P" `Disj` Atom "P", Atom "Q"] |- [Atom "P"]
-- init = Assertion $ [Atom "P" `Conj` Atom "Q"] |- [Atom "P" `Disj` Atom "Q"]
init = Assertion $ [Atom "P"] |- [Neg $ Neg $ Atom "P"]

endSeq :: Proof -> Sequent
endSeq (Assertion end) = end
endSeq (Justification _ end) = end


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

renderDerivation :: Model -> Html Action
renderDerivation prf = H.div [H.classes ["derivation"]] $ case prf of
  Assertion end -> [map NAction (renderSequent end)]
  Justification subprfs end -> [
    let rsp ix subprf = map (ChildAction ix) (renderDerivation subprf)
    in H.div [] (mapWithIndex rsp subprfs),
    H.hr [], map NAction (renderSequent end)]

mapSlices :: forall a b. (Array a -> a -> Array a -> b) -> Array a -> Array b
mapSlices f = go []
  where go before rest = case uncons rest of
          Nothing -> []
          Just {head, tail} -> f before head tail : go (snoc before head) tail

-- TODO inefficient!!!
intersperse :: forall a. a -> Array a -> Array a
intersperse sep arr = case uncons arr of
  Nothing -> []
  Just {head, tail: []} -> [head]
  Just {head, tail} -> [head, sep] <> intersperse sep tail

clickable :: forall act. act -> Html act -> Html act
clickable act body =
  H.span [H.classes ["clickable"], H.onClick (const (Just act))] [body]

renderSequent :: Sequent -> Html NodeAction
renderSequent (Entails ants sucs) = H.span [] $ concat [
    side (renderAnt sucs) ants,
    [clickable vdashAct (H.text " ⊢ ")],
    side (renderSuc ants) sucs]
  where side f ps = intersperse (H.text ", ") (mapSlices f ps)
        vdashAct = if any (_ `elem` ants) sucs
                   then Obligations [] else ClearAbove

renderAnt :: Array Prop -> Array Prop -> Prop -> Array Prop -> Html NodeAction
renderAnt sucs before p after = case p of
  Atom a -> H.span [] [H.text a]
  Conj l r -> let obsl = [before <> [l] <> after |- sucs]
                  obsr = [before <> [r] <> after |- sucs]
              in H.span [] [
                clickable (Obligations obsl) (renderProp l), H.text " ∧ ",
                clickable (Obligations obsr) (renderProp r)]
  Disj l r -> let obs = [before <> [l] <> after |- sucs,
                         before <> [r] <> after |- sucs]
              in clickable (Obligations obs) (renderProp p)
  Neg b -> let obs = [before <> after |- sucs `snoc` b]
           in clickable (Obligations obs) (renderProp p)

renderSuc :: Array Prop -> Array Prop -> Prop -> Array Prop -> Html NodeAction
renderSuc ants before p after = case p of
  Atom a -> H.span [] [H.text a]
  Conj l r -> let obs = [ants |- before <> [l] <> after,
                         ants |- before <> [r] <> after]
              in clickable (Obligations obs) (renderProp p)
  Disj l r -> let obsl = [ants |- before <> [l] <> after]
                  obsr = [ants |- before <> [r] <> after]
              in H.span [] [
                clickable (Obligations obsl) (renderProp l), H.text " ∨ ",
                clickable (Obligations obsr) (renderProp r)]
  Neg b -> let obs = [ants `snoc` b |- before <> after]
           in clickable (Obligations obs) (renderProp p)

renderProp :: forall act. Prop -> Html act
renderProp = H.text <<< ppProp

-- TODO precedence
ppProp :: Prop -> String
ppProp p = case p of
  Atom a -> a
  Conj l r -> ppProp l <> " ∧ " <> ppProp r
  Disj l r -> ppProp l <> " ∨ " <> ppProp r
  Neg b -> "¬" <> ppProp b


render :: Model -> Html Action
render = renderDerivation

