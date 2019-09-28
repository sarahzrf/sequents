module Main where

import Prelude
import Effect (Effect)
import Text.Parsing.StringParser
import Data.Either

import Spork.Html (Html)
import Spork.Html as H
import Spork.PureApp as PureApp

import Derivation (Form(..))
import Derivation as D

main :: Effect Unit
main = unit <$ PureApp.makeWithSelector app "body"
  where app = {init, update, render}

type Model = {input :: String, prf :: D.Model}

init :: Model
init = {input: "", prf: D.Assertion $
    [] D.|- []}
  -- [] D.|- [((Atom "P" `Impl` Atom "Q") `Impl` Atom "P") `Impl` Atom "P"]}
  {-
  [Atom "P" `Conj` (Neg (Atom "P") `Disj` Neg (Neg (Atom "Q")))]
  D.|- [Atom "Q"]
  -}

data Action = DerAction D.Action | Input String | Submit

update :: Model -> Action -> Model
update mod@{prf} (DerAction dact) = mod{prf = D.update prf dact}
update mod (Input s) = mod{input = s}
update mod@{input} Submit = case runParser D.sequentParser input of
  Left err -> case runParser (D.formParser unit) input of
    Left _ -> mod -- TODO show error message somehow?
    Right form -> {input: "", prf: D.Assertion $ [] D.|- [form]}
  Right seq -> {input: "", prf: D.Assertion seq}

render :: Model -> Html Action
render {input, prf} = H.div [H.id_ "main"] [
  DerAction <$> D.renderDerivation prf,
  H.br [],
  H.input [H.value input, H.onValueInput (H.always Input)],
  H.button [H.onClick submit] [H.text "New goal"]]
  where submit = H.always (const Submit)

