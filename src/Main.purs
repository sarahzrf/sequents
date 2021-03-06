module Main where

import Prelude
import Effect (Effect)
import Effect.Exception
import Text.Parsing.StringParser
import Text.Parsing.StringParser.CodePoints
import Text.Parsing.StringParser.Combinators
import Control.MonadZero
import Data.Either
import Data.Array
import Data.Maybe
import Data.Tuple
import Data.List as L
import Partial.Unsafe

import Spork.Html (Html)
import Spork.Html as H
import Spork.PureApp as PureApp
import Web.HTML
import Web.HTML.Window
import Web.HTML.Location
import Web.HTML.HTMLDocument
import Web.DOM.ParentNode
import Web.DOM.Element hiding (toParentNode)
import URI.Query as Q
import URI.Extra.QueryPairs as QP
import Text.Parsing.Parser as TP
import Text.Parsing.Parser.String as TPS

import LK as LK
import LJ as LJ
import CLL2 as CLL2
import RCLL2 as RCLL2
import Derivation as D

main :: Effect Unit
main = window >>= \win -> catchException (flip alert win <<< message) do
  loc <- location win
  params <- search loc
  q <- either (\_ -> throw "bad query string") pure
        (TP.runParser params (Q.parser <|> (mempty <$ TPS.eof)))
  QP.QueryPairs qp <- either (\_ -> throw "could not parse query string")
    pure (QP.parse pure pure q)
  let k = QP.keyFromString "system"
      mv = QP.valueToString <$> findMap (\(Tuple k' mv) ->
        if k' == k then mv else Nothing) qp
  case mv of
    Just "lk" -> unit <$
      PureApp.makeWithSelector {init: initLK, update, render} "body"
    Just "lj" -> unit <$
      PureApp.makeWithSelector {init: initLJ, update, render} "body"
    Just "cll" -> unit <$
      PureApp.makeWithSelector {init: initCLL2, update, render} "body"
    Just "rcll" -> unit <$
      PureApp.makeWithSelector {init: initRCLL2, update, render} "body"
    Just _ -> throw "unknown system"
    Nothing -> readme win

readme :: Window -> Effect Unit
readme win = do
  pnode <- toParentNode <$> document win
  mdiv <- querySelector (QuerySelector "#readme") pnode
  case mdiv of
    Just readmeDiv -> removeAttribute "hidden" readmeDiv
    Nothing -> throw "missing readme?!"

type Model form = {input :: String, prf :: D.Model form}

initLK :: Model LK.Form
initLK = {input: "", prf: D.Assertion $
    either (\_ -> unsafeCrashWith "?") identity (runParser sequentParser prop)}
  where prop = "|- ((P -> Q) -> P) -> P"

initLJ :: Model LJ.Form
initLJ = {input: "", prf: D.Assertion $
    either (\_ -> unsafeCrashWith "?") identity (runParser sequentParser prop)}
  where prop = "|- ~(P \\/ Q) -> ~P /\\ ~Q"

initCLL2 :: Model CLL2.Form
initCLL2 = {input: "", prf: D.Assertion $
    either (\_ -> unsafeCrashWith "?") identity (runParser sequentParser prop)}
  where prop = "|- !(A & B) -o !A * !B"

initRCLL2 :: Model RCLL2.Form
initRCLL2 = {input: "", prf: D.Assertion $
    either (\_ -> unsafeCrashWith "?") identity (runParser sequentParser prop)}
  where prop = "|- !(A & B) -o !A * !B"

data Action form = DerAction (D.Action form) | Input String | Submit

sequentParser :: forall form. D.Calculus form => Parser (D.Sequent form)
sequentParser = do
    seq <- D.(|-) <$> forms <*> (string "|-" *> forms)
    guard (D.okInitial seq)
    pure seq
  where forms = map L.toUnfoldable $
          skipSpaces *> (D.formParser unit `sepBy` char ',') <* skipSpaces

update :: forall form. D.Calculus form =>
  Model form -> Action form -> Model form
update mod@{prf} (DerAction dact) = mod{prf = D.update prf dact}
update mod (Input s) = mod{input = s}
update mod@{input} Submit = case runParser sequentParser input of
  Left err -> case runParser (D.formParser unit) input of
    Left _ -> mod -- TODO show error message somehow?
    Right form -> {input: "", prf: D.Assertion $ [] D.|- [form]}
  Right seq -> {input: "", prf: D.Assertion seq}

render :: forall form. D.RenderForm form => Model form -> Html (Action form)
render {input, prf} = H.div [H.id_ "main"] [
  DerAction <$> D.renderDerivation prf,
  H.br [],
  H.input [H.value input, H.onValueInput (H.always Input)],
  H.button [H.onClick submit] [H.text "New goal"]]
  where submit = H.always (const Submit)

