module LJ where

import Prelude
import Data.Array

import Derivation
import LK as LK

newtype Form = J LK.Form

derive instance eqForm :: Eq Form

unInt :: Form -> LK.Form
unInt (J form) = form

instance ljCalculus :: Calculus Form where
  pickRule rule eseq = map J case pickRule (map unInt rule) (map unInt eseq) of
    pa@(Obligations seqs)
      | all (\(Entails _ cqts) -> length cqts <= 1) seqs -> pa
      | otherwise -> NoRule
    pa -> pa
  formParser _ = map J (formParser unit)
  equiv = (==)

instance ljRender :: RenderForm Form where
  renderForm seqix {form: J form, tag} =
    (map <<< map) J (renderForm seqix {form, tag})

