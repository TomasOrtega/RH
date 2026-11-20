import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponents
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FSystemWeightsEqShiftedCharacterExponents.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.systemWeights_eq_shifted_character_exponents : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m), (sysS H X std).Lv.comp (j + 1) → FillAt (hT := hT) (H := H) (X := X) std j hj) := by
  first | exact @GlobalTheory.TwV.Xc.fillAt_of_comp | exact GlobalTheory.TwV.Xc.fillAt_of_comp | (intros; apply GlobalTheory.TwV.Xc.fillAt_of_comp <;> assumption)
