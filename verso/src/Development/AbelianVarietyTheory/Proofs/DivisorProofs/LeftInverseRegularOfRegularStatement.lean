import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInverseRegularOfRegular
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConstLat.CramerFrame.leftInv_cramer_regular` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeftInverseRegularOfRegular.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.left_inverse_regular_of_regular : ∀ {Z : Scheme.{0}} [IsIntegral Z] {g : ℕ} (M : Matrix (Fin (g + g)) (Fin g) Z.functionField) (τ : Fin g → Fin (g + g)), (rowSel τ * M).det = 1 → leftInv M τ * M = 1 ∧ ∀ x : Z, (∀ r k, RegAt x (M r k)) → ∀ l r, RegAt x (leftInv M τ l r) := by
  first | exact @GlobalTheory.ConstLat.CramerFrame.leftInv_cramer_regular | exact GlobalTheory.ConstLat.CramerFrame.leftInv_cramer_regular | (intros; apply GlobalTheory.ConstLat.CramerFrame.leftInv_cramer_regular <;> assumption)
