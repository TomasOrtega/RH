import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDim
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LieDim.dim_eq_length` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLieBasisCardEqDim.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.lie_basis_card_eq_dim : ∀ (K : Type) [Field K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (n : ℕ) (v : Fin n → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR K ⟶ P.A)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v → P.g = n := by
  first | exact @GlobalTheory.LieDim.dim_eq_length | exact GlobalTheory.LieDim.dim_eq_length | (intros; apply GlobalTheory.LieDim.dim_eq_length <;> assumption)
