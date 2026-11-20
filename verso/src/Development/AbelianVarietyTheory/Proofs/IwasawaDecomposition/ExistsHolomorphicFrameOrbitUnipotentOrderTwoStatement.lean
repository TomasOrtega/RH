import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitUnipotentOrderTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsHolomorphicFrameOrbitUnipotentOrderTwo.lean&line=309#L309)
-/
theorem _root_.GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ∃ (M' : ℕ) (γ' : GL (Fin N) E), IsOrbit X T M' γ' x ∧ ((γ' : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 := by
  first | exact @GlobalTheory.ShFam.OrbitUnip.exists_isOrbit_unipotent | exact GlobalTheory.ShFam.OrbitUnip.exists_isOrbit_unipotent | (intros; apply GlobalTheory.ShFam.OrbitUnip.exists_isOrbit_unipotent <;> assumption)
