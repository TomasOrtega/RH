import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrictlyConcavePolFanConeRealForms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolCell.strictWith_real` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FStrictlyConcavePolFanConeRealForms.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.strictlyConcave_polFan_cone_real_forms : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → IsCone (id : ℤ → ℤ) φ u → StrictWith (id : ℤ → ℤ) φ N (linW w) u → (∀ B ∈ rcone u, (N : ℝ) * evalR φ B = evalW w B) ∧ ∀ B ∈ psdCone (id : ℤ → ℤ) X, (N : ℝ) * evalR φ B ≤ evalW w B ∧ ((N : ℝ) * evalR φ B = evalW w B → B ∈ rcone u) := by
  first | exact @GlobalTheory.PolCell.strictWith_real | exact GlobalTheory.PolCell.strictWith_real | (intros; apply GlobalTheory.PolCell.strictWith_real <;> assumption)
