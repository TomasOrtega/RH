import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistHeightIntegralDecomposition
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FTwistHeightIntegralDecomposition.lean&line=198#L198)
-/
theorem _root_.GlobalTheory.T.twist_height_integral_decomposition : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L' : Fin e → HermLine (Tb ι)) (A' : HermLine (Tb ι)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (v : Fin 2 → ℂ), p ≠ 0 → IsArithVar Q (e + 1) → IsArithVar (twist p Q) (e + 1) → IsGoodProj (twist p Q) Ψ → (∀ j, IsSmoothHerm (L' j)) → IsSmoothHerm A' → IsSectionOn (twist p Q) A' (inc s) → (v = vPlus p ∨ v = vMinus p) → (∀ j, ∀ z ∈ mcPts Q, (L' j).h (glue z v) = (L j).h z) → (∀ z ∈ mcPts Q, A'.h (glue z v) = A.h z) → ∀ᵐ y, ∀ w, sheetDensity (twist p Q) Ψ (pot L') (logNorm A' (inc s)) y (embL v w) = sheetDensity Q (pj v Ψ) (pot L) (logNorm A s) y w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist <;> assumption)
