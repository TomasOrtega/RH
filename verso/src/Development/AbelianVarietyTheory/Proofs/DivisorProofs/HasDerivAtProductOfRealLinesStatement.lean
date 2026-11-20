import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtProductOfRealLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompFinEqZeroOfAt
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThK.DiagDeriv.hasDerivAt_prod_ofFn` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasDerivAtProductOfRealLines.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.has_deriv_at_product_of_real_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (k : ℕ) (δ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (δ i)) →
    ∀ f : GAd σ J → ℂ, IsSm σ J f → ∀ g,
      HasDerivAt (fun t : ℝ => f (g * (List.ofFn fun i => δ i t).prod)) (∑ i, lineDer (δ i) f g) 0 := by
  first | exact @GlobalTheory.ThK.DiagDeriv.hasDerivAt_prod_ofFn | exact GlobalTheory.ThK.DiagDeriv.hasDerivAt_prod_ofFn | (intros; apply GlobalTheory.ThK.DiagDeriv.hasDerivAt_prod_ofFn <;> assumption)
