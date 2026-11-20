import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealSpanPrimeVariableBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.BK.exists_residue_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIdealSpanPrimeVariableBasis.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.ideal_span_prime_variable_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (ι : Type) (b : ι → Ainf l) (i₀ : ι), b i₀ = 1 ∧ (∀ x : Ainf l, ∃ a : ι →₀ bk.S, x - a.sum (fun i y => bk.ev y * b i) ∈ (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) ∧ ∀ a : ι →₀ bk.S, a.sum (fun i y => bk.ev y * b i) ∈ (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev → ∀ i, a i ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  first | exact @GlobalTheory.BSP.BK.exists_residue_basis | exact GlobalTheory.BSP.BK.exists_residue_basis | (intros; apply GlobalTheory.BSP.BK.exists_residue_basis <;> assumption)
