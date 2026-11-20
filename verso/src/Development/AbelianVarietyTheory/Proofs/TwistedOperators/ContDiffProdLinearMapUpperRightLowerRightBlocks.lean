import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
open MeasureTheory

namespace GlobalTheory.FockFamily

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[contDiff_clm_apply_iff]`. Introduce `q`. Simplify `(hJ (0, q)).fst` using `only [blockB_apply]`. Rewrite using `[contDiff_clm_apply_iff]`.

Introduce `q`. Simplify `(hJ (0, q)).snd` using `only [blockD_apply]`.
-/
theorem contDiff_blockB_blockD {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)) (hJ : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  constructor
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockB_apply] using (hJ (0, q)).fst
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockD_apply] using (hJ (0, q)).snd

end GlobalTheory.FockFamily
