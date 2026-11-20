import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace PI.Residue

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [box, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left, mem_ball_zero_iff, Subtype.forall, Real.coe_toNNReal _ (hr _).le]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun w hw => ?_, fun w hw => ?_⟩` and prove the remaining obligations.

Simplify `h w` using `[normAtPlace_apply_of_isReal hw]`. Simplify `h w` using `[normAtPlace_apply_of_isComplex hw]`. Introduce and unpack `⟨h1, h2⟩ w`. Break down `isReal_or_isComplex w with hw | hw` into its components or cases. Rewrite using `[normAtPlace_apply_of_isReal hw]`.

Conclude with `h1 w hw`. Rewrite using `[normAtPlace_apply_of_isComplex hw]`. Conclude with `h2 w hw`.
-/
theorem box_eq_convexBodyLT (K : Type) [Field K] [NumberField K] (r : InfinitePlace K → ℝ)
    (hr : ∀ w, 0 < r w) : box K r = convexBodyLT K (fun w => (r w).toNNReal) := by
  ext y
  simp only [box, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_ball_zero_iff, Subtype.forall, Real.coe_toNNReal _ (hr _).le]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · simpa [normAtPlace_apply_of_isReal hw] using h w
    · simpa [normAtPlace_apply_of_isComplex hw] using h w
  · rintro ⟨h1, h2⟩ w
    rcases isReal_or_isComplex w with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]; exact h1 w hw
    · rw [normAtPlace_apply_of_isComplex hw]; exact h2 w hw

/- English proof (translation)
Introduce `K _ _ r hr`. Rewrite using `[box_eq_convexBodyLT K r hr, convexBodyLT_volume, vfac]`. Use `congr 1`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg (fun w _ => (pow_pos (hr w) _).le)]`. Use `push_cast`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_pow (hr w).le]`. Both sides reduce to the same expression.
-/
theorem boxVolume : BoxVolume := by
  intro K _ _ r hr
  rw [box_eq_convexBodyLT K r hr, convexBodyLT_volume, vfac]
  congr 1
  rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => (pow_pos (hr w) _).le)]
  push_cast
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [ENNReal.ofReal_pow (hr w).le]
  rfl

end PI.Residue
