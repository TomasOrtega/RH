import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]`. Use `split_ifs with hd`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[coeff_weightedHomogeneousComponent]`.

Use `split_ifs with hx1`. Both sides reduce to the same expression. Distinguish the cases in `h2 : coeff x.2 f = 0`. Rewrite using `[h2, mul_zero, mul_zero]`. It suffices to derive a contradiction.

Apply `hx1` to reduce the goal to its premises. Establish `hw` using `hf h2`. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite `hd` using `[← hx, map_add, hw]`. Conclude with `add_right_cancel hd`.

Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Rewrite using `[coeff_weightedHomogeneousComponent]`. Use `split_ifs with hx1`. Distinguish the cases in `h2 : coeff x.2 f = 0`. Rewrite using `[h2, mul_zero]`.

It suffices to derive a contradiction. Apply `hd` to reduce the goal to its premises. Establish `hw` using `hf h2`. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[← hx, map_add, hw, hx1]`.

Rewrite using `[zero_mul]`.
-/
theorem component_mul_multiHomog {R : Type*} [CommRing R] {K : Type} [DecidableEq K]
    {ι : K → Type} (y f : MRing ι R) (b s : K → ℕ) (hf : IsMultiHomog f s) :
    weightedHomogeneousComponent (blockWeight ι) b y * f =
      weightedHomogeneousComponent (blockWeight ι) (b + s) (y * f) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx1
    · rfl
    · by_cases h2 : coeff x.2 f = 0
      · rw [h2, mul_zero, mul_zero]
      · exfalso
        apply hx1
        have hw := hf h2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [← hx, map_add, hw] at hd
        exact add_right_cancel hd
  · refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx1
    · by_cases h2 : coeff x.2 f = 0
      · rw [h2, mul_zero]
      · exfalso
        apply hd
        have hw := hf h2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [← hx, map_add, hw, hx1]
    · rw [zero_mul]

/- English proof (translation)
Introduce `R _ K _ ι I f s hI hf y hy b`. Rewrite `hy`, the goal using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Rewrite using `[component_mul_multiHomog y f b s hf]`. Conclude with `hI _ hy _`.
-/
theorem ColonMultiHomog.proof : ColonMultiHomog.Statement := by
  intro R _ K _ ι I f s hI hf y hy b
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy ⊢
  rw [component_mul_multiHomog y f b s hf]
  exact hI _ hy _

end GroundTheory.Heights₂.Heights.NumbersDVR
