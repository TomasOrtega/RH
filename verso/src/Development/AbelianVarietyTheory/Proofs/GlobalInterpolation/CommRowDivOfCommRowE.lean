import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliOps

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

/- English proof (translation)
Rewrite using `[PI.WGL.pol_apply]`. Simplify using `[rowE, LinearMap.sum_apply]`.
-/
theorem pol_eq_rowE_apply (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) R) :
    PI.WGL.pol R a b g = rowE R r n a b g := by
  rw [PI.WGL.pol_apply]
  simp [rowE, LinearMap.sum_apply]

/- English proof (translation)
Establish `h` using `PI.WGL.rowDiv_succ ℚ a b k g`. Rewrite `h` using `[pol_eq_rowE_apply]`. Rewrite using `[← h]`. Apply the tactic sequence `split_ifs <;> simp [Algebra.smul_def, mul_comm]`.
-/
theorem rowDiv_succ_smul {r n : ℕ} (a b : Fin r) (k : ℕ) (g : MvPolynomial (Fin r × Fin n) ℚ) :
    ((k : ℚ) + 1) • rowDiv ℚ a b (k + 1) g =
      rowDiv ℚ a b k (rowE ℚ r n a b g) - (if a = b then (k : ℚ) • rowDiv ℚ a b k g else 0) := by
  have h := PI.WGL.rowDiv_succ ℚ a b k g
  rw [pol_eq_rowE_apply] at h
  rw [← h]
  split_ifs <;> simp [Algebra.smul_def, mul_comm]

/- English proof (translation)
Introduce `r n T hT a b k`. Establish `hE : ∀ g, T (rowE ℚ r n a b g) = rowE ℚ r n a b (T g)` using `fun g => by`. Use `LinearMap.congr_fun (hT a b) g` as an intermediate fact. Simplify `this` using `only [Module.End.mul_apply]`. Proceed by induction on `k with`.

Consider the case `zero => intro f`. Rewrite using `[PI.WGL.rowDiv_zero, PI.WGL.rowDiv_zero]`. Consider the case `succ k ih`. Introduce `f`. Establish `hne : ((k : ℚ) + 1) ≠ 0` using `by positivity`.

Apply `smul_right_injective _ hne` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← map_smul, rowDiv_succ_smul, rowDiv_succ_smul, map_sub, ih, hE]`. Use `split_ifs`. Rewrite using `[map_smul, ih]`.

Rewrite using `[map_zero]`.
-/
theorem comm_rowDiv_of_comm_rowE : ∀ (r n : ℕ) (T : Module.End ℚ (MvPolynomial (Fin r × Fin n) ℚ)),
    (∀ a b, T * rowE ℚ r n a b = rowE ℚ r n a b * T) →
      ∀ a b k f, T (rowDiv ℚ a b k f) = rowDiv ℚ a b k (T f) := by
  intro r n T hT a b k
  have hE : ∀ g, T (rowE ℚ r n a b g) = rowE ℚ r n a b (T g) := fun g => by
    have := LinearMap.congr_fun (hT a b) g
    simpa only [Module.End.mul_apply] using this
  induction k with
  | zero => intro f; rw [PI.WGL.rowDiv_zero, PI.WGL.rowDiv_zero]
  | succ k ih =>
    intro f
    have hne : ((k : ℚ) + 1) ≠ 0 := by positivity
    apply smul_right_injective _ hne
    simp only
    rw [← map_smul, rowDiv_succ_smul, rowDiv_succ_smul, map_sub, ih, hE]
    split_ifs
    · rw [map_smul, ih]
    · rw [map_zero]

end GlobalTheory.Alc
