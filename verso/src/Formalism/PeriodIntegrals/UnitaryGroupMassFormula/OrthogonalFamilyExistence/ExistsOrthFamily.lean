import Mathlib
import Formalism.PeriodIntegrals.NormGramAtOrigin

noncomputable section

namespace PI.NormGramAtOrigin.UnitaryGroupMassFormula

open Matrix

section Lemmas

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

/- English proof (translation)
Unfold `hform`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.
-/
theorem hform_eq (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform (starRingEnd E) J x y = ∑ j, (∑ i, starRingEnd E (x i) * J i j) * y j := by
  unfold hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[← Matrix.exists_vecMul_eq_zero_iff]`. Use `⟨fun i => starRingEnd E (y i), ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hy` to reduce the goal to its premises. Use extensionality with `i`. Establish `h1` using `congrFun h i`. Simplify using `using h1`.

Use extensionality with `j`. Establish `h1` using `hcon (Pi.single j 1)`. Rewrite `h1` using `[hform_eq]`. Simplify `h1` using `[Matrix.vecMul, dotProduct, Pi.single_apply]`.
-/
theorem exists_pair (J : Matrix (Fin n) (Fin n) E) (hdet : J.det ≠ 0) (y : Fin n → E)
    (hy : y ≠ 0) : ∃ z, hform (starRingEnd E) J y z ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hdet
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨fun i => starRingEnd E (y i), ?_, ?_⟩
  · intro h
    apply hy
    ext i
    have h1 := congrFun h i
    simpa using h1
  · ext j
    have h1 := hcon (Pi.single j 1)
    rw [hform_eq] at h1
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using h1

end Lemmas

end PI.NormGramAtOrigin.UnitaryGroupMassFormula
