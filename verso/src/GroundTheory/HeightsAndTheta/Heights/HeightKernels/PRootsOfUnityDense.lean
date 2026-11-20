import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RootsOfUnityDenseAlt

open Complex

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components.
-/
theorem rootsOfUnity_infinite :
    {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1}.Infinite := by
  have hprim : ∀ m : ℕ,
      IsPrimitiveRoot (exp (2 * Real.pi * I / ((m + 1 : ℕ) : ℂ))) (m + 1) :=
    fun m => Complex.isPrimitiveRoot_exp (m + 1) (Nat.succ_ne_zero m)
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => exp (2 * Real.pi * I / ((m + 1 : ℕ) : ℂ))) ?_ ?_
  · intro a b hab
    have ha := hprim a
    have hb := hprim b
    simp only at hab
    rw [hab] at ha
    have := IsPrimitiveRoot.unique ha hb
    omega
  · intro m
    exact ⟨m + 1, Nat.succ_pos m, (hprim m).pow_eq_one⟩

end RootsOfUnityDenseAlt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem RootsOfUnityDense.proof : RootsOfUnityDense.Statement := by
  intro n P hP
  refine MvPolynomial.funext_set (p := P) (q := 0)
    (fun _ => {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1})
    (fun _ => RootsOfUnityDenseAlt.rootsOfUnity_infinite) ?_
  intro x hx
  rw [map_zero]
  exact hP x fun i => hx i (Set.mem_univ i)

end GroundTheory.Heights₂.Heights
