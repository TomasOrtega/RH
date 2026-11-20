import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeTensorOperatorRaiseStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `M _ _ n ε E N _ _ F io pr c s y hE hF hT hc hy d`. Establish `key` using `GlobalTheory.T.compactCasimirLe_tensorOperator_raise (N s) n ε (F s) M (Fin n) E (fun j => (LinearMap.proj j : (Fin n → M) →ₗ[ℂ] M) ∘ₗ io s) (fun a b => Matrix.single a b (1 : ℂ)) c (Real.sqrt n) (isUnitary_kUnit ε _ (hF s)) (isUnitary_kUnit ε _ hE) hc (Real.sqrt_nonneg _) (by`. Introduce `a b _`. Simplify using `[Matrix.conjTranspose_single])`. Use the proof step `(by`.

Introduce `x`. Rewrite using `[Real.sq_sqrt (Nat.cast_nonneg n)]`. Establish `h1 : ∀ a b : Fin n, ∑ i, ‖∑ j, (Matrix.single a b (1 : ℂ)) i j • x j‖ ^ 2 = ‖x b‖ ^ 2`. Introduce `a b`. Rewrite using `[Finset.sum_eq_single a]`.

Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Matrix.single, hj.symm]`. Simplify using the standard rewrite rules.

Introduce `i _ hi`. Simplify using `[Matrix.single, hi.symm]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `(h1 a b).le`. Check the signs of the components of the expression. Use `_ = _ := by simp)`. Use the proof step `(by`.

Introduce `a b _ j w`. Establish `h` using `congrFun (hT.io_comm s a b w) j`. Simplify using `only [dualTens] at h`. Simplify using `only [LinearMap.comp_apply, LinearMap.proj_apply]`. Rewrite using `[h, Finset.sum_eq_single a]`.

Distinguish the cases in `hj : j = b`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj, Matrix.single, Ne.symm hj]`. Introduce `i _ hi`.

Simplify using `[Matrix.single, hi.symm]`. Use the proof step `simp)`. Use `y hy d`. Conclude with `key`.
-/
theorem casKLe_io_component : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (s : Fin n) (y : N s), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε (F s) c y → ∀ d, CasKLe ε E (c + Real.sqrt n) (io s y d) := by
  intro M _ _ n ε E N _ _ F io pr c s y hE hF hT hc hy d
  have key := GlobalTheory.T.compactCasimirLe_tensorOperator_raise (N s) n ε (F s) M (Fin n) E
    (fun j => (LinearMap.proj j : (Fin n → M) →ₗ[ℂ] M) ∘ₗ io s)
    (fun a b => Matrix.single a b (1 : ℂ)) c (Real.sqrt n)
    (isUnitary_kUnit ε _ (hF s)) (isUnitary_kUnit ε _ hE) hc (Real.sqrt_nonneg _)
    (by
      intro a b _
      simp [Matrix.conjTranspose_single])
    (by
      intro x
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      have h1 : ∀ a b : Fin n,
          ∑ i, ‖∑ j, (Matrix.single a b (1 : ℂ)) i j • x j‖ ^ 2 = ‖x b‖ ^ 2 := by
        intro a b
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single b]
          · simp
          · intro j _ hj
            simp [Matrix.single, hj.symm]
          · simp
        · intro i _ hi
          simp [Matrix.single, hi.symm]
        · simp
      calc _ ≤ ∑ _a : Fin n, ∑ b : Fin n, ‖x b‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
            split_ifs
            · exact (h1 a b).le
            · positivity
        _ = _ := by simp)
    (by
      intro a b _ j w
      have h := congrFun (hT.io_comm s a b w) j
      simp only [dualTens] at h
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [h, Finset.sum_eq_single a]
      · by_cases hj : j = b
        · subst hj
          simp
        · simp [hj, Matrix.single, Ne.symm hj]
      · intro i _ hi
        simp [Matrix.single, hi.symm]
      · simp)
    y hy d
  exact key

end GlobalTheory
