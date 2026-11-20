import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

/- English proof (translation)
Use `set M : Matrix (Fin n) (Fin n) E := (γ : GL (Fin n) E).val with hM`. Establish `h : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * 1 * M = 1` using `γ.2`. Rewrite `h` using `[Matrix.mul_one]`. Establish `hjj : ∑ k, IsCMField.complexConj E (M k j) * M k j = 1`. Use `congrFun₂ h j j` as an intermediate fact.

Simplify `this` using `[Formalism.UG.cT, Matrix.mul_apply]`. Establish `hτ : ∑ k, ((Complex.normSq (τ (M k j)) : ℝ) : ℂ) = 1`. Use `congrArg τ hjj` as an intermediate fact. Rewrite `this` using `[map_sum, map_one]`. Rewrite using `[← this]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, IsCMField.complexEmbedding_complexConj, Complex.normSq_eq_conj_mul_self]`. Establish `hR : ∑ k, Complex.normSq (τ (M k j)) = 1` using `by exact_mod_cast hτ`. Establish `hle : Complex.normSq (τ (M i j)) ≤ 1`. Rewrite using `[← hR]`.

Conclude with `Finset.single_le_sum (f := fun k => Complex.normSq (τ (M k j))) (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)`. Establish `hsq : ‖τ (M i j)‖ ^ 2 ≤ 1` using `by rw [Complex.sq_norm]; exact hle`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq`.
-/
theorem norm_emb_entry_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n)
    (τ : E →+* ℂ) (i j : Fin n) : ‖τ ((γ : GL (Fin n) E).val i j)‖ ≤ 1 := by
  set M : Matrix (Fin n) (Fin n) E := (γ : GL (Fin n) E).val with hM
  have h : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * 1 * M = 1 := γ.2
  rw [Matrix.mul_one] at h
  have hjj : ∑ k, IsCMField.complexConj E (M k j) * M k j = 1 := by
    have := congrFun₂ h j j
    simpa [Formalism.UG.cT, Matrix.mul_apply] using this
  have hτ : ∑ k, ((Complex.normSq (τ (M k j)) : ℝ) : ℂ) = 1 := by
    have := congrArg τ hjj
    rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, IsCMField.complexEmbedding_complexConj, Complex.normSq_eq_conj_mul_self]
  have hR : ∑ k, Complex.normSq (τ (M k j)) = 1 := by exact_mod_cast hτ
  have hle : Complex.normSq (τ (M i j)) ≤ 1 := by
    rw [← hR]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (τ (M k j))) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i)
  have hsq : ‖τ (M i j)‖ ^ 2 ≤ 1 := by rw [Complex.sq_norm]; exact hle
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

end GlobalTheory.BCT.FinPart
