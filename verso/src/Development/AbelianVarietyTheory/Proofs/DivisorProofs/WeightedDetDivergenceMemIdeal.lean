import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiolaIdentityAdjugateDivergenceFreeStatement
open MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `K R _ _ _ ι _ _ δ δ0 I M a b w t ρ h0 hM hw hI hρ`. Use `set c : ι → R := fun i => ∑ j, M.adjugate j i * a j with hc`. Establish `hdet : δ0 M.det = ∑ i, δ i (c i)`. Apply the tactic sequence `rw [GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry δ0 M]`. Establish `hp` using `GlobalTheory.T.piola_identity_adjugate_divergence_free δ M hM`.

Establish `h1 : ∀ i, δ i (c i) = ∑ j, M.adjugate j i * δ0 (M i j) + ∑ j, a j * δ i (M.adjugate j i)`. Introduce `i`. Simplify using `only [hc, map_sum, Derivation.leibniz, smul_eq_mul, h0, Finset.sum_add_distrib]`. Establish `h2 : ∑ i, ∑ j, a j * δ i (M.adjugate j i) = 0`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, hp j, mul_zero]`. Simplify using `only [h1, Finset.sum_add_distrib, h2, add_zero]`. Establish `hadj : ∀ k, ∑ i, c i * M i k = M.det * a k`. Introduce `k`.

Establish `h3 : ∀ j, ∑ i, M.adjugate j i * M i k = if j = k then M.det else 0`. Introduce `j`. Use `congrFun (congrFun (Matrix.adjugate_mul M) j) k` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Rewrite using `[this, Matrix.smul_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hc, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations.

Use `_ = M.det * a k := by`. Simplify using `only [h3, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Establish `hrho : ∑ i, c i * (w * ∑ j, M i j * b j) = ρ * (w * M.det)`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations. Use `_ = ρ * (w * M.det) := by`. Rewrite using `[hρ, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun j _ => by rw [hadj]; ring` and prove the remaining obligations. Establish `key : δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * c i) + t * δ i ρ * (w * c i)) = - ∑ i, c i * (δ i w + t * δ i ρ * w - w * ∑ j, M i j * b j)`. Rewrite using `[Derivation.leibniz, hw, smul_zero, add_zero, smul_eq_mul, hdet, ← hrho, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * c i) + t * δ i ρ * (w * c i)) ∈ I`. Rewrite using `[key]`. Conclude with `I.neg_mem (I.sum_mem fun i _ => I.mul_mem_left _ (hI i))`.
-/
theorem weighted_det_divergence_mem_ideal : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R) (δ0 : Derivation K R R) (I : Ideal R) (M : Matrix ι ι R) (a b : ι → R) (w t ρ : R), (∀ i j, δ0 (M i j) = δ i (a j)) → (∀ h i j, δ h (M i j) = δ i (M h j)) → δ0 w = 0 → (∀ i, δ i w + t * δ i ρ * w - w * ∑ j, M i j * b j ∈ I) → ρ = ∑ j, b j * a j → δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * ∑ j, M.adjugate j i * a j) + t * δ i ρ * (w * ∑ j, M.adjugate j i * a j)) ∈ I := by
  intro K R _ _ _ ι _ _ δ δ0 I M a b w t ρ h0 hM hw hI hρ
  set c : ι → R := fun i => ∑ j, M.adjugate j i * a j with hc
  have hdet : δ0 M.det = ∑ i, δ i (c i) := by
    rw [GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry δ0 M]
    have hp := GlobalTheory.T.piola_identity_adjugate_divergence_free δ M hM
    have h1 : ∀ i, δ i (c i) = ∑ j, M.adjugate j i * δ0 (M i j) + ∑ j, a j * δ i (M.adjugate j i) := by
      intro i
      simp only [hc, map_sum, Derivation.leibniz, smul_eq_mul, h0, Finset.sum_add_distrib]
    have h2 : ∑ i, ∑ j, a j * δ i (M.adjugate j i) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.mul_sum, hp j, mul_zero]
    simp only [h1, Finset.sum_add_distrib, h2, add_zero]
  have hadj : ∀ k, ∑ i, c i * M i k = M.det * a k := by
    intro k
    have h3 : ∀ j, ∑ i, M.adjugate j i * M i k = if j = k then M.det else 0 := by
      intro j
      have := congrFun (congrFun (Matrix.adjugate_mul M) j) k
      rw [Matrix.mul_apply] at this
      rw [this, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    calc ∑ i, c i * M i k = ∑ j, a j * ∑ i, M.adjugate j i * M i k := by
          simp only [hc, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = M.det * a k := by
          simp only [h3, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
  have hrho : ∑ i, c i * (w * ∑ j, M i j * b j) = ρ * (w * M.det) := by
    calc ∑ i, c i * (w * ∑ j, M i j * b j) = ∑ j, w * b j * ∑ i, c i * M i j := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ρ * (w * M.det) := by
          rw [hρ, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by rw [hadj]; ring
  have key : δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * c i) + t * δ i ρ * (w * c i))
      = - ∑ i, c i * (δ i w + t * δ i ρ * w - w * ∑ j, M i j * b j) := by
    rw [Derivation.leibniz, hw, smul_zero, add_zero, smul_eq_mul, hdet, ← hrho, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  change δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * c i) + t * δ i ρ * (w * c i)) ∈ I
  rw [key]
  exact I.neg_mem (I.sum_mem fun i _ => I.mul_mem_left _ (hI i))

end GlobalTheory
