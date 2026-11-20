import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisApply
open NumberField
open scoped TensorProduct

namespace GlobalTheory.UnitaryStd

variable {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)

/- English proof (translation)
Rewrite using `[form_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [cx_apply, basis_repr, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, dotProduct, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_cx_coord (S : Matrix (Fin r) (Fin r) ℤ) (y z : Lat ρ g) :
    form ρ g S (cx ρ g y) z = ∑ i, ∑ j, S i j *
      ∑ α : Fin g ⊕ Fin g, (basis ρ g).repr y (i, α) * (basis ρ g).repr z (j, α) := by
  rw [form_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [cx_apply, basis_repr, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, dotProduct,
    Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  ring

/- English proof (translation)
Rewrite using `[form_cx_coord]`. Take `⟨i0, a⟩` from `p`. Take `⟨j0, b⟩` from `q`. Simplify using `only [Module.Basis.repr_self, Finsupp.single_apply, Prod.mk.injEq]`. Simplify using `[ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]`.
-/
theorem form_cx_basis (S : Matrix (Fin r) (Fin r) ℤ) (p q : Fin r × (Fin g ⊕ Fin g)) :
    form ρ g S (cx ρ g (basis ρ g p)) (basis ρ g q) = if p.2 = q.2 then S p.1 q.1 else 0 := by
  rw [form_cx_coord]
  obtain ⟨i0, a⟩ := p
  obtain ⟨j0, b⟩ := q
  simp only [Module.Basis.repr_self, Finsupp.single_apply, Prod.mk.injEq]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

/- English proof (translation)
Use `set b := Algebra.TensorProduct.basis ℝ (basis ρ g) with hb`. Use `set c := b.repr x with hc`. Establish `hx' : x = ∑ p, c p • b p` using `(b.sum_repr x).symm`. Establish `key : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x = ∑ q, ∑ p, c p * c q * (((if p.2 = q.2 then S p.1 q.1 else 0 : ℤ)) : ℝ)` using `by conv_lhs => rw [hx']`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb, Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, form_cx_basis, mul_one, zsmul_eq_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `set v : (Fin g ⊕ Fin g) → Fin r → ℝ := fun α i => c (i, α) with hv`. Establish `key2 : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x = ∑ α, v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α))`. Rewrite using `[key, Finset.sum_comm]`.

Simplify using `only [Fintype.sum_prod_type, Int.cast_ite, Int.cast_zero, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, hv]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key2]`.

Establish `hnn : ∀ α, 0 ≤ v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α))`. Introduce `α`. Distinguish the cases in `h0 : v α = 0`. Simplify using `[h0]`. Simplify using `using (hS.dotProduct_mulVec_pos h0).le`.

Establish `hne : c ≠ 0`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hx']`. Simplify using `[h]`.

Choose the witnesses or unpack the hypotheses as in `⟨⟨i, α⟩, hp⟩ : ∃ p, c p ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (Finsupp.ext h)`. Establish `hα : v α ≠ 0` using `fun h => hp (by simpa [hv] using congrFun h i)`.

Establish `hpos : 0 < v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α))`. Simplify using `using hS.dotProduct_mulVec_pos hα`. Conclude with `lt_of_lt_of_le hpos (Finset.single_le_sum (fun β _ => hnn β) (Finset.mem_univ α))`.
-/
theorem form_cx_baseChange_pos (S : Matrix (Fin r) (Fin r) ℤ) (hS : (S.map (Int.cast : ℤ → ℝ)).PosDef)
    (x : ℝ ⊗[ℤ] Lat ρ g) (hx : x ≠ 0) :
    0 < (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x := by
  set b := Algebra.TensorProduct.basis ℝ (basis ρ g) with hb
  set c := b.repr x with hc
  have hx' : x = ∑ p, c p • b p := (b.sum_repr x).symm
  have key : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x =
      ∑ q, ∑ p, c p * c q * (((if p.2 = q.2 then S p.1 q.1 else 0 : ℤ)) : ℝ) := by
    conv_lhs => rw [hx']
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb,
      Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
      form_cx_basis, mul_one, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  set v : (Fin g ⊕ Fin g) → Fin r → ℝ := fun α i => c (i, α) with hv
  have key2 : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x =
      ∑ α, v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    rw [key, Finset.sum_comm]
    simp only [Fintype.sum_prod_type, Int.cast_ite, Int.cast_zero, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, dotProduct, Matrix.mulVec,
      Matrix.map_apply, Finset.mul_sum, hv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key2]
  have hnn : ∀ α, 0 ≤ v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    intro α
    by_cases h0 : v α = 0
    · simp [h0]
    · simpa using (hS.dotProduct_mulVec_pos h0).le
  have hne : c ≠ 0 := by
    intro h; apply hx; rw [hx']; simp [h]
  obtain ⟨⟨i, α⟩, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra h; push_neg at h; exact hne (Finsupp.ext h)
  have hα : v α ≠ 0 := fun h => hp (by simpa [hv] using congrFun h i)
  have hpos : 0 < v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    simpa using hS.dotProduct_mulVec_pos hα
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun β _ => hnn β) (Finset.mem_univ α))

end GlobalTheory.UnitaryStd
