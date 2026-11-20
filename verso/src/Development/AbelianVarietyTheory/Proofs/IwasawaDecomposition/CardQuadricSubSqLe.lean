import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.QuadricCount

/- English proof (translation)
Use `split_ifs with hw`. Substitute `hw` using the available equality. Simplify using the standard rewrite rules. Take `⟨i, hi⟩` from `Function.ne_iff.mp hw`. Establish `hi' : w i ≠ 0` using `hi`.

Establish `h1 : ∃ a : k, ψ (a * w i) ≠ 1`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `AddChar.sum_mulShift (w i) hψ` as an intermediate fact. Simplify using `[hcon, hi'] at this`.

Take `⟨a, ha⟩` from `h1`. Establish `h2 : ∑ x : ι → k, ψ (x ⬝ᵥ w) = ψ (a * w i) * ∑ x : ι → k, ψ (x ⬝ᵥ w)`. Rewrite using `[Finset.mul_sum]`. Rewrite using `[← Equiv.sum_comp (Equiv.addLeft (Pi.single i a : ι → k))]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Simplify using `[add_dotProduct, AddChar.map_add_eq_mul]`. Establish `h3 : (1 - ψ (a * w i)) * ∑ x : ι → k, ψ (x ⬝ᵥ w) = 0`. Take the linear combination `h2`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h).symm ha`.

Conclude with `h`.
-/
lemma sum_dot {k : Type} [Field k] [Fintype k] [DecidableEq k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ.IsPrimitive) (w : ι → k) :
    ∑ x : ι → k, ψ (x ⬝ᵥ w) = if w = 0 then ((Fintype.card k : ℂ) ^ Fintype.card ι) else 0 := by
  split_ifs with hw
  · subst hw; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have hi' : w i ≠ 0 := hi
    have h1 : ∃ a : k, ψ (a * w i) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have := AddChar.sum_mulShift (w i) hψ
      simp [hcon, hi'] at this
    obtain ⟨a, ha⟩ := h1
    have h2 : ∑ x : ι → k, ψ (x ⬝ᵥ w) = ψ (a * w i) * ∑ x : ι → k, ψ (x ⬝ᵥ w) := by
      rw [Finset.mul_sum]
      rw [← Equiv.sum_comp (Equiv.addLeft (Pi.single i a : ι → k))]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [add_dotProduct, AddChar.map_add_eq_mul]
    have h3 : (1 - ψ (a * w i)) * ∑ x : ι → k, ψ (x ⬝ᵥ w) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h).symm ha
    · exact h

/- English proof (translation)
Establish `hsym : ∀ x z : ι → k, z ⬝ᵥ S.mulVec x = x ⬝ᵥ S.mulVec z`. Introduce `x z`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS.eq, dotProduct_comm]`. Establish `key : (starRingEnd ℂ) (∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))) * (∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))) = (Fintype.card k : ℂ) ^ Fintype.card ι`. Rewrite using `[map_sum, Finset.sum_mul]`.

Establish `e1 : ∀ x : ι → k, (starRingEnd ℂ) (ψ (t * (x ⬝ᵥ S.mulVec x))) * (∑ y : ι → k, ψ (t * (y ⬝ᵥ S.mulVec y))) = ∑ z : ι → k, ψ (t * (z ⬝ᵥ S.mulVec z)) * ψ (x ⬝ᵥ ((2 * t) • S.mulVec z))`. Introduce `x`. Rewrite using `[Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft x)]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`.

Use `congr 1`. Simplify using `only [Equiv.coe_addLeft, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul, hsym x z]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e1]`. Rewrite using `[Finset.sum_comm]`.

Repeatedly rewrite using `[← Finset.mul_sum, sum_dot ψ hψ]`. Rewrite using `[Finset.sum_eq_single (0 : ι → k)]`. Simplify using the standard rewrite rules. Introduce `z _ hz`. Rewrite using `[if_neg, mul_zero]`.

Introduce `h`. Break down `smul_eq_zero.mp h with h | h` into its components or cases. Conclude with `mul_ne_zero h2 ht h`. Conclude with `hz (Matrix.eq_zero_of_mulVec_eq_zero hd h)`. Simplify using the standard rewrite rules.

Rewrite `key` using `[Complex.conj_mul']`. Conclude with `key` after adjusting the coercions.
-/
lemma gauss_normSq {k : Type} [Field k] [Fintype k] [DecidableEq k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ.IsPrimitive) (S : Matrix ι ι k) (h2 : (2 : k) ≠ 0) (hS : S.IsSymm)
    (hd : S.det ≠ 0) (t : k) (ht : t ≠ 0) :
    ‖∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))‖ ^ 2 = (Fintype.card k : ℝ) ^ Fintype.card ι := by
  have hsym : ∀ x z : ι → k, z ⬝ᵥ S.mulVec x = x ⬝ᵥ S.mulVec z := by
    intro x z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS.eq, dotProduct_comm]
  have key : (starRingEnd ℂ) (∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))) * (∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x)))
      = (Fintype.card k : ℂ) ^ Fintype.card ι := by
    rw [map_sum, Finset.sum_mul]
    have e1 : ∀ x : ι → k, (starRingEnd ℂ) (ψ (t * (x ⬝ᵥ S.mulVec x))) * (∑ y : ι → k, ψ (t * (y ⬝ᵥ S.mulVec y)))
        = ∑ z : ι → k, ψ (t * (z ⬝ᵥ S.mulVec z)) * ψ (x ⬝ᵥ ((2 * t) • S.mulVec z)) := by
      intro x
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft x)]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      simp only [Equiv.coe_addLeft, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul, hsym x z]
      ring
    simp_rw [e1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_dot ψ hψ]
    rw [Finset.sum_eq_single (0 : ι → k)]
    · simp
    · intro z _ hz
      rw [if_neg, mul_zero]
      intro h
      rcases smul_eq_zero.mp h with h | h
      · exact mul_ne_zero h2 ht h
      · exact hz (Matrix.eq_zero_of_mulVec_eq_zero hd h)
    · simp
  rw [Complex.conj_mul'] at key
  exact_mod_cast key

/- English proof (translation)
Introduce `k _ _ _ ι _ _ _ S β h2 hS hd`. Use `set ψ := AddChar.FiniteField.primitiveChar_to_Complex k`. Establish `hψ : ψ.IsPrimitive` using `AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive k`. Use `set N := (Finset.univ.filter fun x : ι → k => x ⬝ᵥ S.mulVec x = β).card with hN`. Use `set q := Fintype.card k with hq`.

Use `set m := Fintype.card ι with hm`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast Fintype.card_pos`. Establish `hm0 : m = (m - 1) + 1` using `by have : 0 < m := Fintype.card_pos; omega`. Establish `e1 : ∑ x : ι → k, ∑ t : k, ψ (t * (x ⬝ᵥ S.mulVec x - β)) = (q : ℂ) * N`. Repeatedly rewrite using `[AddChar.sum_mulShift _ hψ, sub_eq_zero]`.

Use `push_cast`. Rewrite using `[← Finset.sum_filter]`. Simplify using `[hN, hq, mul_comm]`. Rewrite `e1` using `[Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]`. Establish `e2 : ∑ x : ι → k, ψ (0 * (x ⬝ᵥ S.mulVec x - β)) = (q : ℂ) ^ m`.

Simplify using `[hq, hm]`. Rewrite `e1` using `[e2]`. Use `set r : ℝ := Real.sqrt ((q : ℝ) ^ m) with hr`. Establish `hr0 : 0 ≤ r` using `Real.sqrt_nonneg _`. Establish `hr2 : r ^ 2 = (q : ℝ) ^ m` using `Real.sq_sqrt (by positivity)`.

Establish `e3 : ∀ t ∈ Finset.univ.erase (0 : k), ‖∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x - β))‖ ≤ r`. Introduce `t ht`. Establish `ht0 : t ≠ 0` using `(Finset.mem_erase.mp ht).1`. Establish `: ∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x - β)) = ψ (-(t * β)) * ∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← AddChar.map_add_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, norm_mul, AddChar.norm_apply, one_mul, hr, ← gauss_normSq ψ hψ S h2 hS hd t ht0, Real.sqrt_sq (norm_nonneg _)]`.

Establish `e4 : ‖(q : ℂ) * N - (q : ℂ) ^ m‖ ≤ q * r`. Rewrite using `[← e1, add_sub_cancel_left]`. Use `(norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ e3).trans ?_)` and prove the remaining obligations. Rewrite using `[nsmul_eq_mul]`. Use `gcongr`.

Conclude with `Finset.card_le_univ _`. Establish `e5 : (q : ℂ) * N - (q : ℂ) ^ m = (((q : ℝ) * ((N : ℝ) - (q : ℝ) ^ (m - 1)) : ℝ) : ℂ)` using `by conv_lhs => rw [hm0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e4` using `[e5, Complex.norm_real, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq0]`.

Establish `e6` using `le_of_mul_le_mul_left e4 hq0`. Rewrite using `[← hr2, ← sq_abs]`. Use `gcongr`.
-/
theorem card_quadric_sub_sq_le : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (S : Matrix ι ι k) (β : k), (2 : k) ≠ 0 → S.IsSymm → S.det ≠ 0 → (((Finset.univ.filter fun x : ι → k => x ⬝ᵥ S.mulVec x = β).card : ℝ) - (Fintype.card k : ℝ) ^ (Fintype.card ι - 1)) ^ 2 ≤ (Fintype.card k : ℝ) ^ Fintype.card ι := by
  intro k _ _ _ ι _ _ _ S β h2 hS hd
  set ψ := AddChar.FiniteField.primitiveChar_to_Complex k
  have hψ : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive k
  set N := (Finset.univ.filter fun x : ι → k => x ⬝ᵥ S.mulVec x = β).card with hN
  set q := Fintype.card k with hq
  set m := Fintype.card ι with hm
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hm0 : m = (m - 1) + 1 := by have : 0 < m := Fintype.card_pos; omega
  have e1 : ∑ x : ι → k, ∑ t : k, ψ (t * (x ⬝ᵥ S.mulVec x - β)) = (q : ℂ) * N := by
    simp_rw [AddChar.sum_mulShift _ hψ, sub_eq_zero]
    push_cast
    rw [← Finset.sum_filter]
    simp [hN, hq, mul_comm]
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))] at e1
  have e2 : ∑ x : ι → k, ψ (0 * (x ⬝ᵥ S.mulVec x - β)) = (q : ℂ) ^ m := by
    simp [hq, hm]
  rw [e2] at e1
  set r : ℝ := Real.sqrt ((q : ℝ) ^ m) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (q : ℝ) ^ m := Real.sq_sqrt (by positivity)
  have e3 : ∀ t ∈ Finset.univ.erase (0 : k), ‖∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x - β))‖ ≤ r := by
    intro t ht
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
    have : ∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x - β)) = ψ (-(t * β)) * ∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [this, norm_mul, AddChar.norm_apply, one_mul, hr, ← gauss_normSq ψ hψ S h2 hS hd t ht0, Real.sqrt_sq (norm_nonneg _)]
  have e4 : ‖(q : ℂ) * N - (q : ℂ) ^ m‖ ≤ q * r := by
    rw [← e1, add_sub_cancel_left]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ e3).trans ?_)
    rw [nsmul_eq_mul]
    gcongr
    exact Finset.card_le_univ _
  have e5 : (q : ℂ) * N - (q : ℂ) ^ m = (((q : ℝ) * ((N : ℝ) - (q : ℝ) ^ (m - 1)) : ℝ) : ℂ) := by
    conv_lhs => rw [hm0]
    push_cast
    ring
  rw [e5, Complex.norm_real, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq0] at e4
  have e6 := le_of_mul_le_mul_left e4 hq0
  rw [← hr2, ← sq_abs]
  gcongr

end GlobalTheory.QuadricCount
