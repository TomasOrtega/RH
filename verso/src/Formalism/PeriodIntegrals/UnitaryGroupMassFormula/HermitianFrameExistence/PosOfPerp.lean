import Mathlib
import Formalism.PeriodIntegrals.ScPiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.HJSumSmulRight

noncomputable section

open Matrix

namespace PI.ScPiFrameW

open PI.ScPiExists

variable {n : ℕ}

/- English proof (translation)
Consider the cases of `hi : ε i`. Take `⟨k, hk⟩` from `hσ i hi`. Substitute `hk` using the available equality. Simplify using `[hw0]`. Simplify using `[Complex.normSq_nonneg]`.
-/
private theorem nonneg_term_lemma (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i) (w : Fin n → ℂ) (hw0 : ∀ j, w (σ j) = 0) (i : Fin n) :
    0 ≤ (if ε i then (1 : ℝ) else -1) * Complex.normSq (w i) := by
  cases hi : ε i
  · obtain ⟨k, hk⟩ := hσ i hi
    subst hk
    simp [hw0]
  · simp [Complex.normSq_nonneg]

/- English proof (translation)
Rewrite using `[hJ_self_re]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, w i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hw (funext h)`.

Establish `hεi : ε i = true`. Consider the cases of `hj : ε i`. Take `⟨k, hk⟩` from `hσ i hj`. Conclude with `(hi (by rw [← hk]; exact hw0 k)).elim`. Both sides reduce to the same expression.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[if_pos hεi, one_mul]`. Conclude with `Complex.normSq_pos.mpr hi`. Use `_ ≤ ∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (w j) := Finset.single_le_sum (fun j _ => nonneg_term_lemma ε σ hσ w hw0 j) (Finset.mem_univ i)`.
-/
private theorem pos_of_vanish_lemma_2 (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i) (w : Fin n → ℂ) (hw0 : ∀ j, w (σ j) = 0)
    (hw : w ≠ 0) : 0 < (hJ ε w w).re := by
  rw [hJ_self_re]
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (funext h)
  have hεi : ε i = true := by
    cases hj : ε i
    · obtain ⟨k, hk⟩ := hσ i hj
      exact (hi (by rw [← hk]; exact hw0 k)).elim
    · rfl
  calc (0 : ℝ) < (if ε i then (1 : ℝ) else -1) * Complex.normSq (w i) := by
        rw [if_pos hεi, one_mul]
        exact Complex.normSq_pos.mpr hi
    _ ≤ ∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (w j) :=
        Finset.single_le_sum (fun j _ => nonneg_term_lemma ε σ hσ w hw0 j) (Finset.mem_univ i)

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `hle : (hJ ε y y).re ≤ 0` using `not_lt.mp hcon`. Take `⟨m, hm⟩ : ∃ m : Fin r ⊕ Bool → Fin n → ℂ, m = Sum.elim (fun a => e a - f a) (fun b => if b then y else z)` from `⟨_, rfl⟩`. Establish `hmi : ∀ a, m (Sum.inl a) = e a - f a` using `fun a => by rw [hm]; rfl`. Establish `hmf : m (Sum.inr false) = z` using `by rw [hm]; rfl`.

Establish `hmt : m (Sum.inr true) = y` using `by rw [hm]; rfl`. Take `⟨D, hD⟩ : ∃ D : Fin r ⊕ Bool → ℂ, D = Sum.elim (fun _ => (-2 : ℂ)) (fun b => if b then hJ ε y y else -(t : ℂ))` from `⟨_, rfl⟩`. Establish `hDi : ∀ a, D (Sum.inl a) = -2` using `fun a => by rw [hD]; rfl`. Establish `hDf : D (Sum.inr false) = -(t : ℂ)` using `by rw [hD]; rfl`. Establish `hDt : D (Sum.inr true) = hJ ε y y` using `by rw [hD]; rfl`.

Establish `hG : ∀ k l, hJ ε (m k) (m l) = if k = l then D k else 0`. Introduce `k l`. Apply the tactic sequence `rcases k with a | i <;> rcases l with b | j`. Simplify using `only [hmi, hJ_sub_left, hJ_sub_right, hee, hff, hef, hJ_conj ε (e b) (f a), hDi]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Evaluate the numerical expressions. Simplify using `[hab, Ne.symm hab]`. Apply the tactic sequence `cases j <;> simp [hmi, hmf, hmt, hJ_sub_left, hez, hfz, hey, hfy]`. Apply the tactic sequence `cases i <;> simp [hmi, hmf, hmt, hJ_sub_right, hJ_conj ε (e b) z, hJ_conj ε (f b) z, hJ_conj ε (e b) y, hJ_conj ε (f b) y, hez, hfz, hey, hfy]`.

Apply the tactic sequence `cases i <;> cases j <;> simp [hmf, hmt, hDf, hDt, hzz, hzy, hJ_conj ε z y]`. Take `⟨g, hg, k0, hk0⟩` from `exists_rel (fun k : Fin r ⊕ Bool => fun j : Fin (r + 1) => m k (σ j)) (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]; omega)`. Take `⟨v, hv⟩ : ∃ v : Fin n → ℂ, v = ∑ k, g k • m k` from `⟨_, rfl⟩`. Establish `hv0 : ∀ j, v (σ j) = 0`. Introduce `j`.

Establish `h` using `congrFun hg j`. Rewrite using `[hv]`. Simplify `h` using `[Finset.sum_apply]`. Establish `hvv : (hJ ε v v).re = ∑ k, Complex.normSq (g k) * (D k).re`. Rewrite using `[hv, hJ_sum_smul_left, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hJ_sum_smul_right]`. Simplify using `only [hG, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Conclude with `re_star_mul_mul _ _`. Establish `hterm : ∀ k, Complex.normSq (g k) * (D k).re ≤ 0`.

Introduce `k`. Use `mul_nonpos_iff.mpr (Or.inl ⟨Complex.normSq_nonneg _, ?_⟩)` and prove the remaining obligations. Break down `k with a | b` into its components or cases. Rewrite using `[hDi]`. Evaluate the numerical expressions.

Consider the cases of `b`. Rewrite using `[hDf]`. Simplify using `[ht.le]`. Rewrite using `[hDt]`. Conclude with `hle`.

Establish `hsum : 0 ≤ ∑ k, Complex.normSq (g k) * (D k).re`. Rewrite using `[← hvv, hJ_self_re]`. Conclude with `Finset.sum_nonneg fun i _ => nonneg_term_lemma ε σ hσ v hv0 i`. Establish `hzero : ∀ k, Complex.normSq (g k) * (D k).re = 0`. Establish `h0 : ∑ k, Complex.normSq (g k) * (D k).re = 0` using `le_antisymm (Finset.sum_nonpos fun k _ => hterm k) hsum`.

Introduce `k`. Conclude with `(Finset.sum_eq_zero_iff_of_nonpos fun k _ => hterm k).mp h0 k (Finset.mem_univ k)`. Establish `hga : ∀ a, g (Sum.inl a) = 0`. Introduce `a`. Simplify `hzero (Sum.inl a)` using `[hDi]`.

Establish `hgf : g (Sum.inr false) = 0`. Simplify `hzero (Sum.inr false)` using `[hDf, ht.ne']`. Establish `hvy : v = g (Sum.inr true) • y`. Rewrite using `[hv, Fintype.sum_sum_type, Fintype.sum_bool]`. Simplify using `[hga, hgf, hmt]`.

Establish `hgt : g (Sum.inr true) ≠ 0`. Break down `k0 with a | b` into its components or cases. Conclude with `absurd (hga a) hk0`. Consider the cases of `b`. Conclude with `absurd hgf hk0`.

Conclude with `hk0`. Establish `hy0 : ∀ j, y (σ j) = 0`. Introduce `j`. Establish `h` using `hv0 j`. Rewrite `h` using `[hvy, Pi.smul_apply, smul_eq_mul]`.

Conclude with `(mul_eq_zero.mp h).resolve_left hgt`. Conclude with `hcon (pos_of_vanish_lemma_2 ε σ hσ y hy0 hy)`.
-/
theorem pos_of_perp (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ))
    (y : Fin n → ℂ) (hey : ∀ c, hJ ε (e c) y = 0) (hfy : ∀ c, hJ ε (f c) y = 0)
    (hzy : hJ ε z y = 0) (hy : y ≠ 0) : 0 < (hJ ε y y).re := by
  by_contra hcon
  have hle : (hJ ε y y).re ≤ 0 := not_lt.mp hcon
  obtain ⟨m, hm⟩ : ∃ m : Fin r ⊕ Bool → Fin n → ℂ,
      m = Sum.elim (fun a => e a - f a) (fun b => if b then y else z) := ⟨_, rfl⟩
  have hmi : ∀ a, m (Sum.inl a) = e a - f a := fun a => by rw [hm]; rfl
  have hmf : m (Sum.inr false) = z := by rw [hm]; rfl
  have hmt : m (Sum.inr true) = y := by rw [hm]; rfl
  obtain ⟨D, hD⟩ : ∃ D : Fin r ⊕ Bool → ℂ,
      D = Sum.elim (fun _ => (-2 : ℂ)) (fun b => if b then hJ ε y y else -(t : ℂ)) := ⟨_, rfl⟩
  have hDi : ∀ a, D (Sum.inl a) = -2 := fun a => by rw [hD]; rfl
  have hDf : D (Sum.inr false) = -(t : ℂ) := by rw [hD]; rfl
  have hDt : D (Sum.inr true) = hJ ε y y := by rw [hD]; rfl
  have hG : ∀ k l, hJ ε (m k) (m l) = if k = l then D k else 0 := by
    intro k l
    rcases k with a | i <;> rcases l with b | j
    · simp only [hmi, hJ_sub_left, hJ_sub_right, hee, hff, hef, hJ_conj ε (e b) (f a), hDi]
      by_cases hab : a = b
      · subst hab
        norm_num
      · simp [hab, Ne.symm hab]
    · cases j <;> simp [hmi, hmf, hmt, hJ_sub_left, hez, hfz, hey, hfy]
    · cases i <;> simp [hmi, hmf, hmt, hJ_sub_right, hJ_conj ε (e b) z, hJ_conj ε (f b) z,
        hJ_conj ε (e b) y, hJ_conj ε (f b) y, hez, hfz, hey, hfy]
    · cases i <;> cases j <;> simp [hmf, hmt, hDf, hDt, hzz, hzy, hJ_conj ε z y]
  obtain ⟨g, hg, k0, hk0⟩ := exists_rel (fun k : Fin r ⊕ Bool => fun j : Fin (r + 1) => m k (σ j))
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]; omega)
  obtain ⟨v, hv⟩ : ∃ v : Fin n → ℂ, v = ∑ k, g k • m k := ⟨_, rfl⟩
  have hv0 : ∀ j, v (σ j) = 0 := by
    intro j
    have h := congrFun hg j
    rw [hv]
    simpa [Finset.sum_apply] using h
  have hvv : (hJ ε v v).re = ∑ k, Complex.normSq (g k) * (D k).re := by
    rw [hv, hJ_sum_smul_left, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hJ_sum_smul_right]
    simp only [hG, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact re_star_mul_mul _ _
  have hterm : ∀ k, Complex.normSq (g k) * (D k).re ≤ 0 := by
    intro k
    refine mul_nonpos_iff.mpr (Or.inl ⟨Complex.normSq_nonneg _, ?_⟩)
    rcases k with a | b
    · rw [hDi]
      norm_num
    · cases b
      · rw [hDf]
        simp [ht.le]
      · rw [hDt]
        exact hle
  have hsum : 0 ≤ ∑ k, Complex.normSq (g k) * (D k).re := by
    rw [← hvv, hJ_self_re]
    exact Finset.sum_nonneg fun i _ => nonneg_term_lemma ε σ hσ v hv0 i
  have hzero : ∀ k, Complex.normSq (g k) * (D k).re = 0 := by
    have h0 : ∑ k, Complex.normSq (g k) * (D k).re = 0 :=
      le_antisymm (Finset.sum_nonpos fun k _ => hterm k) hsum
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hterm k).mp h0 k (Finset.mem_univ k)
  have hga : ∀ a, g (Sum.inl a) = 0 := by
    intro a
    simpa [hDi] using hzero (Sum.inl a)
  have hgf : g (Sum.inr false) = 0 := by
    simpa [hDf, ht.ne'] using hzero (Sum.inr false)
  have hvy : v = g (Sum.inr true) • y := by
    rw [hv, Fintype.sum_sum_type, Fintype.sum_bool]
    simp [hga, hgf, hmt]
  have hgt : g (Sum.inr true) ≠ 0 := by
    rcases k0 with a | b
    · exact absurd (hga a) hk0
    · cases b
      · exact absurd hgf hk0
      · exact hk0
  have hy0 : ∀ j, y (σ j) = 0 := by
    intro j
    have h := hv0 j
    rw [hvy, Pi.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hgt
  exact hcon (pos_of_vanish_lemma_2 ε σ hσ y hy0 hy)

end PI.ScPiFrameW
