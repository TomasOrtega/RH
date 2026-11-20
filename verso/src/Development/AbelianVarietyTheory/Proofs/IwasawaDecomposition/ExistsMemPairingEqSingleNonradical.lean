import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `r g rk Mq V ε hskew hli horth hperp j hj`. Establish `skew : ∀ x y : Fin r → ℚ, x ⬝ᵥ Mq *ᵥ y = -(y ⬝ᵥ Mq *ᵥ x)`. Introduce `x y`. Rewrite using `[dotProduct_mulVec x Mq y, dotProduct_comm y, ← vecMul_transpose, hskew, vecMul_neg, neg_dotProduct, neg_neg]`. Set `Φ : (Fin r → ℚ) →ₗ[ℚ] (Fin g → ℚ)` to `{ toFun := fun x i => x ⬝ᵥ Mq *ᵥ ε i map_add' := by intro x y; funext i; simp [add_dotProduct] map_smul' := by intro c x; funext i; simp [smul_dotProduct] }`.

Establish `hΦ : ∀ x i, Φ x i = x ⬝ᵥ Mq *ᵥ ε i` using `fun _ _ => rfl`. It suffices to establish `h : Pi.single j (1 : ℚ) ∈ V.map Φ by`. Take `⟨x, hx, hxe⟩` from `h`. Use `⟨x, hx, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← hΦ, hxe, Pi.single_apply]`.

Assume the negation of the conclusion as `hnot`. Take `⟨f, hfj, hfS⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance`. Establish `hf0 : ∀ s ∈ V.map Φ, f s = 0`. Introduce `s hs`. Establish `: f s ∈ (V.map Φ).map f` using `Submodule.mem_map_of_mem hs`.

Rewrite `this` using `[hfS]`. Simplify using `using this`. Use `set a : Fin g → ℚ := fun i => f (Pi.single i 1) with ha`. Establish `hfsum : ∀ s : Fin g → ℚ, f s = ∑ i, a i * s i`. Introduce `s`.

Use `conv_lhs => rw [pi_eq_sum_univ s]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`. Use `congr 1`.

Simplify using `only [ha]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `[Pi.single_apply, eq_comm]`. Use `set a' : Fin g → ℚ := fun i => if rk ≤ i.val then a i else 0 with ha'`.

Establish `hΦlow : ∀ w ∈ V, ∀ i : Fin g, i.val < rk → Φ w i = 0`. Introduce `w hw i hi`. Rewrite using `[hΦ, skew, horth i hi w hw, neg_zero]`. Establish `hsum' : ∀ w ∈ V, ∑ i, a' i * Φ w i = 0`. Introduce `w hw`.

Establish `h1 : ∑ i, a' i * Φ w i = ∑ i, a i * Φ w i`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : rk ≤ i.val`. Simplify using `[ha', hi]`. Simplify using `[ha', hi, hΦlow w hw i (by omega)]`.

Rewrite using `[h1, ← hfsum]`. Conclude with `hf0 _ (Submodule.mem_map_of_mem hw)`. Use `set e : Fin r → ℚ := ∑ i, a' i • ε i with he`. Establish `heV : ∀ w ∈ V, e ⬝ᵥ Mq *ᵥ w = 0`. Introduce `w hw`.

Rewrite using `[he, sum_dotProduct]`. Establish `: ∑ i, (a' i • ε i) ⬝ᵥ Mq *ᵥ w = -∑ i, a' i * Φ w i`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_dotProduct, smul_eq_mul, hΦ, skew w, mul_neg, neg_neg]`.

Rewrite using `[this, hsum' w hw, neg_zero]`. Establish `hespan` using `hperp e heV`. Rewrite `hespan` using `[Finsupp.mem_span_image_iff_linearCombination]`. Take `⟨l, hl, hc⟩` from `hespan`. Set `c' : Fin g → ℚ` to `fun i => l i`.

Establish `hc' : ∑ i, c' i • ε i = e`. Rewrite using `[← hc, Finsupp.linearCombination_apply, Finsupp.sum_fintype]`. Introduce `i`. Simplify using the standard rewrite rules. Establish `hzero : ∑ i, (a' i - c' i) • ε i = 0`.

Simplify using `only [sub_smul, Finset.sum_sub_distrib, hc', he, sub_self]`. Use `Fintype.linearIndependent_iff.mp hli _ hzero j` as an intermediate fact. Establish `hcj : c' j = 0` using `(Finsupp.mem_supported' ℚ l).mp hl j (by simp; omega)`. Establish `haj : a' j = a j` using `by simp [ha', hj]`. Rewrite `this` using `[hcj, haj, sub_zero]`.

Conclude with `hfj this`.
-/
theorem dualV_pairing_exists : ∀ (r g rk : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)) (ε : Fin g → Fin r → ℚ), Mqᵀ = -Mq → LinearIndependent ℚ ε → (∀ i : Fin g, i.val < rk → ∀ w ∈ V, ε i ⬝ᵥ Mq *ᵥ w = 0) → (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → y ∈ Submodule.span ℚ (ε '' {i | i.val < rk})) → ∀ j : Fin g, rk ≤ j.val → ∃ x ∈ V, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0 := by
  intro r g rk Mq V ε hskew hli horth hperp j hj
  have skew : ∀ x y : Fin r → ℚ, x ⬝ᵥ Mq *ᵥ y = -(y ⬝ᵥ Mq *ᵥ x) := by
    intro x y
    rw [dotProduct_mulVec x Mq y, dotProduct_comm y, ← vecMul_transpose, hskew, vecMul_neg,
      neg_dotProduct, neg_neg]
  let Φ : (Fin r → ℚ) →ₗ[ℚ] (Fin g → ℚ) :=
    { toFun := fun x i => x ⬝ᵥ Mq *ᵥ ε i
      map_add' := by intro x y; funext i; simp [add_dotProduct]
      map_smul' := by intro c x; funext i; simp [smul_dotProduct] }
  have hΦ : ∀ x i, Φ x i = x ⬝ᵥ Mq *ᵥ ε i := fun _ _ => rfl
  suffices h : Pi.single j (1 : ℚ) ∈ V.map Φ by
    obtain ⟨x, hx, hxe⟩ := h
    refine ⟨x, hx, fun i => ?_⟩
    rw [← hΦ, hxe, Pi.single_apply]
  by_contra hnot
  obtain ⟨f, hfj, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hf0 : ∀ s ∈ V.map Φ, f s = 0 := by
    intro s hs
    have : f s ∈ (V.map Φ).map f := Submodule.mem_map_of_mem hs
    rw [hfS] at this
    simpa using this
  set a : Fin g → ℚ := fun i => f (Pi.single i 1) with ha
  have hfsum : ∀ s : Fin g → ℚ, f s = ∑ i, a i * s i := by
    intro s
    conv_lhs => rw [pi_eq_sum_univ s]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    congr 1
    simp only [ha]
    congr 1
    funext k
    simp [Pi.single_apply, eq_comm]
  set a' : Fin g → ℚ := fun i => if rk ≤ i.val then a i else 0 with ha'
  have hΦlow : ∀ w ∈ V, ∀ i : Fin g, i.val < rk → Φ w i = 0 := by
    intro w hw i hi
    rw [hΦ, skew, horth i hi w hw, neg_zero]
  have hsum' : ∀ w ∈ V, ∑ i, a' i * Φ w i = 0 := by
    intro w hw
    have h1 : ∑ i, a' i * Φ w i = ∑ i, a i * Φ w i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : rk ≤ i.val
      · simp [ha', hi]
      · simp [ha', hi, hΦlow w hw i (by omega)]
    rw [h1, ← hfsum]
    exact hf0 _ (Submodule.mem_map_of_mem hw)
  set e : Fin r → ℚ := ∑ i, a' i • ε i with he
  have heV : ∀ w ∈ V, e ⬝ᵥ Mq *ᵥ w = 0 := by
    intro w hw
    rw [he, sum_dotProduct]
    have : ∑ i, (a' i • ε i) ⬝ᵥ Mq *ᵥ w = -∑ i, a' i * Φ w i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_dotProduct, smul_eq_mul, hΦ, skew w, mul_neg, neg_neg]
    rw [this, hsum' w hw, neg_zero]
  have hespan := hperp e heV
  rw [Finsupp.mem_span_image_iff_linearCombination] at hespan
  obtain ⟨l, hl, hc⟩ := hespan
  let c' : Fin g → ℚ := fun i => l i
  have hc' : ∑ i, c' i • ε i = e := by
    rw [← hc, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  have hzero : ∑ i, (a' i - c' i) • ε i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hc', he, sub_self]
  have := Fintype.linearIndependent_iff.mp hli _ hzero j
  have hcj : c' j = 0 := (Finsupp.mem_supported' ℚ l).mp hl j (by simp; omega)
  have haj : a' j = a j := by simp [ha', hj]
  rw [hcj, haj, sub_zero] at this
  exact hfj this

end GlobalTheory
