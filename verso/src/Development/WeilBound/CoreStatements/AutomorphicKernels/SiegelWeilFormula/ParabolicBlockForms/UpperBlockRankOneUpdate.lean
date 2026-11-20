import Mathlib

namespace PositivityTheory.SiegelWeilFormula.Act.C4.Bq

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

def NQ (x y : ι) (M : Matrix ι ι R) : Prop :=
  (∀ k, (M - 1) k x = 0) ∧ ∀ k l, l ≠ x → l ≠ y → k ≠ x → (M - 1) k l = 0

def Pad (x y : ι) (J : Matrix ι ι R) : Prop :=
  ∀ r c, (r = x ∨ r = y ∨ c = x ∨ c = y) → J r c = (1 : Matrix ι ι R) r c

/- English proof (translation)
Establish `e : J * M * J' - 1 = J * (M - 1) * J'`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJJ]`. Establish `hJx : ∀ r, r ≠ x → J r x = 0` using `fun r hr => by`. Rewrite using `[hJ r x (Or.inr (Or.inr (Or.inl rfl))), Matrix.one_apply_ne hr]`. Establish `hJ'x : ∀ l, l ≠ x → J' l x = 0` using `fun l hl => by`.

Rewrite using `[hJ' l x (Or.inr (Or.inr (Or.inl rfl))), Matrix.one_apply_ne hl]`. Establish `hJ'y : ∀ c, c ≠ y → J' y c = 0` using `fun c hc => by`. Rewrite using `[hJ' y c (Or.inr (Or.inl rfl)), Matrix.one_apply_ne (Ne.symm hc)]`. Use `⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩` and prove the remaining obligations. Rewrite using `[e, Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun m' _ => ?_` and prove the remaining obligations. Distinguish the cases in `hm : m = x`. Substitute `hm` using the available equality.

Rewrite using `[hM.1 m', mul_zero, zero_mul]`. Rewrite using `[hJ'x m hm, mul_zero]`. Rewrite using `[e, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`.

Use `Finset.sum_eq_zero fun m' _ => ?_` and prove the remaining obligations. Distinguish the cases in `hm : m = y`. Substitute `hm` using the available equality. Rewrite using `[hJ'y l hly, mul_zero]`. Distinguish the cases in `hmx : m = x`.

Substitute `hmx` using the available equality. Rewrite using `[hM.1 m', mul_zero, zero_mul]`. Distinguish the cases in `hm'x : m' = x`. Substitute `hm'x` using the available equality. Rewrite using `[hJx k hkx, zero_mul, zero_mul]`.

Rewrite using `[hM.2 m' m hmx hm hm'x, mul_zero, zero_mul]`.
-/
theorem NQ.conj {x y : ι} (hxy : x ≠ y) {J J' M : Matrix ι ι R} (hJ : Pad x y J) (hJ' : Pad x y J')
    (hJJ : J * J' = 1) (hM : NQ x y M) : NQ x y (J * M * J') := by
  have e : J * M * J' - 1 = J * (M - 1) * J' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJJ]
  have hJx : ∀ r, r ≠ x → J r x = 0 := fun r hr => by
    rw [hJ r x (Or.inr (Or.inr (Or.inl rfl))), Matrix.one_apply_ne hr]
  have hJ'x : ∀ l, l ≠ x → J' l x = 0 := fun l hl => by
    rw [hJ' l x (Or.inr (Or.inr (Or.inl rfl))), Matrix.one_apply_ne hl]
  have hJ'y : ∀ c, c ≠ y → J' y c = 0 := fun c hc => by
    rw [hJ' y c (Or.inr (Or.inl rfl)), Matrix.one_apply_ne (Ne.symm hc)]
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rw [e, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun m' _ => ?_
    by_cases hm : m = x
    · subst hm; rw [hM.1 m', mul_zero, zero_mul]
    · rw [hJ'x m hm, mul_zero]
  · rw [e, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun m' _ => ?_
    by_cases hm : m = y
    · subst hm; rw [hJ'y l hly, mul_zero]
    · by_cases hmx : m = x
      · subst hmx; rw [hM.1 m', mul_zero, zero_mul]
      · by_cases hm'x : m' = x
        · subst hm'x; rw [hJx k hkx, zero_mul, zero_mul]
        · rw [hM.2 m' m hmx hm hm'x, mul_zero, zero_mul]

/- English proof (translation)
Establish `e : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1)`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Use `⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩` and prove the remaining obligations. Rewrite using `[e, Matrix.add_apply, Matrix.add_apply, hM.1 k, hN.1 k, Matrix.mul_apply]`.

Simplify using `only [zero_add]`. Conclude with `Finset.sum_eq_zero fun m _ => by rw [hN.1 m, mul_zero]`. Rewrite using `[e, Matrix.add_apply, Matrix.add_apply, hM.2 k l hlx hly hkx, hN.2 k l hlx hly hkx, Matrix.mul_apply]`. Simplify using `only [zero_add]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hm : m = x`. Substitute `hm` using the available equality. Rewrite using `[hM.1 k, zero_mul]`. Rewrite using `[hN.2 m l hlx hly hm, mul_zero]`.
-/
theorem NQ.mul {x y : ι} {M N : Matrix ι ι R} (hM : NQ x y M) (hN : NQ x y N) : NQ x y (M * N) := by
  have e : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]; abel
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rw [e, Matrix.add_apply, Matrix.add_apply, hM.1 k, hN.1 k, Matrix.mul_apply]
    simp only [zero_add]
    exact Finset.sum_eq_zero fun m _ => by rw [hN.1 m, mul_zero]
  · rw [e, Matrix.add_apply, Matrix.add_apply, hM.2 k l hlx hly hkx, hN.2 k l hlx hly hkx, Matrix.mul_apply]
    simp only [zero_add]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : m = x
    · subst hm; rw [hM.1 k, zero_mul]
    · rw [hN.2 m l hlx hly hm, mul_zero]

/- English proof (translation)
Break down `h with rfl | ⟨hly, hkx⟩` into its components or cases. Use `hM.1 k` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis. Distinguish the cases in `hlx : l = x`. Substitute `hlx` using the available equality.

Use `hM.1 k` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis. Use `hM.2 k l hlx hly hkx` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem NQ.apply {x y : ι} {M : Matrix ι ι R} (hM : NQ x y M) {k l : ι} (h : l = x ∨ (l ≠ y ∧ k ≠ x)) :
    M k l = (1 : Matrix ι ι R) k l := by
  rcases h with rfl | ⟨hly, hkx⟩
  · have := hM.1 k; rwa [Matrix.sub_apply, sub_eq_zero] at this
  · by_cases hlx : l = x
    · subst hlx; have := hM.1 k; rwa [Matrix.sub_apply, sub_eq_zero] at this
    · have := hM.2 k l hlx hly hkx; rwa [Matrix.sub_apply, sub_eq_zero] at this

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]`. Distinguish the cases in `hk : k = i₀`. Substitute `hk` using the available equality. Rewrite using `[hM.apply (Or.inl rfl)]`.

Simplify using `[Matrix.one_apply]`. Rewrite using `[hM.apply (Or.inr ⟨by simp, by simp⟩)]`. Simplify using `[Matrix.one_apply]`.
-/
theorem NQ.projected_block_lower_sum {i₀ : Fin n} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    M.toBlocks₂₁ = 0 := by
  ext i k
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  by_cases hk : k = i₀
  · subst hk; rw [hM.apply (Or.inl rfl)]; simp [Matrix.one_apply]
  · rw [hM.apply (Or.inr ⟨by simp, by simp⟩)]
    simp [Matrix.one_apply]

/- English proof (translation)
Use `Matrix.ext fun a k => ?_` and prove the remaining obligations. Simplify using `only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Finset.univ_unique, Finset.sum_singleton]`. Distinguish the cases in `ha : a = i₀`. Substitute `ha` using the available equality. Simplify using `only [Pi.single_eq_same, one_mul, Matrix.sub_apply]`.

Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Distinguish the cases in `hk : a = k`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`.

Rewrite using `[Pi.single_eq_of_ne ha, zero_mul, add_zero]`. Distinguish the cases in `hk : k = i₀`. Substitute `hk` using the available equality. Rewrite using `[hM.apply (Or.inl rfl)]`. Simplify using `[Matrix.one_apply]`.

Rewrite using `[hM.apply (Or.inr ⟨by simp, by simpa using ha⟩)]; simp [Matrix.one_apply]`.
-/
theorem NQ.upper_block_rank_one_update {i₀ : Fin n} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    M.toBlocks₁₁ = 1 + replicateCol Unit (Pi.single i₀ (1 : R)) * replicateRow Unit (fun k => (M - 1) (Sum.inl i₀) (Sum.inl k)) := by
  refine Matrix.ext fun a k => ?_
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, replicateCol_apply,
    replicateRow_apply, Finset.univ_unique, Finset.sum_singleton]
  by_cases ha : a = i₀
  · subst ha
    simp only [Pi.single_eq_same, one_mul, Matrix.sub_apply]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hk : a = k
    · subst hk; simp
    · simp [hk]
  · rw [Pi.single_eq_of_ne ha, zero_mul, add_zero]
    by_cases hk : k = i₀
    · subst hk; rw [hM.apply (Or.inl rfl)]; simp [Matrix.one_apply]
    · rw [hM.apply (Or.inr ⟨by simp, by simpa using ha⟩)]; simp [Matrix.one_apply]

/- English proof (translation)
Rewrite using `[hM.upper_block_rank_one_update, det_one_add_replicateCol_mul_replicateRow]`. Establish `h0 : (M - 1) (Sum.inl i₀) (Sum.inl i₀) = 0` using `hM.1 _`. Rewrite `h0` using `[Matrix.sub_apply, sub_eq_zero]`. Simplify using `[dotProduct, Pi.single_apply, h0]`.
-/
theorem NQ.upper_block_det_one {i₀ : Fin n} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    M.toBlocks₁₁.det = 1 := by
  rw [hM.upper_block_rank_one_update, det_one_add_replicateCol_mul_replicateRow]
  have h0 : (M - 1) (Sum.inl i₀) (Sum.inl i₀) = 0 := hM.1 _
  rw [Matrix.sub_apply, sub_eq_zero] at h0
  simp [dotProduct, Pi.single_apply, h0]

/- English proof (translation)
Use `⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩` and prove the remaining obligations. Break down `k with a | a` into its components or cases. Use `hA0 a` as an intermediate fact. Simplify `this` using `[Matrix.sub_apply, Matrix.one_apply]`. Simplify using `[Matrix.sub_apply, Matrix.one_apply]`.

Apply the tactic sequence `rcases l with l | l <;> rcases k with k | k`. Establish `hk : k ≠ i₀` using `fun h => hkx (by rw [h])`. Use `hA k l hk` as an intermediate fact. Simplify `this` using `[Matrix.sub_apply, Matrix.one_apply]`. Simplify using `[Matrix.sub_apply, Matrix.one_apply]`.

Establish `hk : k ≠ i₀` using `fun h => hkx (by rw [h])`. Establish `hl : l ≠ i₀` using `fun h => hly (by rw [h])`. Simplify using `[Matrix.sub_apply, Matrix.one_apply, hB k l hk hl]`. Establish `hl : l ≠ i₀` using `fun h => hly (by rw [h])`. Use `hD k l hl` as an intermediate fact.

Simplify `this` using `[Matrix.sub_apply, Matrix.one_apply]`.
-/
theorem NQ.of_blocks {i₀ : Fin n} {A B D : Matrix (Fin n) (Fin n) R}
    (hA0 : ∀ a, (A - 1) a i₀ = 0) (hA : ∀ a k, a ≠ i₀ → (A - 1) a k = 0)
    (hB : ∀ a k, a ≠ i₀ → k ≠ i₀ → B a k = 0) (hD : ∀ a k, k ≠ i₀ → (D - 1) a k = 0) :
    NQ (Sum.inl i₀) (Sum.inr i₀) (Matrix.fromBlocks A B 0 D) := by
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rcases k with a | a
    · have := hA0 a
      simpa [Matrix.sub_apply, Matrix.one_apply] using this
    · simp [Matrix.sub_apply, Matrix.one_apply]
  · rcases l with l | l <;> rcases k with k | k
    · have hk : k ≠ i₀ := fun h => hkx (by rw [h])
      have := hA k l hk
      simpa [Matrix.sub_apply, Matrix.one_apply] using this
    · simp [Matrix.sub_apply, Matrix.one_apply]
    · have hk : k ≠ i₀ := fun h => hkx (by rw [h])
      have hl : l ≠ i₀ := fun h => hly (by rw [h])
      simp [Matrix.sub_apply, Matrix.one_apply, hB k l hk hl]
    · have hl : l ≠ i₀ := fun h => hly (by rw [h])
      have := hD k l hl
      simpa [Matrix.sub_apply, Matrix.one_apply] using this

end PositivityTheory.SiegelWeilFormula.Act.C4.Bq
