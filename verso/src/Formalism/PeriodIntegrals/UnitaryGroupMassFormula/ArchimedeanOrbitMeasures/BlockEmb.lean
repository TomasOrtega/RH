import Mathlib

noncomputable section

namespace PI.AprimeInfG

open scoped Matrix

variable {n k : ℕ} {S : Finset (Fin n)}

def emb0 (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if h : i ∈ S ∧ j ∈ S then X (e.symm ⟨i, h.1⟩) (e.symm ⟨j, h.2⟩) else 0

def blockEmbeddingAddHom (e : Fin k ≃ S) : Matrix (Fin k) (Fin k) ℂ →+ Matrix (Fin n) (Fin n) ℂ where
  toFun := emb0 e
  map_zero' := by
    funext i j
    simp [emb0]
  map_add' X Y := by
    funext i j
    simp only [emb0, Matrix.add_apply]
    split_ifs <;> simp

/- English proof (translation)
Simplify using `[emb0]`.
-/
private theorem emb0_apply_coe_coe (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    emb0 e X (e a) (e b) = X a b := by
  simp [emb0]

/- English proof (translation)
Simplify using `[emb0, hi]`.
-/
private theorem emb0_apply_of_left_not_mem (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) {i j : Fin n}
    (hi : i ∉ S) : emb0 e X i j = 0 := by
  simp [emb0, hi]

/- English proof (translation)
Simplify using `[emb0, hj]`.
-/
private theorem emb0_apply_of_right_not_mem (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) {i j : Fin n}
    (hj : j ∉ S) : emb0 e X i j = 0 := by
  simp [emb0, hj]

/- English proof (translation)
Assemble the required witnesses or components as `⟨e.symm ⟨i, hi⟩, by simp⟩`.
-/
private theorem exists_equiv_coe_eq_of_mem (e : Fin k ≃ S) {i : Fin n} (hi : i ∈ S) :
    ∃ a, (e a : Fin n) = i :=
  ⟨e.symm ⟨i, hi⟩, by simp⟩

/- English proof (translation)
Rewrite using `[← Finset.sum_subset (Finset.subset_univ S) (fun l _ hl => hF l hl), ← Finset.sum_coe_sort S]`. Conclude with `(Equiv.sum_comp e (fun x : S => F x)).symm`.
-/
private theorem sum_eq_sum_equiv_of_eq_zero_of_not_mem {M : Type*} [AddCommMonoid M] (e : Fin k ≃ S) (F : Fin n → M)
    (hF : ∀ l, l ∉ S → F l = 0) : ∑ l, F l = ∑ c, F (e c) := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun l _ hl => hF l hl), ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp e (fun x : S => F x)).symm

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hi : i ∈ S`. Distinguish the cases in `hj : j ∈ S`. Take `⟨a, rfl⟩` from `exists_equiv_coe_eq_of_mem e hi`.

Take `⟨b, rfl⟩` from `exists_equiv_coe_eq_of_mem e hj`. Rewrite using `[emb0_apply_coe_coe, Matrix.mul_apply, sum_eq_sum_equiv_of_eq_zero_of_not_mem e]`. Simplify using `only [emb0_apply_coe_coe]`. Introduce `l hl`. Simplify using `[emb0_apply_of_right_not_mem e X hl]`.

Rewrite using `[emb0_apply_of_right_not_mem e _ hj]`. Use `symm`. Conclude with `Finset.sum_eq_zero (fun l _ => by rw [emb0_apply_of_right_not_mem e Y hj, mul_zero])`. Rewrite using `[emb0_apply_of_left_not_mem e _ hi]`. Use `symm`.

Conclude with `Finset.sum_eq_zero (fun l _ => by rw [emb0_apply_of_left_not_mem e X hi, zero_mul])`.
-/
theorem embed_mul (e : Fin k ≃ S) (X Y : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e (X * Y) = emb0 e X * emb0 e Y := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, Matrix.mul_apply, sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
      · simp only [emb0_apply_coe_coe]
      · intro l hl
        simp [emb0_apply_of_right_not_mem e X hl]
    · rw [emb0_apply_of_right_not_mem e _ hj]
      symm
      exact Finset.sum_eq_zero (fun l _ => by rw [emb0_apply_of_right_not_mem e Y hj, mul_zero])
  · rw [emb0_apply_of_left_not_mem e _ hi]
    symm
    exact Finset.sum_eq_zero (fun l _ => by rw [emb0_apply_of_left_not_mem e X hi, zero_mul])

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp only [zero_add, pow_one]`. Consider the case `succ m ih => rw [pow_succ, embed_mul, ih, ← pow_succ]`.
-/
theorem embed_pow_succ (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (m : ℕ) :
    emb0 e (X ^ (m + 1)) = emb0 e X ^ (m + 1) := by
  induction m with
  | zero => simp only [zero_add, pow_one]
  | succ m ih => rw [pow_succ, embed_mul, ih, ← pow_succ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem emb0Add_apply (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    blockEmbeddingAddHom e X = emb0 e X :=
  rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply]`. Distinguish the cases in `hi : i ∈ S`. Distinguish the cases in `hj : j ∈ S`. Take `⟨a, rfl⟩` from `exists_equiv_coe_eq_of_mem e hi`.

Take `⟨b, rfl⟩` from `exists_equiv_coe_eq_of_mem e hj`. Rewrite using `[emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.smul_apply]`. Rewrite using `[emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_right_not_mem e _ hj, smul_zero]`. Rewrite using `[emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_left_not_mem e _ hi, smul_zero]`.
-/
private theorem emb0_smul (e : Fin k ≃ S) (c : ℂ) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e (c • X) = c • emb0 e X := by
  ext i j
  rw [Matrix.smul_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.smul_apply]
    · rw [emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_right_not_mem e _ hj, smul_zero]
  · rw [emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_left_not_mem e _ hi, smul_zero]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `h : i ∈ S ∧ j ∈ S`. Simplify using `only [emb0, dif_pos h]`. Conclude with `continuous_id.matrix_elem _ _`. Simplify using `only [emb0, dif_neg h]`.

Conclude with `continuous_const`.
-/
theorem continuous_embed (e : Fin k ≃ S) : Continuous (emb0 e) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : i ∈ S ∧ j ∈ S
  · simp only [emb0, dif_pos h]
    exact continuous_id.matrix_elem _ _
  · simp only [emb0, dif_neg h]
    exact continuous_const

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra`. Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `h1` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X`.

Establish `h2` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (emb0 e X)`. Establish `h3` using `(h1.map (blockEmbeddingAddHom e) (continuous_embed e)).add (hasSum_ite_eq 0 (1 - emb0 e 1))`. Use `h2.unique ?_` and prove the remaining obligations. Use `h3 using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals try rfl`.

Use function extensionality and compare the values at `m`. Break down `m with _ | m` into its components or cases. Simplify using `[emb0Add_apply]`. Simplify using `[emb0Add_apply, emb0_smul, embed_pow_succ]`.
-/
theorem exp_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    NormedSpace.exp (emb0 e X) = emb0 e (NormedSpace.exp X) + (1 - emb0 e 1) := by
  letI : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (emb0 e X)
  have h3 := (h1.map (blockEmbeddingAddHom e) (continuous_embed e)).add
    (hasSum_ite_eq 0 (1 - emb0 e 1))
  refine h2.unique ?_
  convert h3 using 1
  all_goals try rfl
  funext m
  rcases m with _ | m
  · simp [emb0Add_apply]
  · simp [emb0Add_apply, emb0_smul, embed_pow_succ]

def resB (e : Fin k ≃ S) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => M (e a) (e b)

/- English proof (translation)
Use extensionality with `a b`. Conclude with `emb0_apply_coe_coe e X a b`.
-/
theorem restrict_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : resB e (emb0 e X) = X := by
  ext a b
  exact emb0_apply_coe_coe e X a b

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hi : i ∈ S`. Distinguish the cases in `hj : j ∈ S`. Take `⟨a, rfl⟩` from `exists_equiv_coe_eq_of_mem e hi`. Take `⟨b, rfl⟩` from `exists_equiv_coe_eq_of_mem e hj`.

Rewrite using `[emb0_apply_coe_coe]`. Both sides reduce to the same expression. Rewrite using `[emb0_apply_of_right_not_mem e _ hj, hM i j (Or.inr hj)]`. Rewrite using `[emb0_apply_of_left_not_mem e _ hi, hM i j (Or.inl hi)]`.
-/
theorem embed_restrict (e : Fin k ≃ S) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) :
    emb0 e (resB e M) = M := by
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe]
      rfl
    · rw [emb0_apply_of_right_not_mem e _ hj, hM i j (Or.inr hj)]
  · rw [emb0_apply_of_left_not_mem e _ hi, hM i j (Or.inl hi)]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply]`. Distinguish the cases in `hi : i ∈ S`. Distinguish the cases in `hj : j ∈ S`. Take `⟨a, rfl⟩` from `exists_equiv_coe_eq_of_mem e hi`.

Take `⟨b, rfl⟩` from `exists_equiv_coe_eq_of_mem e hj`. Rewrite using `[emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.conjTranspose_apply]`. Rewrite using `[emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_left_not_mem e _ hj, star_zero]`. Rewrite using `[emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_right_not_mem e _ hi, star_zero]`.
-/
theorem embed_conjTranspose (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e Xᴴ = (emb0 e X)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.conjTranspose_apply]
    · rw [emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_left_not_mem e _ hj, star_zero]
  · rw [emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_right_not_mem e _ hi, star_zero]

/- English proof (translation)
Rewrite using `[sum_eq_sum_equiv_of_eq_zero_of_not_mem e]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[sum_eq_sum_equiv_of_eq_zero_of_not_mem e]`. Simplify using `only [emb0_apply_coe_coe]`. Introduce `j hj`.

Simplify using `[emb0_apply_of_right_not_mem e X hj]`. Introduce `i hi`. Simplify using `[emb0_apply_of_left_not_mem e X hi]`.
-/
theorem sum_norm_sq_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    (∑ i, ∑ j, ‖emb0 e X i j‖ ^ 2) = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
  rw [sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
    · simp only [emb0_apply_coe_coe]
    · intro j hj
      simp [emb0_apply_of_right_not_mem e X hj]
  · intro i hi
    simp [emb0_apply_of_left_not_mem e X hi]

end PI.AprimeInfG
