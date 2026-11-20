import Mathlib

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `split_ifs with hc`. Substitute `hc` using the available equality. Establish `h1 : ∀ b, X 1 b = 1`. Introduce `b`. Establish `h` using `hl 1 1 b`.

Rewrite `h` using `[one_mul]`. Establish `hb` using `h0 1 b`. Establish `: X 1 b * (X 1 b - 1) = 0` using `by rw [mul_sub, mul_one, ← h, sub_self]`. Break down `mul_eq_zero.mp this with h' | h'` into its components or cases. Conclude with `absurd h' hb`.

Conclude with `sub_eq_zero.mp h'`. Simplify using `[h1]`. Choose the witnesses or unpack the hypotheses as in `⟨b₀, hb₀⟩ : ∃ b₀, X c b₀ ≠ 1 := by`. Assume the negation of the conclusion as `hne`. Simplify using `only [not_exists, ne_eq, not_not] at hne`.

Conclude with `hc (hnd c hne)`. Establish `hshift : (∑ b, X c b) = X c b₀ * ∑ b, X c b`. Rewrite using `[Finset.mul_sum]`. Repeatedly rewrite using `[← hr]`. Conclude with `(Equiv.sum_comp (Equiv.mulLeft b₀) (fun b => X c b)).symm`.

Establish `: (X c b₀ - 1) * ∑ b, X c b = 0`. Rewrite using `[sub_mul, one_mul, ← hshift, sub_self]`. Break down `mul_eq_zero.mp this with h' | h'` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h') hb₀`. Conclude with `h'`.
-/
private theorem sum_pairing_eq_card_ite_one {Γ K : Type} [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] [Field K]
    (X : Γ → Γ → K) (h0 : ∀ a b, X a b ≠ 0) (hl : ∀ a a' b, X (a * a') b = X a b * X a' b)
    (hr : ∀ a b b', X a (b * b') = X a b * X a b')
    (hnd : ∀ a, (∀ b, X a b = 1) → a = 1) (c : Γ) :
    (∑ b, X c b) = if c = 1 then (Fintype.card Γ : K) else 0 := by
  split_ifs with hc
  · subst hc
    have h1 : ∀ b, X 1 b = 1 := by
      intro b
      have h := hl 1 1 b
      rw [one_mul] at h
      have hb := h0 1 b
      have : X 1 b * (X 1 b - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hb
      · exact sub_eq_zero.mp h'
    simp [h1]
  · obtain ⟨b₀, hb₀⟩ : ∃ b₀, X c b₀ ≠ 1 := by
      by_contra hne
      simp only [not_exists, ne_eq, not_not] at hne
      exact hc (hnd c hne)
    have hshift : (∑ b, X c b) = X c b₀ * ∑ b, X c b := by
      rw [Finset.mul_sum]
      simp_rw [← hr]
      exact (Equiv.sum_comp (Equiv.mulLeft b₀) (fun b => X c b)).symm
    have : (X c b₀ - 1) * ∑ b, X c b = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hb₀
    · exact h'

/- English proof (translation)
Introduce `Γ K _ _ _ _ X h0 hl hr hnd`. Use `set M : Matrix Γ Γ K := Matrix.of X with hM`. Establish `hMP : M * Matrix.transpose (M.submatrix (Equiv.inv Γ) id) = (Fintype.card Γ : K) • (1 : Matrix Γ Γ K)`. Use extensionality with `a a'`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, hM, Matrix.of_apply, Equiv.inv_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`.

Repeatedly rewrite using `[← hl]`. Rewrite using `[sum_pairing_eq_card_ite_one X h0 hl hr hnd]`. Distinguish the cases in `h : a = a'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Establish `: a * a'⁻¹ ≠ 1` using `fun e => h (mul_inv_eq_one.mp e)`. Simplify using `[h, this]`. Establish `hdet` using `congrArg Matrix.det hMP`. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_permute, Matrix.det_smul, Matrix.det_one, mul_one]`. Establish `hs : ((Equiv.Perm.sign (Equiv.inv Γ) : ℤ) : K) ^ 2 = 1`.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.inv Γ)) with e | e <;> simp [e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, mul_pow, hs]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = (Fintype.card Γ : K) ^ (2 * Fintype.card Γ) := by rw [hdet, ← pow_mul, mul_comm]`.
-/
theorem det_bicharacter_pow_four :
    ∀ (Γ K : Type) [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] [Field K] (X : Γ → Γ → K), (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → (Matrix.of X).det ^ 4 = (Fintype.card Γ : K) ^ (2 * Fintype.card Γ) := by
  intro Γ K _ _ _ _ X h0 hl hr hnd
  set M : Matrix Γ Γ K := Matrix.of X with hM
  have hMP : M * Matrix.transpose (M.submatrix (Equiv.inv Γ) id) = (Fintype.card Γ : K) • (1 : Matrix Γ Γ K) := by
    ext a a'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, hM,
      Matrix.of_apply, Equiv.inv_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp_rw [← hl]
    rw [sum_pairing_eq_card_ite_one X h0 hl hr hnd]
    by_cases h : a = a'
    · subst h; simp
    · have : a * a'⁻¹ ≠ 1 := fun e => h (mul_inv_eq_one.mp e)
      simp [h, this]
  have hdet := congrArg Matrix.det hMP
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_permute, Matrix.det_smul, Matrix.det_one,
    mul_one] at hdet
  have hs : ((Equiv.Perm.sign (Equiv.inv Γ) : ℤ) : K) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.inv Γ)) with e | e <;> simp [e]
  calc M.det ^ 4 = (M.det * (((Equiv.Perm.sign (Equiv.inv Γ) : ℤ) : K) * M.det)) ^ 2 := by
        rw [mul_pow, mul_pow, hs]; ring
    _ = (Fintype.card Γ : K) ^ (2 * Fintype.card Γ) := by rw [hdet, ← pow_mul, mul_comm]

end GlobalTheory
