import Mathlib

namespace GlobalTheory.DetZeroFactorization

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Establish `hc : c ≠ 0` using `fun hc => hn ⟨ha, hc⟩`. Substitute `ha` using the available equality. Establish `hb : b = 0`. Establish `hbc : b * c = 0` using `by linear_combination -h`.

Conclude with `(mul_eq_zero.mp hbc).resolve_right hc`. Use `⟨d / c, by simp [hb], ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Use `⟨b / a, by field_simp, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_comm, mul_div_assoc', div_eq_iff ha]`.

Take the linear combination `-h`.
-/
theorem exists_mul_of_det_zero {K : Type*} [Field K] (a b c d : K) (h : a * d - b * c = 0)
    (hn : ¬ (a = 0 ∧ c = 0)) : ∃ u : K, b = a * u ∧ d = c * u := by
  by_cases ha : a = 0
  · have hc : c ≠ 0 := fun hc => hn ⟨ha, hc⟩
    subst ha
    have hb : b = 0 := by
      have hbc : b * c = 0 := by linear_combination -h
      exact (mul_eq_zero.mp hbc).resolve_right hc
    refine ⟨d / c, by simp [hb], ?_⟩
    field_simp
  · refine ⟨b / a, by field_simp, ?_⟩
    rw [eq_comm, mul_div_assoc', div_eq_iff ha]
    linear_combination -h

/- English proof (translation)
Introduce `d1 q hq δ hdet`. Establish `: Fact q.Prime` using `⟨hq⟩`. Establish `hq0 : (q : ℤ) ≠ 0` using `by exact_mod_cast hq.ne_zero`. Establish `hdet' : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = q` using `by rw [← hdet, Matrix.det_fin_two]`. Distinguish the cases in `hdiv : (q : ℤ) ∣ δ 0 0 ∧ (q : ℤ) ∣ δ 1 0`.

Take `⟨⟨a', ha'⟩, ⟨c', hc'⟩⟩` from `hdiv`. Establish `h1 : a' * δ 1 1 - δ 0 1 * c' = 1`. Apply `mul_left_cancel₀ hq0` to reduce the goal to its premises. Take the linear combination `hdet' - δ 1 1 * ha' + δ 0 1 * hc'`. Use `⟨⟨!![a', δ 0 1; c', δ 1 1], by rw [Matrix.det_fin_two_of]; exact h1⟩, none, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [d1, Matrix.mul_apply, Fin.sum_univ_two, ha', hc'] <;> ring`. Establish `h0 : (δ 0 0 : ZMod q) * δ 1 1 - δ 0 1 * δ 1 0 = 0`. Use `congrArg (Int.cast : ℤ → ZMod q) hdet'` as an intermediate fact. Move the coercions through the operations in `at this`.

Rewrite using `[this, ZMod.natCast_self]`. Establish `hn : ¬ ((δ 0 0 : ZMod q) = 0 ∧ (δ 1 0 : ZMod q) = 0)`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]` and apply the resulting hypothesis. Take `⟨u, hb, hd⟩` from `exists_mul_of_det_zero (δ 0 0 : ZMod q) (δ 0 1) (δ 1 0) (δ 1 1) h0 hn`. Take `⟨n, hnq, hnu⟩ : ∃ n : ℕ, n < q ∧ (n : ZMod q) = u` from `⟨u.val, ZMod.val_lt u, ZMod.natCast_zmod_val u⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨b', hb'⟩ : (q : ℤ) ∣ δ 0 1 - δ 0 0 * (n : ℤ) := by`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[hnu, hb, sub_self]`. Choose the witnesses or unpack the hypotheses as in `⟨d', hd'⟩ : (q : ℤ) ∣ δ 1 1 - δ 1 0 * (n : ℤ) := by`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[hnu, hd, sub_self]`. Establish `h1 : δ 0 0 * d' - b' * δ 1 0 = 1`. Apply `mul_left_cancel₀ hq0` to reduce the goal to its premises.

Take the linear combination `hdet' - δ 0 0 * hd' + δ 1 0 * hb'`. Use `⟨⟨!![δ 0 0, b'; δ 1 0, d'], by rw [Matrix.det_fin_two_of]; exact h1⟩, some ⟨n, hnq⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [d1, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith`.
-/
theorem main : (let d1 : (q : ℕ) → Option (Fin q) → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℤ := @(fun (q : ℕ) (x : Option (Fin q)) ↦ match x with | Option.none => !![(↑q : ℤ), (0 : ℤ); (0 : ℤ), (1 : ℤ)] | Option.some u => !![(1 : ℤ), (↑(↑u : ℕ) : ℤ); (0 : ℤ), (↑q : ℤ)]); ∀ {q : ℕ}, Nat.Prime q → ∀ (δ : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℤ), Matrix.det δ = (↑q : ℤ) → ∃ (γ : Matrix.SpecialLinearGroup (Fin (2 : ℕ)) ℤ) (y : Option (Fin q)), δ = (↑γ : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℤ) * d1 q y) := by
  intro d1 q hq δ hdet
  have : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hdet' : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = q := by rw [← hdet, Matrix.det_fin_two]
  by_cases hdiv : (q : ℤ) ∣ δ 0 0 ∧ (q : ℤ) ∣ δ 1 0
  ·
    obtain ⟨⟨a', ha'⟩, ⟨c', hc'⟩⟩ := hdiv
    have h1 : a' * δ 1 1 - δ 0 1 * c' = 1 := by
      apply mul_left_cancel₀ hq0
      linear_combination hdet' - δ 1 1 * ha' + δ 0 1 * hc'
    refine ⟨⟨!![a', δ 0 1; c', δ 1 1], by rw [Matrix.det_fin_two_of]; exact h1⟩, none, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d1, Matrix.mul_apply, Fin.sum_univ_two, ha', hc'] <;> ring
  ·
    have h0 : (δ 0 0 : ZMod q) * δ 1 1 - δ 0 1 * δ 1 0 = 0 := by
      have := congrArg (Int.cast : ℤ → ZMod q) hdet'
      push_cast at this
      rw [this, ZMod.natCast_self]
    have hn : ¬ ((δ 0 0 : ZMod q) = 0 ∧ (δ 1 0 : ZMod q) = 0) := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨u, hb, hd⟩ := exists_mul_of_det_zero (δ 0 0 : ZMod q) (δ 0 1) (δ 1 0) (δ 1 1) h0 hn
    obtain ⟨n, hnq, hnu⟩ : ∃ n : ℕ, n < q ∧ (n : ZMod q) = u :=
      ⟨u.val, ZMod.val_lt u, ZMod.natCast_zmod_val u⟩
    obtain ⟨b', hb'⟩ : (q : ℤ) ∣ δ 0 1 - δ 0 0 * (n : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hnu, hb, sub_self]
    obtain ⟨d', hd'⟩ : (q : ℤ) ∣ δ 1 1 - δ 1 0 * (n : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hnu, hd, sub_self]
    have h1 : δ 0 0 * d' - b' * δ 1 0 = 1 := by
      apply mul_left_cancel₀ hq0
      linear_combination hdet' - δ 0 0 * hd' + δ 1 0 * hb'
    refine ⟨⟨!![δ 0 0, b'; δ 1 0, d'], by rw [Matrix.det_fin_two_of]; exact h1⟩,
      some ⟨n, hnq⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d1, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

end GlobalTheory.DetZeroFactorization
