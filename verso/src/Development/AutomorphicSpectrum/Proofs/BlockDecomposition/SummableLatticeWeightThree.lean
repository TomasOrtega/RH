import Mathlib

open Filter Topology

namespace GlobalTheory.CompanionTheory.MajSum

/- English proof (translation)
Use `Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hs) ?_` and prove the remaining obligations. Establish `hcof : ({0} : Set ℤ)ᶜ ∈ cofinite` using `(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite`. Establish `hev : ∀ᶠ m : ℤ in cofinite, ‖((1 + |(m : ℝ)|) ^ s)⁻¹‖ ≤ |(m : ℝ)| ^ (-s)` using `by filter_upwards [hcof] with m hm`. Establish `hm' : m ≠ 0` using `by simpa using hm`. Establish `hm0 : 0 < |(m : ℝ)|` using `abs_pos.2 (by exact_mod_cast hm')`.

Establish `hpos : 0 < 1 + |(m : ℝ)|` using `by linarith`. Rewrite using `[Real.norm_of_nonneg (inv_nonneg.2 (Real.rpow_nonneg hpos.le s)), Real.rpow_neg hm0.le]`. Conclude with `inv_anti₀ (Real.rpow_pos_of_pos hm0 s) (Real.rpow_le_rpow hm0.le (by linarith) (by linarith))`. Simplify `hev` using `[Filter.eventually_cofinite]`.
-/
lemma summable_one_add_abs_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun m : ℤ => ((1 + |(m : ℝ)|) ^ s)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hs) ?_
  have hcof : ({0} : Set ℤ)ᶜ ∈ cofinite := (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite
  have hev : ∀ᶠ m : ℤ in cofinite, ‖((1 + |(m : ℝ)|) ^ s)⁻¹‖ ≤ |(m : ℝ)| ^ (-s) := by
    filter_upwards [hcof] with m hm
    have hm' : m ≠ 0 := by simpa using hm
    have hm0 : 0 < |(m : ℝ)| := abs_pos.2 (by exact_mod_cast hm')
    have hpos : 0 < 1 + |(m : ℝ)| := by linarith
    rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.rpow_nonneg hpos.le s)), Real.rpow_neg hm0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hm0 s)
      (Real.rpow_le_rpow hm0.le (by linarith) (by linarith))
  simpa [Filter.eventually_cofinite] using hev

/- English proof (translation)
Establish `hc0 : 0 < c` using `by linarith`. Establish `hX : 0 < 1 + x` using `by linarith`. Establish `hY : 0 < 1 + y` using `by linarith`. Establish `hZ : 0 < 1 + z` using `by linarith`. Establish `hS : 0 < 1 + x + y` using `by linarith`.

Establish `h1 : (1 + x) ^ (3 / 2 : ℝ) * (1 + y) ^ (3 / 2 : ℝ) ≤ (1 + x + y) ^ 3`. Rewrite using `[← Real.mul_rpow hX.le hY.le]`. Establish `hle : (1 + x) * (1 + y) ≤ (1 + x + y) ^ 2` using `by nlinarith [mul_nonneg hx hy]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast (1 + x + y) 2, ← Real.rpow_mul hS.le, ← Real.rpow_natCast (1 + x + y) 3]`.

Evaluate the numerical expressions. Establish `h2 : 1 + x + y ≤ c * (1 + x / c + y / c)`. Establish `: c * (1 + x / c + y / c) = c + x + y` using `by field_simp`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3 : 1 + z ≤ c * (1 + z / c)`. Establish `: c * (1 + z / c) = c + z` using `by field_simp`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP : 0 < 1 + x / c + y / c` using `by positivity`.

Establish `hQ : 0 < 1 + z / c` using `by positivity`. Establish `h4 : (1 + x + y) ^ 3 ≤ (c * (1 + x / c + y / c)) ^ 3` using `pow_le_pow_left₀ hS.le h2 3`. Establish `h5 : (1 + z) ^ 2 ≤ (c * (1 + z / c)) ^ 2` using `pow_le_pow_left₀ hZ.le h3 2`. Establish `hA : 0 < (1 + x) ^ (3 / 2 : ℝ)` using `Real.rpow_pos_of_pos hX _`. Establish `hB : 0 < (1 + y) ^ (3 / 2 : ℝ)` using `Real.rpow_pos_of_pos hY _`.

Establish `hC : 0 < (1 + z) ^ (2 : ℝ)` using `Real.rpow_pos_of_pos hZ _`. Establish `hC' : (1 + z) ^ (2 : ℝ) = (1 + z) ^ 2`. Rewrite using `[← Real.rpow_natCast (1 + z) 2]`. Evaluate the numerical expressions. Establish `key : (1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)) ≤ c ^ 5 * ((1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2)`.

Rewrite using `[hC', ← mul_assoc]`. Combine the equalities or inequalities in the displayed calculation. Establish `hD : 0 < (1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2` using `by positivity`. Establish `hE : 0 < (1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ))`. Check the signs of the components of the expression.

Establish `hinv : ((1 + x) ^ (3 / 2 : ℝ))⁻¹ * (((1 + y) ^ (3 / 2 : ℝ))⁻¹ * ((1 + z) ^ (2 : ℝ))⁻¹) = ((1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)))⁻¹`. Rewrite using `[mul_inv, mul_inv]`. Rewrite using `[hinv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hD hE]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma term_le {x y z c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hc : 1 ≤ c) :
    ((1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2)⁻¹ ≤
      c ^ 5 * (((1 + x) ^ (3 / 2 : ℝ))⁻¹ * (((1 + y) ^ (3 / 2 : ℝ))⁻¹ * ((1 + z) ^ (2 : ℝ))⁻¹)) := by
  have hc0 : 0 < c := by linarith
  have hX : 0 < 1 + x := by linarith
  have hY : 0 < 1 + y := by linarith
  have hZ : 0 < 1 + z := by linarith
  have hS : 0 < 1 + x + y := by linarith
  have h1 : (1 + x) ^ (3 / 2 : ℝ) * (1 + y) ^ (3 / 2 : ℝ) ≤ (1 + x + y) ^ 3 := by
    rw [← Real.mul_rpow hX.le hY.le]
    have hle : (1 + x) * (1 + y) ≤ (1 + x + y) ^ 2 := by nlinarith [mul_nonneg hx hy]
    calc ((1 + x) * (1 + y)) ^ (3 / 2 : ℝ)
        ≤ ((1 + x + y) ^ 2) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = (1 + x + y) ^ 3 := by
          rw [← Real.rpow_natCast (1 + x + y) 2, ← Real.rpow_mul hS.le,
            ← Real.rpow_natCast (1 + x + y) 3]
          norm_num
  have h2 : 1 + x + y ≤ c * (1 + x / c + y / c) := by
    have : c * (1 + x / c + y / c) = c + x + y := by field_simp
    rw [this]; linarith
  have h3 : 1 + z ≤ c * (1 + z / c) := by
    have : c * (1 + z / c) = c + z := by field_simp
    rw [this]; linarith
  have hP : 0 < 1 + x / c + y / c := by positivity
  have hQ : 0 < 1 + z / c := by positivity
  have h4 : (1 + x + y) ^ 3 ≤ (c * (1 + x / c + y / c)) ^ 3 :=
    pow_le_pow_left₀ hS.le h2 3
  have h5 : (1 + z) ^ 2 ≤ (c * (1 + z / c)) ^ 2 := pow_le_pow_left₀ hZ.le h3 2
  have hA : 0 < (1 + x) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hX _
  have hB : 0 < (1 + y) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hY _
  have hC : 0 < (1 + z) ^ (2 : ℝ) := Real.rpow_pos_of_pos hZ _
  have hC' : (1 + z) ^ (2 : ℝ) = (1 + z) ^ 2 := by
    rw [← Real.rpow_natCast (1 + z) 2]; norm_num
  have key : (1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)) ≤
      c ^ 5 * ((1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2) := by
    rw [hC', ← mul_assoc]
    calc (1 + x) ^ (3 / 2 : ℝ) * (1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ 2
        ≤ (c * (1 + x / c + y / c)) ^ 3 * (c * (1 + z / c)) ^ 2 :=
          mul_le_mul (h1.trans h4) h5 (by positivity) (by positivity)
      _ = c ^ 5 * ((1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2) := by ring
  have hD : 0 < (1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2 := by positivity
  have hE : 0 < (1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)) := by
    positivity
  have hinv : ((1 + x) ^ (3 / 2 : ℝ))⁻¹ * (((1 + y) ^ (3 / 2 : ℝ))⁻¹ * ((1 + z) ^ (2 : ℝ))⁻¹) =
      ((1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)))⁻¹ := by
    rw [mul_inv, mul_inv]
  rw [hinv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hD hE]
  linarith

/- English proof (translation)
Establish `hM0 : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Use `⟨((M : ℚ) * q).num, ?_⟩` and prove the remaining obligations. Rewrite using `[Rat.coe_int_num_of_den_eq_one h]`. Clear the denominators using the available nonvanishing facts.
-/
lemma exists_int_of_den_eq_one {M : ℕ} (hM : 0 < M) {q : ℚ} (h : ((M : ℚ) * q).den = 1) :
    ∃ m : ℤ, (m : ℚ) / M = q := by
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨((M : ℚ) * q).num, ?_⟩
  rw [Rat.coe_int_num_of_den_eq_one h]
  field_simp

/- English proof (translation)
Introduce `M hM`. Establish `hM0 : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hMR : (1 : ℝ) ≤ M` using `by exact_mod_cast hM`. Set `g : ℤ × ℤ × ℤ → ℚ × ℚ × ℚ` to `fun t => ((t.1 : ℚ) / M, (t.2.1 : ℚ) / M, (t.2.2 : ℚ) / M)`. Establish `hdiv : ∀ a b : ℤ, (a : ℚ) / M = (b : ℚ) / M → a = b`.

Introduce `a b hab`. Establish `: (a : ℚ) = b`. Clear denominators, using `at hab` for the nonvanishing conditions. Conclude with `hab`. Conclude with `this` after adjusting the coercions.

Establish `hg : Function.Injective g`. Introduce and unpack `⟨a, b, c⟩ ⟨a', b', c'⟩ h`. Simplify using `only [g, Prod.mk.injEq] at h`. Take `⟨h1, h2, h3⟩` from `h`. Rewrite using `[hdiv _ _ h1, hdiv _ _ h2, hdiv _ _ h3]`.

Establish `hden : ∀ a : ℤ, ((M : ℚ) * ((a : ℚ) / M)).den = 1`. Introduce `a`. Rewrite using `[mul_div_cancel₀ _ hM0]`. Conclude with `Rat.den_intCast a`. Use `(hg.summable_iff ?_).1 ?_` and prove the remaining obligations.

Introduce and unpack `⟨p, q, r⟩ hx`. Use `if_neg ?_` and prove the remaining obligations. Introduce and unpack `⟨h1, h2, h3⟩`. Take `⟨a, rfl⟩` from `exists_int_of_den_eq_one hM h1`. Take `⟨b, rfl⟩` from `exists_int_of_den_eq_one hM h2`.

Take `⟨c, rfl⟩` from `exists_int_of_den_eq_one hM h3`. Conclude with `hx ⟨(a, b, c), rfl⟩`. Establish `hA` using `summable_one_add_abs_rpow (s := 3 / 2) (by norm_num)`. Establish `hC` using `summable_one_add_abs_rpow (s := 2) (by norm_num)`. Establish `hnA : 0 ≤ fun m : ℤ => ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹` using `fun m => by`.

Check the signs of the components of the expression. Establish `hnC : 0 ≤ fun m : ℤ => ((1 + |(m : ℝ)|) ^ (2 : ℝ))⁻¹` using `fun m => by`. Check the signs of the components of the expression. Establish `hBC` using `hA.mul_of_nonneg hC hnA hnC`. Establish `hnBC : 0 ≤ fun t : ℤ × ℤ => ((1 + |(t.1 : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ * ((1 + |(t.2 : ℝ)|) ^ (2 : ℝ))⁻¹` using `fun t => by`.

Check the signs of the components of the expression. Establish `hABC` using `(hA.mul_of_nonneg hBC hnA hnBC).mul_left ((M : ℝ) ^ 5)`. Use `Summable.of_nonneg_of_le ?_ ?_ hABC` and prove the remaining obligations. Introduce and unpack `⟨a, b, c⟩`. Simplify using `only [Function.comp, g]`.

Apply the tactic sequence `split_ifs <;> positivity`. Introduce and unpack `⟨a, b, c⟩`. Simplify using `only [Function.comp, g]`. Rewrite using `[if_pos ⟨hden a, hden b, hden c⟩]`. Establish `hcast : ∀ u : ℤ, |(((u : ℚ) / M : ℚ) : ℝ)| = |(u : ℝ)| / M`.

Introduce `u`. Use `push_cast`. Rewrite using `[abs_div, Nat.abs_cast]`. Rewrite using `[hcast a, hcast b, hcast c]`. Conclude with `term_le (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hMR`.
-/
theorem summable_lattice_majorant :
    ∀ M : ℕ, 0 < M → Summable (fun p : ℚ × ℚ × ℚ =>
      if ((M : ℚ) * p.1).den = 1 ∧ ((M : ℚ) * p.2.1).den = 1 ∧ ((M : ℚ) * p.2.2).den = 1 then
        ((1 + |(p.1 : ℝ)| + |(p.2.1 : ℝ)|) ^ 3 * (1 + |(p.2.2 : ℝ)|) ^ 2)⁻¹ else (0 : ℝ)) := by
  intro M hM
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let g : ℤ × ℤ × ℤ → ℚ × ℚ × ℚ :=
    fun t => ((t.1 : ℚ) / M, (t.2.1 : ℚ) / M, (t.2.2 : ℚ) / M)
  have hdiv : ∀ a b : ℤ, (a : ℚ) / M = (b : ℚ) / M → a = b := by
    intro a b hab
    have : (a : ℚ) = b := by
      field_simp at hab
      exact hab
    exact_mod_cast this
  have hg : Function.Injective g := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [hdiv _ _ h1, hdiv _ _ h2, hdiv _ _ h3]
  have hden : ∀ a : ℤ, ((M : ℚ) * ((a : ℚ) / M)).den = 1 := by
    intro a
    rw [mul_div_cancel₀ _ hM0]
    exact Rat.den_intCast a
  refine (hg.summable_iff ?_).1 ?_
  · rintro ⟨p, q, r⟩ hx
    refine if_neg ?_
    rintro ⟨h1, h2, h3⟩
    obtain ⟨a, rfl⟩ := exists_int_of_den_eq_one hM h1
    obtain ⟨b, rfl⟩ := exists_int_of_den_eq_one hM h2
    obtain ⟨c, rfl⟩ := exists_int_of_den_eq_one hM h3
    exact hx ⟨(a, b, c), rfl⟩
  · have hA := summable_one_add_abs_rpow (s := 3 / 2) (by norm_num)
    have hC := summable_one_add_abs_rpow (s := 2) (by norm_num)
    have hnA : 0 ≤ fun m : ℤ => ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ := fun m => by
      positivity
    have hnC : 0 ≤ fun m : ℤ => ((1 + |(m : ℝ)|) ^ (2 : ℝ))⁻¹ := fun m => by
      positivity
    have hBC := hA.mul_of_nonneg hC hnA hnC
    have hnBC : 0 ≤ fun t : ℤ × ℤ =>
        ((1 + |(t.1 : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ * ((1 + |(t.2 : ℝ)|) ^ (2 : ℝ))⁻¹ := fun t => by
      positivity
    have hABC := (hA.mul_of_nonneg hBC hnA hnBC).mul_left ((M : ℝ) ^ 5)
    refine Summable.of_nonneg_of_le ?_ ?_ hABC
    · rintro ⟨a, b, c⟩
      simp only [Function.comp, g]
      split_ifs <;> positivity
    · rintro ⟨a, b, c⟩
      simp only [Function.comp, g]
      rw [if_pos ⟨hden a, hden b, hden c⟩]
      have hcast : ∀ u : ℤ, |(((u : ℚ) / M : ℚ) : ℝ)| = |(u : ℝ)| / M := by
        intro u
        push_cast
        rw [abs_div, Nat.abs_cast]
      rw [hcast a, hcast b, hcast c]
      exact term_le (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hMR

end GlobalTheory.CompanionTheory.MajSum
