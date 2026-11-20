import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob

open UpperTheory.V.Z.Kato.Joint

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]`. Conclude with `h`.
-/
private lemma smNz_unit {l : ℕ} [Fact l.Prime] {n : ℕ} (h : ¬ l ∣ n) : IsUnit (n : ZMod l) := by
  rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  exact h

/- English proof (translation)
Establish `hu` using `smNz_unit (l := l) h`. Use `χ.unit_norm_eq_one hu.unit` as an intermediate fact. Rewrite `this` using `[IsUnit.unit_spec]`. Then use the resulting hypothesis.
-/
private lemma smNz_norm {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) {n : ℕ} (h : ¬ l ∣ n) :
    ‖χ (n : ZMod l)‖ = 1 := by
  have hu := smNz_unit (l := l) h
  have := χ.unit_norm_eq_one hu.unit
  rwa [IsUnit.unit_spec] at this

/- English proof (translation)
Introduce `l _ ι e N c d ψ a b hN hN0 hc0 hd0 hc hd ha hce hdb`. Establish `hp : l.Prime` using `Fact.out`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `intro i fin_cases i <;> simp [smT, hp.dvd_mul, hN, hc, hd]`. Simplify using `only [Fin.sum_univ_four, smB, smT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_mul, map_neg, map_pow, map_zpow₀, map_natCast, RingEquiv.apply_symm_apply, Nat.cast_mul, MulChar.inv_apply_eq_inv', mu …`.

Establish `hC : (c : ℂ) ≠ 0` using `by exact_mod_cast hc0.ne'`. Establish `hD : (d : ℂ) ≠ 0` using `by exact_mod_cast hd0.ne'`. Establish `hNc : (N : ℂ) ≠ 0` using `by exact_mod_cast hN0.ne'`. Establish `hψN : ψ (N : ZMod l) ≠ 0`. Introduce `h0`.

Use `smNz_norm ψ hN` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`. Establish `hψc : ψ (c : ZMod l) ≠ 0`. Introduce `h0`.

Use `smNz_norm ψ hc` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`. Establish `hCe : (c : ℂ) ^ e ≠ 0` using `pow_ne_zero _ hC`. Establish `hw : (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) * (c : ℂ) ^ e = (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹`.

Rewrite using `[← zpow_natCast (c : ℂ) e, ← zpow_add₀ hC, ← zpow_natCast (c : ℂ) 2, ← zpow_neg, ← zpow_add₀ hC]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set w := (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) with hwdef`.

Establish `hfac : (c : ℂ) ^ 2 * (d : ℂ) ^ 2 * (ψ (N : ZMod l))⁻¹ * (N : ℂ) ^ e + -(w * a * (d : ℂ) ^ 2) * (ψ (N : ZMod l) * ψ (c : ZMod l))⁻¹ * ((N : ℂ) ^ e * (c : ℂ) ^ e) + -((c : ℂ) ^ 2 * ((d : ℂ) * b)) * (ψ (N : ZMod l) * ψ (d : ZMod l))⁻¹ * ((N : ℂ) ^ e * (d : ℂ) ^ e) + w * a * ((d : ℂ) …`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfac, hw]`. Use `mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNc) (inv_ne_zero hψN)) ?_) ?_` and prove the remaining obligations. Establish `h1 : (c : ℂ) ^ 2 - (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * a * (ψ (c : ZMod l))⁻¹ = (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * ((c : ℂ) ^ e - a * (ψ (c : ZMod l))⁻¹)`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[h1]`. Use `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hC) (inv_ne_zero hCe)) ?_` and prove the remaining obligations. Rewrite using `[sub_ne_zero]`. Apply `hce` to reduce the goal to its premises.

Rewrite using `[norm_mul, norm_inv, ha, smNz_norm ψ hc]`. Evaluate the numerical expressions. Introduce `h0`. Apply `hdb` to reduce the goal to its premises. Rewrite using `[zpow_neg_one, pow_succ]`.

Take the linear combination `h0`.
-/
theorem UpperTheory.V.Z.Kato.Joint.smNz :
    UpperTheory.V.Z.Kato.Joint.SmNz := by
  intro l _ ι e N c d ψ a b hN hN0 hc0 hd0 hc hd ha hce hdb
  have hp : l.Prime := Fact.out
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> simp [smT, hp.dvd_mul, hN, hc, hd]
  · simp only [Fin.sum_univ_four, smB, smT, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_mul,
      map_neg, map_pow, map_zpow₀, map_natCast, RingEquiv.apply_symm_apply, Nat.cast_mul,
      MulChar.inv_apply_eq_inv', mul_pow]
    have hC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have hD : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hψN : ψ (N : ZMod l) ≠ 0 := by
      intro h0
      have := smNz_norm ψ hN
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hψc : ψ (c : ZMod l) ≠ 0 := by
      intro h0
      have := smNz_norm ψ hc
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hCe : (c : ℂ) ^ e ≠ 0 := pow_ne_zero _ hC
    have hw : (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) * (c : ℂ) ^ e = (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ := by
      rw [← zpow_natCast (c : ℂ) e, ← zpow_add₀ hC, ← zpow_natCast (c : ℂ) 2, ← zpow_neg,
        ← zpow_add₀ hC]
      congr 1
      push_cast
      ring
    set w := (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) with hwdef
    have hfac : (c : ℂ) ^ 2 * (d : ℂ) ^ 2 * (ψ (N : ZMod l))⁻¹ * (N : ℂ) ^ e +
        -(w * a * (d : ℂ) ^ 2) * (ψ (N : ZMod l) * ψ (c : ZMod l))⁻¹ * ((N : ℂ) ^ e * (c : ℂ) ^ e) +
        -((c : ℂ) ^ 2 * ((d : ℂ) * b)) * (ψ (N : ZMod l) * ψ (d : ZMod l))⁻¹ * ((N : ℂ) ^ e * (d : ℂ) ^ e) +
        w * a * ((d : ℂ) * b) * (ψ (N : ZMod l) * ψ (c : ZMod l) * ψ (d : ZMod l))⁻¹ *
          ((N : ℂ) ^ e * (c : ℂ) ^ e * (d : ℂ) ^ e) =
        (N : ℂ) ^ e * (ψ (N : ZMod l))⁻¹ *
          ((c : ℂ) ^ 2 - w * (c : ℂ) ^ e * a * (ψ (c : ZMod l))⁻¹) *
          ((d : ℂ) ^ 2 - (d : ℂ) * b * (d : ℂ) ^ e * (ψ (d : ZMod l))⁻¹) := by
      ring
    rw [hfac, hw]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNc) (inv_ne_zero hψN)) ?_) ?_
    · have h1 : (c : ℂ) ^ 2 - (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * a * (ψ (c : ZMod l))⁻¹ =
          (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * ((c : ℂ) ^ e - a * (ψ (c : ZMod l))⁻¹) := by
        field_simp
      rw [h1]
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hC) (inv_ne_zero hCe)) ?_
      rw [sub_ne_zero]
      apply hce
      rw [norm_mul, norm_inv, ha, smNz_norm ψ hc]
      norm_num
    · intro h0
      apply hdb
      rw [zpow_neg_one, pow_succ]
      linear_combination h0
