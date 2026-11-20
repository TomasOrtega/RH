import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem qzB_smul_mk (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) (q : ℚ_[l]) :
    x • QZ.mk l q = QZ.mk l ((x : ℚ_[l]) * q) := rfl

/- English proof (translation)
The claim follows from `Submodule.Quotient.mk_eq_zero (ZlSub l)`.
-/
private theorem qzB_mk_eq_zero (l : ℕ) [Fact l.Prime] (q : ℚ_[l]) :
    QZ.mk l q = 0 ↔ ∃ z : ℤ_[l], (z : ℚ_[l]) = q :=
  Submodule.Quotient.mk_eq_zero (ZlSub l)

/- English proof (translation)
The claim follows from `Submodule.Quotient.mk_surjective (ZlSub l) a`.
-/
private theorem qzB_mk_surj (l : ℕ) [Fact l.Prime] (a : QZ l) : ∃ q, QZ.mk l q = a :=
  Submodule.Quotient.mk_surjective (ZlSub l) a

/- English proof (translation)
Introduce `l _`. Establish `hl : l.Prime` using `Fact.out`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Establish `tors : ∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0`. Introduce `x`.

Take `⟨q, rfl⟩` from `qzB_mk_surj l x`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt ‖q‖ hl1`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.cast_smul_eq_nsmul ℤ_[l], qzB_smul_mk, qzB_mk_eq_zero]`. Establish `hpos : (0 : ℝ) < (l : ℝ) ^ k` using `pow_pos (by linarith) k`.

Use `⟨⟨_, ?_⟩, rfl⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast, inv_mul_le_iff₀ hpos, mul_one]`. Conclude with `hk.le`. Use `⟨?_, tors, ?_⟩` and prove the remaining obligations.

Introduce `u hu a`. Take `⟨q, rfl⟩` from `qzB_mk_surj l a`. Establish `hu' : (u : ℚ_[l]) ≠ 0` using `PadicInt.coe_ne_zero.2 hu`. Use `⟨QZ.mk l (q / u), ?_⟩` and prove the remaining obligations. Use `show u • QZ.mk l (q / u) = QZ.mk l q`.

Rewrite using `[qzB_smul_mk, mul_div_cancel₀ q hu']`. Introduce `h2 x hx`. Take `⟨k, hk⟩` from `tors x`. Establish `hc : IsCoprime (2 : ℤ) ((l ^ k : ℕ) : ℤ)`. Rewrite using `[show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Nat.isCoprime_iff_coprime]`.

Conclude with `Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm h2))`. Take `⟨a, b, hab⟩` from `hc`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[add_smul, mul_smul, mul_smul]`. Use `norm_cast`.

Use `_ = 0 := by rw [hx, hk, smul_zero, smul_zero, add_zero]`.
-/
theorem UpperTheory.V.Kum.qzBasic :
    ∀ (l : ℕ) [Fact l.Prime], (∀ u : ℤ_[l], u ≠ 0 → Function.Surjective fun x : QZ l => u • x) ∧ (∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0) ∧ (l ≠ 2 → ∀ x : QZ l, 2 • x = 0 → x = 0) := by
  intro l _
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have tors : ∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0 := by
    intro x
    obtain ⟨q, rfl⟩ := qzB_mk_surj l x
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hl1
    refine ⟨k, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], qzB_smul_mk, qzB_mk_eq_zero]
    have hpos : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (by linarith) k
    refine ⟨⟨_, ?_⟩, rfl⟩
    push_cast
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast, inv_mul_le_iff₀ hpos, mul_one]
    exact hk.le
  refine ⟨?_, tors, ?_⟩
  · intro u hu a
    obtain ⟨q, rfl⟩ := qzB_mk_surj l a
    have hu' : (u : ℚ_[l]) ≠ 0 := PadicInt.coe_ne_zero.2 hu
    refine ⟨QZ.mk l (q / u), ?_⟩
    show u • QZ.mk l (q / u) = QZ.mk l q
    rw [qzB_smul_mk, mul_div_cancel₀ q hu']
  · intro h2 x hx
    obtain ⟨k, hk⟩ := tors x
    have hc : IsCoprime (2 : ℤ) ((l ^ k : ℕ) : ℤ) := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm h2))
    obtain ⟨a, b, hab⟩ := hc
    calc x = (1 : ℤ) • x := (one_smul ℤ x).symm
      _ = (a * 2 + b * ((l ^ k : ℕ) : ℤ)) • x := by rw [hab]
      _ = a • ((2 : ℕ) • x) + b • ((l ^ k) • x) := by
        rw [add_smul, mul_smul, mul_smul]
        norm_cast
      _ = 0 := by rw [hx, hk, smul_zero, smul_zero, add_zero]
