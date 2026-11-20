import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ConvolutionNonnegOfDivisors

open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Use `(LSeriesSummable_congr s (fun {n} hn => ?_)).mpr (χ.LSeriesSummable_of_one_lt_re hs)` and prove the remaining obligations. Simplify using `[toArithmeticFunction, hn]`.
-/
lemma dirichlet_character_lseries_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable ⇑(toArithmeticFunction (fun m : ℕ => χ (m : ZMod N))) s := by
  refine (LSeriesSummable_congr s (fun {n} hn => ?_)).mpr (χ.LSeriesSummable_of_one_lt_re hs)
  simp [toArithmeticFunction, hn]

/- English proof (translation)
Rewrite using `[DirichletCharacter.LFunction_eq_LSeries χ hs]`. Conclude with `LSeries_congr (fun {n} hn => by simp [toArithmeticFunction, hn]) s`.
-/
lemma dirichlet_character_lseries_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries ⇑(toArithmeticFunction (fun m : ℕ => χ (m : ZMod N))) s = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact LSeries_congr (fun {n} hn => by simp [toArithmeticFunction, hn]) s

set_option backward.isDefEq.respectTransparency.types false in
/- English proof (translation)
Establish `h1 : LSeriesSummable ⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s`. Use `ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs` as an intermediate fact. Conclude with `(LSeriesSummable_congr s (fun {n} hn => by simp [hn])).mp this`. Rewrite using `[DirichletCharacter.zetaMul, ArithmeticFunction.LSeries_mul' h1 (dirichlet_character_lseries_summable χ hs), dirichlet_character_lseries_eq χ hs]`. Use `congr 1`.

Rewrite using `[← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]`. Conclude with `LSeries_congr (fun {n} hn => by simp [hn]) s`.
-/
lemma lseries_zetaMul_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (DirichletCharacter.zetaMul χ) s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have h1 : LSeriesSummable ⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    have := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
    exact (LSeriesSummable_congr s (fun {n} hn => by simp [hn])).mp this
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.LSeries_mul' h1 (dirichlet_character_lseries_summable χ hs),
    dirichlet_character_lseries_eq χ hs]
  congr 1
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact LSeries_congr (fun {n} hn => by simp [hn]) s

/- English proof (translation)
Introduce `q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 hψ`. Use `set f : ArithmeticFunction ℂ := DirichletCharacter.zetaMul χ₁ * (toArithmeticFunction (fun m : ℕ => χ₂ (m : ZMod q₂)) * toArithmeticFunction (fun m : ℕ => ψ (m : ZMod (q₁ * q₂)))) with hf`. Establish `hvals : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → ∀ x, χ x = 0 ∨ χ x = 1 ∨ χ x = -1`. Introduce `N χ hχ x`. Distinguish the cases in `hx : IsUnit x`.

Establish `h` using `congrArg (fun φ : DirichletCharacter ℂ N => φ x) hχ`. Simplify using `only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hx] at h`. Establish `h' : χ x * χ x = 1` using `by rw [← sq]; exact h`. Break down `(mul_self_eq_one_iff).mp h' with h' | h'` into its components or cases. Conclude with `Or.inr (Or.inl h')`.

Conclude with `Or.inr (Or.inr h')`. Conclude with `Or.inl (MulChar.map_nonunit χ hx)`. Establish `hmul : f.IsMultiplicative` using `(DirichletCharacter.isMultiplicative_zetaMul χ₁).mul ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ₂).mul (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))`. Establish `hswap : f = DirichletCharacter.zetaMul χ₂ * (toArithmeticFunction (fun m : ℕ => χ₁ (m : ZMod q₁)) * toArithmeticFunction (fun m : ℕ => ψ (m : ZMod (q₁ * q₂))))`. Simplify using `only [hf, DirichletCharacter.zetaMul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hψ' : ∀ n : ℕ, ψ (n : ZMod (q₁ * q₂)) = χ₂ (n : ZMod q₂) * χ₁ (n : ZMod q₁)`. Introduce `n`. Rewrite using `[hψ n, mul_comm]`. Establish `hpp : ∀ p k : ℕ, p.Prime → 0 ≤ f (p ^ k)`.

Introduce `p k hp`. Break down `hvals χ₂ h2 (p : ZMod q₂) with h | h | h` into its components or cases. Conclude with `prime_power_coefficient_nonneg h1 hψ hp (Or.inl h) k`. Conclude with `prime_power_coefficient_nonneg h1 hψ hp (Or.inr (Or.inl h)) k`. Break down `hvals χ₁ h1 (p : ZMod q₁) with h' | h' | h'` into its components or cases.

Rewrite using `[hswap]`. Conclude with `prime_power_coefficient_nonneg h2 hψ' hp (Or.inl h') k`. Rewrite using `[hswap]`. Conclude with `prime_power_coefficient_nonneg h2 hψ' hp (Or.inr (Or.inl h')) k`. Conclude with `prime_power_coefficient_nonneg h1 hψ hp (Or.inr (Or.inr ⟨h, h'⟩)) k`.

Establish `hnn : ∀ n, 0 ≤ f n`. Introduce `n`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[ArithmeticFunction.IsMultiplicative.multiplicative_factorization f hmul hn, Finsupp.prod]`.

Conclude with `Finset.prod_nonneg fun p hp => hpp p _ (Nat.prime_of_mem_primeFactors (by simpa using hp))`. Establish `hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable (⇑f) s` using `fun s hs => ArithmeticFunction.LSeriesSummable_mul (DirichletCharacter.LSeriesSummable_zetaMul χ₁ hs) (ArithmeticFunction.LSeriesSummable_mul (dirichlet_character_lseries_summable χ₂ hs) (dirichlet_character_lseries_summable ψ hs))`. Use `⟨⇑f, hnn, hmul.map_one, ?_, ?_⟩` and prove the remaining obligations. Use `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := ⇑f) (x := 1) (fun y hy => hsum y (by simpa using hy))` as an intermediate fact. Simplify using `using this`.

Introduce `s hs`. Rewrite using `[Fbq, ArithmeticFunction.LSeries_mul' (DirichletCharacter.LSeriesSummable_zetaMul χ₁ hs) (ArithmeticFunction.LSeriesSummable_mul (dirichlet_character_lseries_summable χ₂ hs) (dirichlet_character_lseries_summable ψ hs)), ArithmeticFunction.LSeries_mul' (dirichlet_character_lseries …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dirichlet_product_coefficients : BqCoeff := by
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 hψ
  set f : ArithmeticFunction ℂ := DirichletCharacter.zetaMul χ₁ *
    (toArithmeticFunction (fun m : ℕ => χ₂ (m : ZMod q₂)) *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod (q₁ * q₂)))) with hf

  have hvals : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 →
      ∀ x, χ x = 0 ∨ χ x = 1 ∨ χ x = -1 := by
    intro N χ hχ x
    by_cases hx : IsUnit x
    · have h := congrArg (fun φ : DirichletCharacter ℂ N => φ x) hχ
      simp only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hx] at h
      have h' : χ x * χ x = 1 := by rw [← sq]; exact h
      rcases (mul_self_eq_one_iff).mp h' with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · exact Or.inl (MulChar.map_nonunit χ hx)
  have hmul : f.IsMultiplicative :=
    (DirichletCharacter.isMultiplicative_zetaMul χ₁).mul
      ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ₂).mul
        (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))
  have hswap : f = DirichletCharacter.zetaMul χ₂ *
      (toArithmeticFunction (fun m : ℕ => χ₁ (m : ZMod q₁)) *
        toArithmeticFunction (fun m : ℕ => ψ (m : ZMod (q₁ * q₂)))) := by
    simp only [hf, DirichletCharacter.zetaMul]
    ring
  have hψ' : ∀ n : ℕ, ψ (n : ZMod (q₁ * q₂)) = χ₂ (n : ZMod q₂) * χ₁ (n : ZMod q₁) := by
    intro n
    rw [hψ n, mul_comm]
  have hpp : ∀ p k : ℕ, p.Prime → 0 ≤ f (p ^ k) := by
    intro p k hp
    rcases hvals χ₂ h2 (p : ZMod q₂) with h | h | h
    · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inl h) k
    · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inr (Or.inl h)) k
    · rcases hvals χ₁ h1 (p : ZMod q₁) with h' | h' | h'
      · rw [hswap]; exact prime_power_coefficient_nonneg h2 hψ' hp (Or.inl h') k
      · rw [hswap]; exact prime_power_coefficient_nonneg h2 hψ' hp (Or.inr (Or.inl h')) k
      · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inr (Or.inr ⟨h, h'⟩)) k
  have hnn : ∀ n, 0 ≤ f n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization f hmul hn, Finsupp.prod]
      exact Finset.prod_nonneg fun p hp =>
        hpp p _ (Nat.prime_of_mem_primeFactors (by simpa using hp))
  have hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable (⇑f) s := fun s hs =>
    ArithmeticFunction.LSeriesSummable_mul (DirichletCharacter.LSeriesSummable_zetaMul χ₁ hs)
      (ArithmeticFunction.LSeriesSummable_mul (dirichlet_character_lseries_summable χ₂ hs)
        (dirichlet_character_lseries_summable ψ hs))
  refine ⟨⇑f, hnn, hmul.map_one, ?_, ?_⟩
  · have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := ⇑f) (x := 1)
      (fun y hy => hsum y (by simpa using hy))
    simpa using this
  · intro s hs
    rw [Fbq, ArithmeticFunction.LSeries_mul' (DirichletCharacter.LSeriesSummable_zetaMul χ₁ hs)
      (ArithmeticFunction.LSeriesSummable_mul (dirichlet_character_lseries_summable χ₂ hs)
        (dirichlet_character_lseries_summable ψ hs)),
      ArithmeticFunction.LSeries_mul' (dirichlet_character_lseries_summable χ₂ hs) (dirichlet_character_lseries_summable ψ hs),
      lseries_zetaMul_eq χ₁ hs, dirichlet_character_lseries_eq χ₂ hs, dirichlet_character_lseries_eq ψ hs]
    ring

end Formalism.ZeroFreeDirichlet
