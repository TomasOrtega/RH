import Mathlib
import Formalism.LandauZeroFreeBounds.Statement

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

/- English proof (translation)
Unfold `Formalism.ZeroFreeDirichlet.InRegion`. Rewrite using `[Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]`. Establish `hZpos : 0 < Z` using `by linarith`. Establish `hq1' : (1 : ℝ) ≤ q` using `by exact_mod_cast hq1`. Establish `h2q : 0 < Real.log ((q : ℝ) * 2)` using `Real.log_pos (by linarith)`.

Establish `hZ3 : Real.log (Z ^ 3) = 3 * Real.log Z` using `by rw [Real.log_pow]; norm_num`. Establish `hle : Real.log ((q : ℝ) * 2) ≤ 3 * Real.log Z`. Rewrite using `[← hZ3]`. Apply `Real.log_le_log (by linarith)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Establish `hdiv : c / 3 / Real.log Z ≤ c / Real.log ((q : ℝ) * 2)`. Rewrite using `[div_div]`. Conclude with `div_le_div_of_nonneg_left hc.le h2q hle`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inRegion_of_lt {c Z β : ℝ} {q : ℕ} (hc : 0 < c) (hZ : 3 ≤ Z) (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Z ^ 2)
    (hβ : 1 - c / 3 / Real.log Z < β) : Formalism.ZeroFreeDirichlet.InRegion c q (β : ℂ) := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  rw [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]
  have hZpos : 0 < Z := by linarith
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have h2q : 0 < Real.log ((q : ℝ) * 2) := Real.log_pos (by linarith)
  have hZ3 : Real.log (Z ^ 3) = 3 * Real.log Z := by rw [Real.log_pow]; norm_num
  have hle : Real.log ((q : ℝ) * 2) ≤ 3 * Real.log Z := by
    rw [← hZ3]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hdiv : c / 3 / Real.log Z ≤ c / Real.log ((q : ℝ) * 2) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le h2q hle
  linarith

/- English proof (translation)
Use `⟨Or.inl ?_, ?_⟩` and prove the remaining obligations. Introduce `h1`. Apply `hχ` to reduce the goal to its premises. Apply `DirichletCharacter.changeLevel_injective h` to reduce the goal to its premises. Rewrite using `[h1, map_one]`.

Rewrite using `[DirichletCharacter.LFunction_changeLevel h χ (Or.inl hχ), hs, zero_mul]`.
-/
theorem isLZero_changeLevel {M q : ℕ} [NeZero M] [NeZero q] (h : M ∣ q) (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1)
    {s : ℂ} (hs : DirichletCharacter.LFunction χ s = 0) :
    Formalism.ZeroFreeDirichlet.IsLZero (DirichletCharacter.changeLevel h χ) s := by
  refine ⟨Or.inl ?_, ?_⟩
  · intro h1
    apply hχ
    apply DirichletCharacter.changeLevel_injective h
    rw [h1, map_one]
  · rw [DirichletCharacter.LFunction_changeLevel h χ (Or.inl hχ), hs, zero_mul]

/- English proof (translation)
Take `⟨c, hc, hzfr⟩` from `hZ`. Use `⟨c / 3, by positivity, ?_⟩` and prove the remaining obligations. Introduce `Z M₁ M₂ _ _ χ₁ χ₂ β₁ β₂ hZ3 hM₁ hM₂ _ _ hne₁ hne₂ hz₁ hz₂ hb₁ hb₂ _ _ n hn`. Use `haveI : NeZero (M₁ * M₂) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩`. Establish `hq1 : 1 ≤ M₁ * M₂` using `Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)`.

Establish `hqZ : ((M₁ * M₂ : ℕ) : ℝ) ≤ Z ^ 2`. Use `push_cast`. Rewrite using `[pow_two]`. Conclude with `mul_le_mul hM₁ hM₂ (Nat.cast_nonneg _) (by linarith)`. Establish `hr₁` using `inRegion_of_lt hc hZ3 hq1 hqZ hb₁`.

Establish `hr₂` using `inRegion_of_lt hc hZ3 hq1 hqZ hb₂`. Establish `hL₁` using `isLZero_changeLevel (dvd_mul_right M₁ M₂) χ₁ hne₁ hz₁`. Establish `hL₂` using `isLZero_changeLevel (dvd_mul_left M₂ M₁) χ₂ hne₂ hz₂`. Take `⟨-, -, -, -, huniq⟩` from `hzfr (M₁ * M₂) _ _ hr₁ hL₁`. Establish `heq` using `(huniq _ _ hr₂ hL₂).1`.

Establish `hv` using `congrArg (fun ψ : DirichletCharacter ℂ (M₁ * M₂) => ψ ((ZMod.unitOfCoprime n hn : (ZMod (M₁ * M₂))ˣ) : ZMod (M₁ * M₂))) heq`. Rewrite `hv` using `[DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_left M₂ M₁), ZMod.cast_natCast (dvd_mul_right M₁ M₂)]`. Conclude with `hv.symm`.
-/
theorem page_across (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (Z : ℝ) (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂] (χ₁ : DirichletCharacter ℂ M₁)
      (χ₂ : DirichletCharacter ℂ M₂) (β₁ β₂ : ℝ), 3 ≤ Z → (M₁ : ℝ) ≤ Z → (M₂ : ℝ) ≤ Z →
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 →
      DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0 →
      1 - c₀ / Real.log Z < β₁ → 1 - c₀ / Real.log Z < β₂ → β₁ < 1 → β₂ < 1 →
      ∀ n : ℕ, n.Coprime (M₁ * M₂) → χ₁ (n : ZMod M₁) = χ₂ (n : ZMod M₂) := by
  obtain ⟨c, hc, hzfr⟩ := hZ
  refine ⟨c / 3, by positivity, ?_⟩
  intro Z M₁ M₂ _ _ χ₁ χ₂ β₁ β₂ hZ3 hM₁ hM₂ _ _ hne₁ hne₂ hz₁ hz₂ hb₁ hb₂ _ _ n hn
  haveI : NeZero (M₁ * M₂) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hq1 : 1 ≤ M₁ * M₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hqZ : ((M₁ * M₂ : ℕ) : ℝ) ≤ Z ^ 2 := by
    push_cast
    rw [pow_two]
    exact mul_le_mul hM₁ hM₂ (Nat.cast_nonneg _) (by linarith)

  have hr₁ := inRegion_of_lt hc hZ3 hq1 hqZ hb₁
  have hr₂ := inRegion_of_lt hc hZ3 hq1 hqZ hb₂
  have hL₁ := isLZero_changeLevel (dvd_mul_right M₁ M₂) χ₁ hne₁ hz₁
  have hL₂ := isLZero_changeLevel (dvd_mul_left M₂ M₁) χ₂ hne₂ hz₂
  obtain ⟨-, -, -, -, huniq⟩ := hzfr (M₁ * M₂) _ _ hr₁ hL₁
  have heq := (huniq _ _ hr₂ hL₂).1
  have hv := congrArg (fun ψ : DirichletCharacter ℂ (M₁ * M₂) =>
    ψ ((ZMod.unitOfCoprime n hn : (ZMod (M₁ * M₂))ˣ) : ZMod (M₁ * M₂))) heq
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_left M₂ M₁),
    ZMod.cast_natCast (dvd_mul_right M₁ M₂)] at hv
  exact hv.symm

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
