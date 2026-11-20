import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModVanish
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.JInt

/- English proof (translation)
Introduce `h`. Establish `h2 : (2 * |r|) ^ 2 = u ^ 2 + Δ` using `by rw [mul_pow, sq_abs]; linarith`. Establish `hr0 : 0 ≤ 2 * |r|` using `by positivity`. Establish `hu0 : 0 ≤ u` using `by linarith`. Establish `a1 : u < 2 * |r|` using `by nlinarith`.

Establish `a2 : 2 * |r| < u + 1` using `by nlinarith`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_four_sq {u Δ : ℤ} (hu : Δ ≤ u) (hΔ : 0 < Δ) (r : ℤ) : u ^ 2 + Δ ≠ 4 * (r * r) := by
  intro h
  have h2 : (2 * |r|) ^ 2 = u ^ 2 + Δ := by rw [mul_pow, sq_abs]; linarith
  have hr0 : 0 ≤ 2 * |r| := by positivity
  have hu0 : 0 ≤ u := by linarith
  have a1 : u < 2 * |r| := by nlinarith
  have a2 : 2 * |r| < u + 1 := by nlinarith
  omega

/- English proof (translation)
Use `set x := (τ : ℂ).re`. Use `set y := (τ : ℂ).im`. Establish `hy : 0 < y` using `τ.im_pos`. Establish `hre` using `congrArg Complex.re hfix`. Establish `him` using `congrArg Complex.im hfix`.

Simplify using `only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_im, Complex.mul_im] at hre him`. Establish `h1 : ((D : ℝ) - A + 2 * C * x) * y = 0` using `by linear_combination -him`. Establish `h1' : (D : ℝ) - A + 2 * C * x = 0` using `(mul_eq_zero.mp h1).resolve_right hy.ne'`. Establish `key : (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) = 4 * (C : ℝ) ^ 2 * y ^ 2`. Use `push_cast`.

Take the linear combination `(-(D : ℝ) + A - 2 * C * x) * h1' - 4 * (C : ℝ) * hre`. Establish `hCr : (0 : ℝ) < (C : ℝ) ^ 2` using `by positivity`. Establish `: (0 : ℝ) < (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ)` using `by rw [key]; positivity`. Conclude with `this` after adjusting the coercions.
-/
theorem disc_pos {A B C D : ℤ} {τ : ℍ} (hC : C ≠ 0)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : 0 < -((D - A) ^ 2 + 4 * B * C) := by
  set x := (τ : ℂ).re
  set y := (τ : ℂ).im
  have hy : 0 < y := τ.im_pos
  have hre := congrArg Complex.re hfix
  have him := congrArg Complex.im hfix
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
    Complex.mul_im] at hre him
  have h1 : ((D : ℝ) - A + 2 * C * x) * y = 0 := by linear_combination -him
  have h1' : (D : ℝ) - A + 2 * C * x = 0 := (mul_eq_zero.mp h1).resolve_right hy.ne'
  have key : (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) = 4 * (C : ℝ) ^ 2 * y ^ 2 := by
    push_cast
    linear_combination (-(D : ℝ) + A - 2 * C * x) * h1' - 4 * (C : ℝ) * hre
  have hCr : (0 : ℝ) < (C : ℝ) ^ 2 := by positivity
  have : (0 : ℝ) < (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) := by rw [key]; positivity
  exact_mod_cast this

/- English proof (translation)
Introduce `L c τ α hτ hα him`. Take `⟨hc, hlat⟩` from `hτ`. Establish `h1 : c * (τ : ℂ) ∈ L.lattice` using `(hlat _).2 ⟨1, 0, by simp⟩`. Establish `h2 : c ∈ L.lattice` using `(hlat _).2 ⟨0, 1, by simp⟩`. Take `⟨A, B, hAB⟩` from `(hlat _).1 (hα _ h1)`.

Take `⟨C, D, hCD⟩` from `(hlat _).1 (hα _ h2)`. Establish `e1 : α * (τ : ℂ) = A * τ + B` using `by apply mul_left_cancel₀ hc; linear_combination hAB`. Establish `e2 : α = C * τ + D` using `by apply mul_left_cancel₀ hc; linear_combination hCD`. Establish `hfix : (A : ℂ) * τ + B = τ * (C * τ + D)` using `by rw [← e1, e2]; ring`. Establish `hC : C ≠ 0`.

Introduce and unpack `rfl`. Apply `him` to reduce the goal to its premises. Rewrite using `[e2]`. Simplify using the standard rewrite rules. Establish `hΔ` using `disc_pos hC hfix`.

Use `set Δ := -((D - A) ^ 2 + 4 * B * C) with hΔdef`. Use `set t := A + D`. Use `set k := Δ + |t|`. Use `set M := (A + k) * (D + k) - B * C with hM`. Establish `h4M : 4 * M = (2 * k + t) ^ 2 + Δ` using `by rw [hM, hΔdef]; ring`.

Establish `hu : Δ ≤ 2 * k + t`. Use `neg_abs_le t` as an intermediate fact. Use `abs_nonneg t` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hMpos : 0 < M` using `by nlinarith`.

Establish `hm : 0 < M.toNat` using `by omega`. Establish `hMc : ((M.toNat : ℕ) : ℤ) = M` using `Int.toNat_of_nonneg hMpos.le`. Use `jT_isIntegral hm ?_ (Gm_vanish hm τ (A + k) B C (D + k) (by rw [hMc]) ?_)` and prove the remaining obligations. Introduce and unpack `⟨r, hr⟩`. Establish `: M = (r : ℤ) * r` using `by rw [← hMc, hr]; push_cast; ring`.

Conclude with `not_four_sq hu hΔ r (by rw [← h4M, this])`. Use `push_cast`. Take the linear combination `hfix`.
-/
theorem main : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ) (α : ℂ), IsTauOf L c τ → MulStable L α → α.im ≠ 0 →
    IsIntegral ℤ (jT τ) := by
  intro L c τ α hτ hα him
  obtain ⟨hc, hlat⟩ := hτ
  have h1 : c * (τ : ℂ) ∈ L.lattice := (hlat _).2 ⟨1, 0, by simp⟩
  have h2 : c ∈ L.lattice := (hlat _).2 ⟨0, 1, by simp⟩
  obtain ⟨A, B, hAB⟩ := (hlat _).1 (hα _ h1)
  obtain ⟨C, D, hCD⟩ := (hlat _).1 (hα _ h2)
  have e1 : α * (τ : ℂ) = A * τ + B := by apply mul_left_cancel₀ hc; linear_combination hAB
  have e2 : α = C * τ + D := by apply mul_left_cancel₀ hc; linear_combination hCD
  have hfix : (A : ℂ) * τ + B = τ * (C * τ + D) := by rw [← e1, e2]; ring
  have hC : C ≠ 0 := by
    rintro rfl
    apply him; rw [e2]; simp
  have hΔ := disc_pos hC hfix
  set Δ := -((D - A) ^ 2 + 4 * B * C) with hΔdef
  set t := A + D
  set k := Δ + |t|
  set M := (A + k) * (D + k) - B * C with hM
  have h4M : 4 * M = (2 * k + t) ^ 2 + Δ := by rw [hM, hΔdef]; ring
  have hu : Δ ≤ 2 * k + t := by
    have := neg_abs_le t; have := abs_nonneg t; linarith
  have hMpos : 0 < M := by nlinarith
  have hm : 0 < M.toNat := by omega
  have hMc : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hMpos.le
  refine jT_isIntegral hm ?_ (Gm_vanish hm τ (A + k) B C (D + k) (by rw [hMc]) ?_)
  · rintro ⟨r, hr⟩
    have : M = (r : ℤ) * r := by rw [← hMc, hr]; push_cast; ring
    exact not_four_sq hu hΔ r (by rw [← h4M, this])
  · push_cast; linear_combination hfix

end GlobalTheory.JInt
