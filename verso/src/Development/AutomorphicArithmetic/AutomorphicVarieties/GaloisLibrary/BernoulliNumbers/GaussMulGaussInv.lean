import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Establish `hF : ZMod.dft (⇑χ) = fun k ↦ (fun j ↦ (⇑χ⁻¹) (-j)) k * gaussSum χ ZMod.stdAddChar`. Use function extensionality and compare the values at `fun k ↦ hχ.fourierTransform_eq_inv_mul_gaussSum k`. Establish `h1` using `congr_fun (ZMod.dft_dft (⇑χ)) 1`. Rewrite `h1` using `[hF, ZMod.dft_mul_const, ZMod.dft_comp_neg]`. Simplify using `only at h1`.

Rewrite `h1` using `[DirichletCharacter.fourierTransform_eq_gaussSum_mulShift, neg_neg, AddChar.mulShift_one, smul_eq_mul]`. Establish `hsq : χ (-1) * χ (-1) = 1`. Rewrite using `[← map_mul, neg_one_mul, neg_neg, map_one]`. Rewrite using `[mul_comm (gaussSum χ _), h1, mul_assoc, hsq, mul_one]`.
-/
private theorem gauss_mul_gauss_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) = N := by
  have hF : ZMod.dft (⇑χ) = fun k ↦ (fun j ↦ (⇑χ⁻¹) (-j)) k * gaussSum χ ZMod.stdAddChar :=
    funext fun k ↦ hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h1 := congr_fun (ZMod.dft_dft (⇑χ)) 1
  rw [hF, ZMod.dft_mul_const, ZMod.dft_comp_neg] at h1
  simp only at h1
  rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift, neg_neg, AddChar.mulShift_one,
    smul_eq_mul] at h1
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [mul_comm (gaussSum χ _), h1, mul_assoc, hsq, mul_one]

/- English proof (translation)
Establish `h` using `gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar (-1)`. Rewrite `h` using `[inv_inv, Units.val_neg, Units.val_one]`. Rewrite using `[starRingEnd_apply, star_gaussSum_eq, AddChar.inv_mulShift, h, mul_comm]`.
-/
private theorem conj_gauss {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) = gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) := by
  have h := gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar (-1)
  rw [inv_inv, Units.val_neg, Units.val_one] at h
  rw [starRingEnd_apply, star_gaussSum_eq, AddChar.inv_mulShift, h, mul_comm]

/- English proof (translation)
Introduce `N _ χ hχ`. Establish `hns : (Complex.normSq (gaussSum χ ZMod.stdAddChar) : ℂ) = N`. Rewrite using `[← Complex.mul_conj, conj_gauss, ← mul_assoc, gauss_mul_gauss_inv χ hχ]`. Establish `hns' : Complex.normSq (gaussSum χ ZMod.stdAddChar) = N` using `by exact_mod_cast hns`. Establish `hg : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N`.

Rewrite using `[Complex.norm_def, hns']`. Use `⟨hg, ?_⟩` and prove the remaining obligations. Establish `hpos : (0 : ℝ) < N` using `Nat.cast_pos.mpr (NeZero.pos N)`. Rewrite using `[DirichletCharacter.rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I, one_pow, div_one, hg, Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]`. Rewrite using `[show (1 / 2 : ℂ).re = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]`.

Conclude with `div_self (Real.sqrt_ne_zero'.mpr hpos)`.
-/
theorem UpperTheory.V.Bern.b_gauss :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N ∧ ‖χ.rootNumber‖ = 1 := by
  intro N _ χ hχ
  have hns : (Complex.normSq (gaussSum χ ZMod.stdAddChar) : ℂ) = N := by
    rw [← Complex.mul_conj, conj_gauss, ← mul_assoc, gauss_mul_gauss_inv χ hχ]
  have hns' : Complex.normSq (gaussSum χ ZMod.stdAddChar) = N := by exact_mod_cast hns
  have hg : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N := by
    rw [Complex.norm_def, hns']
  refine ⟨hg, ?_⟩
  have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I, one_pow, div_one,
    hg, Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
  rw [show (1 / 2 : ℂ).re = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact div_self (Real.sqrt_ne_zero'.mpr hpos)
