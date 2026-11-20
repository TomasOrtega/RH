import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

noncomputable section

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private def slashEquiv (N : ℕ) (x : ZMod N) (a b c d : ℤ) (hdet : a * d - b * c = 1) (hc : (c : ZMod N) = 0) :
    {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = x} ≃
      {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = x * (d : ZMod N)} where
  toFun v := ⟨(v.1.1 * a + v.1.2 * c, v.1.1 * b + v.1.2 * d), by
    obtain ⟨⟨m, n⟩, h1, h2⟩ := v
    simp only at h1 h2
    constructor <;> simp [h1, h2, hc]⟩
  invFun v := ⟨(v.1.1 * d - v.1.2 * c, -(v.1.1 * b) + v.1.2 * a), by
    obtain ⟨⟨m, n⟩, h1, h2⟩ := v
    simp only at h1 h2
    have h : (a : ZMod N) * d = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod N) hdet
      push_cast at this
      simpa [hc] using this
    constructor
    · simp [h1, hc]
    · push_cast
      rw [h1, h2]
      linear_combination x * h⟩
  left_inv v := by
    obtain ⟨⟨m, n⟩, h⟩ := v
    apply Subtype.ext
    apply Prod.ext
    · show (m * a + n * c) * d - (m * b + n * d) * c = m
      linear_combination m * hdet
    · show -((m * a + n * c) * b) + (m * b + n * d) * a = n
      linear_combination n * hdet
  right_inv v := by
    obtain ⟨⟨m, n⟩, h⟩ := v
    apply Subtype.ext
    apply Prod.ext
    · show (m * d - n * c) * a + (-(m * b) + n * a) * c = m
      linear_combination m * hdet
    · show (m * d - n * c) * b + (-(m * b) + n * a) * d = n
      linear_combination n * hdet

/- English proof (translation)
Introduce `N k _ _ a γ hγ`. Establish `hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1`. Use `γ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Conclude with `this`.

Establish `hc : ((γ 1 0 : ℤ) : ZMod N) = 0` using `Gamma0_mem.mp hγ`. Use extensionality with `z`. Rewrite using `[ModularForm.SL_slash_apply]`. Establish `hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (z : ℂ) = (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)`. Simplify using `[denom]`.

Establish `hsm : ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))`. Rewrite using `[UpperHalfPlane.coe_specialLinearGroup_apply]`. Simplify using the standard rewrite rules. Establish `hne : (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0`. Rewrite using `[← hden]`.

Conclude with `denom_ne_zero _ z`. Establish `key : ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) = (γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)` using `div_mul_cancel₀ _ hne`. Rewrite using `[hden]`. Unfold `eisFun`. Rewrite using `[hsm, mul_assoc, ← tsum_mul_right]`.

Rewrite using `[← (slashEquiv N a (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) hdet hc).tsum_eq]`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `v`. Rewrite using `[← mul_zpow]`.

Use `congr 1`. Simplify using `only [slashEquiv, Equiv.coe_fn_mk]`. Use `push_cast`. Take the linear combination `((v : ℤ × ℤ).1 : ℂ) * key`.
-/
theorem eisSlash : EisSlash := by
  intro N k _ _ a γ hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ
  ext z
  rw [ModularForm.SL_slash_apply]
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (z : ℂ) = (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) := by
    simp [denom]
  have hsm : ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have hne : (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0 := by
    rw [← hden]
    exact denom_ne_zero _ z
  have key : ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) = (γ 0 0 : ℂ) * z + (γ 0 1 : ℂ) := div_mul_cancel₀ _ hne
  rw [hden]
  unfold eisFun
  rw [hsm, mul_assoc, ← tsum_mul_right]
  rw [← (slashEquiv N a (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) hdet hc).tsum_eq]
  congr 1
  congr 1
  funext v
  rw [← mul_zpow]
  congr 1
  simp only [slashEquiv, Equiv.coe_fn_mk]
  push_cast
  linear_combination ((v : ℤ × ℤ).1 : ℂ) * key

end UpperTheory.V.Sd
