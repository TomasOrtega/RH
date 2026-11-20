import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.DVR

variable {𝕜 W : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup W] [Module 𝕜 W]

def qf (B : LinearMap.BilinForm 𝕜 W) (w : W) : 𝕜 := B w w / 2

variable {B : LinearMap.BilinForm 𝕜 W}

/- English proof (translation)
Simplify using `only [qf, map_add, LinearMap.add_apply, hB y x]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qf_add (hB : ∀ x y, B x y = B y x) (x y : W) : qf B (x + y) = qf B x + B x y + qf B y := by
  simp only [qf, map_add, LinearMap.add_apply, hB y x]; ring

/- English proof (translation)
Simplify using `only [qf, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qf_smul (c : 𝕜) (x : W) : qf B (c • x) = c ^ 2 * qf B x := by
  simp only [qf, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Rewrite `h₁` using `[qf_add hB]`. Rewrite `h₂` using `[sub_eq_add_neg, qf_add hB, map_neg, show -μ = (-1 : 𝕜) • μ by simp, qf_smul]`. Apply the tactic sequence `rw [abs_le]; constructor <;> nlinarith`.
-/
theorem abs_le_qf_of_min (hB : ∀ x y, B x y = B y x) {x μ : W} (h₁ : qf B x ≤ qf B (x + μ))
    (h₂ : qf B x ≤ qf B (x - μ)) : |B x μ| ≤ qf B μ := by
  rw [qf_add hB] at h₁
  rw [sub_eq_add_neg, qf_add hB, map_neg, show -μ = (-1 : 𝕜) • μ by simp, qf_smul] at h₂
  rw [abs_le]; constructor <;> nlinarith

/- English proof (translation)
Establish `h` using `abs_le.mp (abs_le_qf_of_min hB h₁ h₂)`. Rewrite using `[qf_add hB, map_smul, qf_smul, smul_eq_mul]`. Establish `hk : (0 : 𝕜) ≤ k` using `Nat.cast_nonneg k`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h.1 hk]`.
-/
theorem tie (hB : ∀ x y, B x y = B y x) {x μ : W} (h₁ : qf B x ≤ qf B (x + μ)) (h₂ : qf B x ≤ qf B (x - μ))
    (k : ℕ) : (k : 𝕜) * ((k : 𝕜) - 1) * qf B μ ≤ qf B (x + (k : 𝕜) • μ) - qf B x := by
  have h := abs_le.mp (abs_le_qf_of_min hB h₁ h₂)
  rw [qf_add hB, map_smul, qf_smul, smul_eq_mul]
  have hk : (0 : 𝕜) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_le_mul_of_nonneg_left h.1 hk]

end ReciprocityTheory.ChartRestriction.G.DVR
