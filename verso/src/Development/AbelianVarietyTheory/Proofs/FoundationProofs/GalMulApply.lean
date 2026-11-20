import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
open GlobalTheory.KZ Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Apply `(X.exp : X.K →+* HahnSeries ℚ Ω).injective` to reduce the goal to its premises. Use extensionality with `r`. Use `show (X.exp (X.gal (s * s') f)).coeff r = (X.exp (X.gal s (X.gal s' f))).coeff r`. Rewrite using `[X.gal_exp, X.gal_exp, X.gal_exp]`. Both sides reduce to the same expression.
-/
theorem Tower.gal_mul_apply (X : Tower Ω ε) (s s' : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal (s * s') f = X.gal s (X.gal s' f) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  show (X.exp (X.gal (s * s') f)).coeff r = (X.exp (X.gal s (X.gal s' f))).coeff r
  rw [X.gal_exp, X.gal_exp, X.gal_exp]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[Tower.kmap_kmap]`. Establish `hg : X.gal (s * s') = (X.gal s').trans (X.gal s)`. Use extensionality with `f`.

Conclude with `X.gal_mul_apply s s' f`. Establish `hc : (cyclotomicCharacter Ω l (s * s').toRingEquiv : ℤ_[l]) = (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (cyclotomicCharacter Ω l s'.toRingEquiv : ℤ_[l])`. Establish `: (s * s').toRingEquiv = s.toRingEquiv * s'.toRingEquiv` using `rfl`. Rewrite using `[this, map_mul, Units.val_mul]`. Rewrite using `[hg, hc]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [mul_comm, mul_left_comm]`.
-/
theorem Tower.galB_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s s' : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) :
    X.galB l (s * s') b = X.galB l s (X.galB l s' b) := by
  funext u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Tower.kmap_kmap]
  have hg : X.gal (s * s') = (X.gal s').trans (X.gal s) := by
    ext f; exact X.gal_mul_apply s s' f
  have hc : (cyclotomicCharacter Ω l (s * s').toRingEquiv : ℤ_[l]) =
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (cyclotomicCharacter Ω l s'.toRingEquiv : ℤ_[l]) := by
    have : (s * s').toRingEquiv = s.toRingEquiv * s'.toRingEquiv := rfl
    rw [this, map_mul, Units.val_mul]
  rw [hg, hc]
  congr 2
  funext i
  fin_cases i <;> simp [mul_comm, mul_left_comm]

end GlobalTheory.KZ
