import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

/- English proof (translation)
Introduce `x₀ hx₀ hiso`. Establish `hne : h.toSesq x₀ ≠ 0`. Introduce `h0`. Apply `hx₀` to reduce the goal to its premises. Apply `h.nonsingular.1` to reduce the goal to its premises.

Rewrite using `[h0, map_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨y', hy'⟩ : ∃ y', h.toSesq x₀ y' ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Conclude with `hne (LinearMap.ext fun z => not_not.1 fun hz => hc ⟨z, hz⟩)`. Take `⟨y, hy⟩ : ∃ y, h.toSesq x₀ y = 1` from `⟨(h.toSesq x₀ y')⁻¹ • y', by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy']⟩`.

Establish `hyx : h.toSesq y x₀ = 1`. Rewrite using `[← h.isSymm.eq x₀ y, hy, map_one]`. Take `⟨a, ha_def⟩ : ∃ a, h.toSesq y y = a` from `⟨_, rfl⟩`. Establish `ha : conjHom F E a = a`. Rewrite using `[← ha_def]`.

Conclude with `h.isSymm.eq y y`. Establish `ht : conjHom F E (a / 2) = a / 2`. Rewrite using `[map_div₀, ha, map_ofNat]`. Establish `hl : ∀ z, h.toSesq (y - (a / 2) • x₀) z = h.toSesq y z - (a / 2) * h.toSesq x₀ z`. Introduce `z`.

Rewrite using `[LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, ht, smul_eq_mul]`. Use `⟨y - (a / 2) • x₀, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, hy, hiso, smul_zero, sub_zero]`. Rewrite using `[hl]`. Simplify using `only [map_sub, map_smul, smul_eq_mul, hyx, hy, hiso, ha_def]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem WittPartner.proof (h : HermitianForm F E W) : WittPartner.Statement h := by
  intro x₀ hx₀ hiso

  have hne : h.toSesq x₀ ≠ 0 := by
    intro h0
    apply hx₀
    apply h.nonsingular.1
    rw [h0, map_zero]
  obtain ⟨y', hy'⟩ : ∃ y', h.toSesq x₀ y' ≠ 0 := by
    by_contra hc
    exact hne (LinearMap.ext fun z => not_not.1 fun hz => hc ⟨z, hz⟩)

  obtain ⟨y, hy⟩ : ∃ y, h.toSesq x₀ y = 1 :=
    ⟨(h.toSesq x₀ y')⁻¹ • y', by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy']⟩
  have hyx : h.toSesq y x₀ = 1 := by
    rw [← h.isSymm.eq x₀ y, hy, map_one]

  obtain ⟨a, ha_def⟩ : ∃ a, h.toSesq y y = a := ⟨_, rfl⟩
  have ha : conjHom F E a = a := by
    rw [← ha_def]
    exact h.isSymm.eq y y
  have ht : conjHom F E (a / 2) = a / 2 := by
    rw [map_div₀, ha, map_ofNat]

  have hl : ∀ z, h.toSesq (y - (a / 2) • x₀) z = h.toSesq y z - (a / 2) * h.toSesq x₀ z := by
    intro z
    rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, ht, smul_eq_mul]
  refine ⟨y - (a / 2) • x₀, ?_, ?_⟩
  · rw [map_sub, map_smul, hy, hiso, smul_zero, sub_zero]
  · rw [hl]
    simp only [map_sub, map_smul, smul_eq_mul, hyx, hy, hiso, ha_def]
    ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
