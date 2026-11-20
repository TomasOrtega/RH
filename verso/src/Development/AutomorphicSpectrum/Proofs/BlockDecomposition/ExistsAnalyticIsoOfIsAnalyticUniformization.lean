import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticUniformization

/- English proof (translation)
Set `φ : (ℂ ⧸ Λ.toAddSubgroup) →+ E.toAffine.Point` to `QuotientAddGroup.lift Λ.toAddSubgroup f fun z hz => (hf.map_eq_zero_iff z).2 hz`. Establish `hφ : ∀ z : ℂ, φ (QuotientAddGroup.mk z) = f z` using `fun z => rfl`. Establish `hinj : Function.Injective φ`. Use `(injective_iff_map_eq_zero φ).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `QuotientAddGroup.mk_surjective x`.

Rewrite `hx` using `[hφ]`. Conclude with `(QuotientAddGroup.eq_zero_iff z).2 ((hf.map_eq_zero_iff z).1 hx)`. Establish `hsurj : Function.Surjective φ` using `fun P => by`. Take `⟨z, rfl⟩` from `hf.surjective P`. Conclude with `⟨QuotientAddGroup.mk z, hφ z⟩`.

Set `ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point` to `AddEquiv.ofBijective φ ⟨hinj, hsurj⟩`. Establish `hξ : ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z` using `fun z => rfl`. Use `⟨ξ, fun z hz => ?_, hξ⟩` and prove the remaining obligations. Establish `hz0 : f z ≠ 0` using `fun h => hz ((hf.map_eq_zero_iff z).1 h)`. Take `⟨X, Y, hX, hY, hev⟩` from `hf.analyticAt_affine z hz0`.

Use `⟨X, Y, hX, hY, hev.mono fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨h, hw⟩` from `hw`. Conclude with `⟨h, (hξ w).trans hw⟩`.
-/
theorem exists_analyticIso_of_isAnalyticUniformization (Λ : Submodule ℤ ℂ)
    (E : WeierstrassCurve ℂ) (f : ℂ →+ E.toAffine.Point)
    (hf : GroundTheory.Global.Elliptic.IsAnalyticUniformization Λ f) :
    ∃ ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point,
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z := by
  let φ : (ℂ ⧸ Λ.toAddSubgroup) →+ E.toAffine.Point :=
    QuotientAddGroup.lift Λ.toAddSubgroup f fun z hz => (hf.map_eq_zero_iff z).2 hz
  have hφ : ∀ z : ℂ, φ (QuotientAddGroup.mk z) = f z := fun z => rfl
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hφ] at hx
    exact (QuotientAddGroup.eq_zero_iff z).2 ((hf.map_eq_zero_iff z).1 hx)
  have hsurj : Function.Surjective φ := fun P => by
    obtain ⟨z, rfl⟩ := hf.surjective P
    exact ⟨QuotientAddGroup.mk z, hφ z⟩
  let ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point :=
    AddEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hξ : ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z := fun z => rfl
  refine ⟨ξ, fun z hz => ?_, hξ⟩
  have hz0 : f z ≠ 0 := fun h => hz ((hf.map_eq_zero_iff z).1 h)
  obtain ⟨X, Y, hX, hY, hev⟩ := hf.analyticAt_affine z hz0
  refine ⟨X, Y, hX, hY, hev.mono fun w hw => ?_⟩
  obtain ⟨h, hw⟩ := hw
  exact ⟨h, (hξ w).trans hw⟩

end GlobalTheory.CompanionTheory.EllipticUniformization
