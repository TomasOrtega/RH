import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChange
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginCut

/- English proof (translation)
Introduce `A A₁ R R₁ _ _ _ _ _ _ _ j γ ρ ρ₁ β hβ hret hργ q hq DA _ _ actA hT`. Use `letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) := β.toAlgebra`. Take `⟨act', -, hT'⟩` from `GlobalTheory.LocAcyc.isZModTorsor_baseChange (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA q hq actA hT`. Set `M₁` to `Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)`. Set `f : R₁ →+* FractionRing A₁` to `(algebraMap A₁ (FractionRing A₁)).comp ρ₁`.

Establish `hf : ∀ m : M₁, IsUnit (f m)`. Introduce and unpack `⟨m, hm⟩`. Take `⟨a, ha, rfl⟩` from `hm`. Establish `: ρ₁ (algebraMap A₁ R₁ a) = a`. Simplify using `using congrArg (fun φ : A₁ →+* A₁ => φ a) hret`.

Simplify using `only [f, RingHom.comp_apply, this]`. Conclude with `IsLocalization.map_units (FractionRing A₁) (⟨a, ha⟩ : nonZeroDivisors A₁)`. Set `ρK : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* FractionRing A₁` to `IsLocalization.lift (M := M₁) (S := GlobalTheory.LocAcyc.GenFib A₁ R₁) hf`. Establish `hρK : ρK.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = f` using `IsLocalization.lift_comp hf`. Use `⟨TensorProduct (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA, inferInstance, inferInstance, act', Algebra.TensorProduct.includeRight.toRingHom, hT', ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `b`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply]`. Rewrite using `[← Algebra.TensorProduct.tmul_one_eq_one_tmul]`. Both sides reduce to the same expression. Introduce `σ hσ`.

Establish `hagree : ρK.comp β = σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA)`. Apply `IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))` to reduce the goal to its premises. Rewrite using `[hσ, RingHom.comp_assoc, hβ, ← RingHom.comp_assoc, hρK, ← hργ]`. Both sides reduce to the same expression. Use `letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (FractionRing A₁) := (ρK.comp β).toAlgebra`.

Set `fA : GlobalTheory.LocAcyc.GenFib A₁ R₁ →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁` to `{ ρK with commutes' := fun _ => rfl }`. Set `gA : DA →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁` to `{ σ with commutes' := fun b => (congrArg (fun φ => φ b) hagree).symm }`. Use `⟨(Algebra.TensorProduct.productMap fA gA).toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `r`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]`.

Use `show ρK (algebraMap R₁ _ r) = _`. Rewrite using `[← RingHom.comp_apply ρK, hρK]`. Both sides reduce to the same expression.
-/
theorem torsor_baseChange_point :
    ∀ (A A₁ R R₁ : Type) [CommRing A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R]
    [CommRing R₁] [Algebra A₁ R₁] (j : A →+* A₁) (γ : R →+* R₁) (ρ : R →+* A) (ρ₁ : R₁ →+* A₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ →
    ρ₁.comp (algebraMap A₁ R₁) = RingHom.id A₁ →
    ρ₁.comp γ = j.comp ρ →
    ∀ (q : ℕ), 0 < q → ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q actA →
    ∃ (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ R₁] DA₁)) (h : DA →+* DA₁),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁ q actA₁ ∧
      h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁).comp β ∧
      ∀ σ : DA →+* FractionRing A₁,
        (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA)).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
          (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
        ∃ σ₁ : DA₁ →+* FractionRing A₁,
          (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
            (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  intro A A₁ R R₁ _ _ _ _ _ _ _ j γ ρ ρ₁ β hβ hret hργ q hq DA _ _ actA hT
  letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) := β.toAlgebra
  obtain ⟨act', -, hT'⟩ := GlobalTheory.LocAcyc.isZModTorsor_baseChange (GlobalTheory.LocAcyc.GenFib A R)
    (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA q hq actA hT

  let M₁ := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)
  let f : R₁ →+* FractionRing A₁ := (algebraMap A₁ (FractionRing A₁)).comp ρ₁
  have hf : ∀ m : M₁, IsUnit (f m) := by
    rintro ⟨m, hm⟩
    obtain ⟨a, ha, rfl⟩ := hm
    have : ρ₁ (algebraMap A₁ R₁ a) = a := by
      simpa using congrArg (fun φ : A₁ →+* A₁ => φ a) hret
    simp only [f, RingHom.comp_apply, this]
    exact IsLocalization.map_units (FractionRing A₁) (⟨a, ha⟩ : nonZeroDivisors A₁)
  let ρK : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* FractionRing A₁ :=
    IsLocalization.lift (M := M₁) (S := GlobalTheory.LocAcyc.GenFib A₁ R₁) hf
  have hρK : ρK.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = f :=
    IsLocalization.lift_comp hf
  refine ⟨TensorProduct (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA, inferInstance,
    inferInstance, act', Algebra.TensorProduct.includeRight.toRingHom, hT', ?_, ?_⟩
  · ext b
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  · intro σ hσ
    have hagree : ρK.comp β = σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) := by
      apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
      rw [hσ, RingHom.comp_assoc, hβ, ← RingHom.comp_assoc, hρK, ← hργ]
      rfl
    letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (FractionRing A₁) := (ρK.comp β).toAlgebra
    let fA : GlobalTheory.LocAcyc.GenFib A₁ R₁ →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁ :=
      { ρK with commutes' := fun _ => rfl }
    let gA : DA →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁ :=
      { σ with commutes' := fun b => (congrArg (fun φ => φ b) hagree).symm }
    refine ⟨(Algebra.TensorProduct.productMap fA gA).toRingHom, ?_⟩
    ext r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one,
      mul_one]
    show ρK (algebraMap R₁ _ r) = _
    rw [← RingHom.comp_apply ρK, hρK]
    rfl

end GlobalTheory.KeyOriginCut
