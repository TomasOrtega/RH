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
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Equip the data with the indicated structure. Introduce a local definition for the expression.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
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
