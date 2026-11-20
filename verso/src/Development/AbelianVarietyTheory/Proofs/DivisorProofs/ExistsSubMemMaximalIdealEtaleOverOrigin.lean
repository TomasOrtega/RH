import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOrigin
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.OriginResidue

/- English proof (translation)
Use `⟨fun p hp => ?_⟩` and prove the remaining obligations. Establish `h` using `IsSepClosed.splits_domain (f := e.toRingHom) (p.map e.symm.toRingHom) hp.map`. Rewrite `h` using `[Polynomial.map_map, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from by ext; simp, Polynomial.map_id]`. Then use the resulting hypothesis.
-/
theorem isSepClosed_of_ringEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) [IsSepClosed K] :
    IsSepClosed L := by
  refine ⟨fun p hp => ?_⟩
  have h := IsSepClosed.splits_domain (f := e.toRingHom) (p.map e.symm.toRingHom) hp.map
  rwa [Polynomial.map_map, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from by
    ext; simp, Polynomial.map_id] at h

variable {A : Type} [CommRing A] [IsLocalRing A]

def constToResidue [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] :
    A →+* (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField :=
  (algebraMap (Polynomial A) (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField).comp Polynomial.C

/- English proof (translation)
Simplify using `only [constToResidue, RingHom.comp_apply]`. Rewrite using `[Ideal.algebraMap_residueField_eq_zero, GlobalTheory.LocalStage.mem_originIdeal_iff]`. Simplify using `using ha`.
-/
theorem constToResidue_eq_zero [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] {a : A}
    (ha : a ∈ maximalIdeal A) : constToResidue a = 0 := by
  simp only [constToResidue, RingHom.comp_apply]
  rw [Ideal.algebraMap_residueField_eq_zero, GlobalTheory.LocalStage.mem_originIdeal_iff]
  simpa using ha

instance [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] : IsLocalHom (constToResidue (A := A)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have := constToResidue_eq_zero ((mem_maximalIdeal a).2 h)
  rw [this] at ha
  exact not_isUnit_zero ha

/- English proof (translation)
Simplify using `only [constToResidue, RingHom.comp_apply]`. Rewrite using `[← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero, GlobalTheory.LocalStage.mem_originIdeal_iff]`. Simplify using the standard rewrite rules.
-/
theorem algebraMap_eq_constToResidue [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] (f : Polynomial A) :
    algebraMap (Polynomial A) (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField f =
      constToResidue (f.coeff 0) := by
  simp only [constToResidue, RingHom.comp_apply]
  rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero,
    GlobalTheory.LocalStage.mem_originIdeal_iff]
  simp

/- English proof (translation)
Use `set p := GlobalTheory.KeyOriginCut.originIdeal A`. Introduce `x`. Take `⟨z, rfl⟩` from `residue_surjective x`. Take `⟨⟨f, s⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl z`. Establish `hs : algebraMap (Polynomial A) p.ResidueField s ≠ 0`.

Rewrite using `[Ne, Ideal.algebraMap_residueField_eq_zero]`. Conclude with `s.2`. Establish `key : residue _ (IsLocalization.mk' (Localization.AtPrime p) f s) * algebraMap (Polynomial A) p.ResidueField s = algebraMap (Polynomial A) p.ResidueField f`. Rewrite using `[IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime p) p.ResidueField, IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime p) p.ResidueField f, ResidueField.algebraMap_eq, ← map_mul, IsLocalization.mk'_spec]`. Use `⟨residue A (f.coeff 0) / residue A ((s : Polynomial A).coeff 0), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, ResidueField.lift_residue_apply, ResidueField.lift_residue_apply, ← algebraMap_eq_constToResidue, ← algebraMap_eq_constToResidue, ← key, mul_div_cancel_right₀ _ hs]`.
-/
theorem lift_surjective [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] :
    Function.Surjective (ResidueField.lift (constToResidue (A := A))) := by
  set p := GlobalTheory.KeyOriginCut.originIdeal A
  intro x
  obtain ⟨z, rfl⟩ := residue_surjective x
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  have hs : algebraMap (Polynomial A) p.ResidueField s ≠ 0 := by
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact s.2
  have key : residue _ (IsLocalization.mk' (Localization.AtPrime p) f s) *
      algebraMap (Polynomial A) p.ResidueField s = algebraMap (Polynomial A) p.ResidueField f := by
    rw [IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime p) p.ResidueField,
      IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime p) p.ResidueField f,
      ResidueField.algebraMap_eq, ← map_mul, IsLocalization.mk'_spec]
  refine ⟨residue A (f.coeff 0) / residue A ((s : Polynomial A).coeff 0), ?_⟩
  rw [map_div₀, ResidueField.lift_residue_apply, ResidueField.lift_residue_apply,
    ← algebraMap_eq_constToResidue, ← algebraMap_eq_constToResidue, ← key, mul_div_cancel_right₀ _ hs]

/- English proof (translation)
Introduce `A _ _ _ E _ _ _ Q _ hQ y`. Use `set p := GlobalTheory.KeyOriginCut.originIdeal A with hp`. Use `haveI : p.IsPrime := hQ ▸ Ideal.comap_isPrime _ Q`. Use `haveI : Q.LiesOver p := ⟨hQ.symm⟩`. Use `letI := Localization.AtPrime.algebraOfLiesOver p Q`.

Use `haveI : IsSepClosed p.ResidueField := isSepClosed_of_ringEquiv (RingEquiv.ofBijective _ ⟨(ResidueField.lift (constToResidue (A := A))).injective, lift_surjective⟩)`. Take `⟨x, hx⟩` from `IsSepClosed.algebraMap_surjective p.ResidueField Q.ResidueField (residue (Localization.AtPrime Q) y)`. Take `⟨c, rfl⟩` from `lift_surjective x`. Take `⟨c, rfl⟩` from `residue_surjective c`. Use `⟨Polynomial.C c, ?_⟩` and prove the remaining obligations.

Rewrite using `[← residue_eq_zero_iff, map_sub, ← hx, ResidueField.lift_residue_apply]`. Simplify using `only [constToResidue, RingHom.comp_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime Q) Q.ResidueField, ResidueField.algebraMap_eq, sub_self]`.
-/
theorem residue_origin : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsSepClosed (ResidueField A)] (E : Type) [CommRing E] [Algebra (Polynomial A) E] [Algebra.Etale (Polynomial A) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A) E) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ y : Localization.AtPrime Q, ∃ a : Polynomial A, y - algebraMap (Polynomial A) (Localization.AtPrime Q) a ∈ maximalIdeal (Localization.AtPrime Q) := by
  intro A _ _ _ E _ _ _ Q _ hQ y
  set p := GlobalTheory.KeyOriginCut.originIdeal A with hp
  haveI : p.IsPrime := hQ ▸ Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨hQ.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p Q
  haveI : IsSepClosed p.ResidueField := isSepClosed_of_ringEquiv
    (RingEquiv.ofBijective _ ⟨(ResidueField.lift (constToResidue (A := A))).injective, lift_surjective⟩)
  obtain ⟨x, hx⟩ := IsSepClosed.algebraMap_surjective p.ResidueField Q.ResidueField
    (residue (Localization.AtPrime Q) y)
  obtain ⟨c, rfl⟩ := lift_surjective x
  obtain ⟨c, rfl⟩ := residue_surjective c
  refine ⟨Polynomial.C c, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← hx, ResidueField.lift_residue_apply]
  simp only [constToResidue, RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime Q) Q.ResidueField, ResidueField.algebraMap_eq, sub_self]

end GlobalTheory.OriginResidue
