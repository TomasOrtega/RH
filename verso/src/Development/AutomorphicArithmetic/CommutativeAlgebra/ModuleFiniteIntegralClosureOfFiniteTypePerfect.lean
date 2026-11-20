import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteIntegralClosureOfIsIntegrallyClosed

open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

/- English proof (translation)
Use `letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L`. Use `haveI : IsScalarTower B (FractionRing B) L := FractionRing.isScalarTower_liftAlgebra B L`. Use `haveI : Algebra.EssFiniteType (FractionRing B) L := Algebra.EssFiniteType.of_comp B (FractionRing B) L`. Set `M` to `algebraicClosure (FractionRing B) L`. Use `haveI : FiniteDimensional (FractionRing B) M := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType (FractionRing B) L`.

Use `haveI : Module.Finite B (integralClosure B M) := GlobalTheory.NormFin.finite_integralClosure_of_perfectField k B (FractionRing B) M`. Set `g : M →ₐ[B] L` to `M.val.restrictScalars B`. Establish `hg : Function.Injective g` using `Subtype.val_injective`. Set `φ : integralClosure B M →ₗ[B] integralClosure B L` to `{ toFun := fun x => ⟨g x, x.2.map g⟩ map_add' := by`. Introduce `x y`.

Use `ext`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := by`. Introduce `r x`. Use `ext`.

Simplify using `}`. Use `Module.Finite.of_surjective φ ?_` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Establish `hyF : IsIntegral (FractionRing B) y` using `hy.tower_top`. Set `z : M` to `⟨y, mem_algebraicClosure_iff'.mpr hyF⟩`.

Establish `hz : IsIntegral B z` using `(isIntegral_algHom_iff g hg).mp hy`. Conclude with `⟨⟨z, hz⟩, rfl⟩`.
-/
private theorem UpperTheory.integralClosure_finite_of_finiteType_perfect (k : Type) [Field k] [PerfectField k] (B L : Type)
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] [Field L] [Algebra B L]
    [FaithfulSMul B L] [Algebra.EssFiniteType B L] :
    Module.Finite B (integralClosure B L) := by
  letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
  haveI : IsScalarTower B (FractionRing B) L := FractionRing.isScalarTower_liftAlgebra B L
  haveI : Algebra.EssFiniteType (FractionRing B) L :=
    Algebra.EssFiniteType.of_comp B (FractionRing B) L
  let M := algebraicClosure (FractionRing B) L
  haveI : FiniteDimensional (FractionRing B) M :=
    GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType (FractionRing B) L
  haveI : Module.Finite B (integralClosure B M) :=
    GlobalTheory.NormFin.finite_integralClosure_of_perfectField k B (FractionRing B) M
  let g : M →ₐ[B] L := M.val.restrictScalars B
  have hg : Function.Injective g := Subtype.val_injective
  let φ : integralClosure B M →ₗ[B] integralClosure B L :=
    { toFun := fun x => ⟨g x, x.2.map g⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro r x
        ext
        simp }
  refine Module.Finite.of_surjective φ ?_
  rintro ⟨y, hy⟩
  have hyF : IsIntegral (FractionRing B) y := hy.tower_top
  let z : M := ⟨y, mem_algebraicClosure_iff'.mpr hyF⟩
  have hz : IsIntegral B z := (isIntegral_algHom_iff g hg).mp hy
  exact ⟨⟨z, hz⟩, rfl⟩

/- English proof (translation)
Introduce `k _ _ A L _ _ _ _ _ _`. Set `I` to `RingHom.ker (algebraMap A L)`. Use `letI : Algebra (A ⧸ I) L := (RingHom.kerLift (algebraMap A L)).toAlgebra`. Use `haveI : IsScalarTower A (A ⧸ I) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : FaithfulSMul (A ⧸ I) L := (faithfulSMul_iff_algebraMap_injective (A ⧸ I) L).mpr (RingHom.kerLift_injective _)`.

Use `haveI : I.IsPrime := RingHom.ker_isPrime (algebraMap A L)`. Use `haveI : IsDomain (A ⧸ I) := Ideal.Quotient.isDomain I`. Use `haveI : Algebra.FiniteType k (A ⧸ I) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective`. Use `haveI : Algebra.EssFiniteType (A ⧸ I) L := Algebra.EssFiniteType.of_comp A (A ⧸ I) L`. Use `haveI : Module.Finite A (A ⧸ I) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ A I).toLinearMap Ideal.Quotient.mk_surjective`.

Use `haveI : Module.Finite (A ⧸ I) (integralClosure (A ⧸ I) L) := UpperTheory.integralClosure_finite_of_finiteType_perfect k (A ⧸ I) L`. Conclude with `GlobalTheory.finite_integralClosure_of_finite_tower A (A ⧸ I) L`.
-/
theorem UpperTheory.module_finite_integralClosure_of_finiteType_perfect :
    ∀ (k : Type) [Field k] [PerfectField k] (A L : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Field L] [Algebra A L] [Algebra.EssFiniteType A L], Module.Finite A (integralClosure A L) := by
  intro k _ _ A L _ _ _ _ _ _
  let I := RingHom.ker (algebraMap A L)
  letI : Algebra (A ⧸ I) L := (RingHom.kerLift (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A (A ⧸ I) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul (A ⧸ I) L :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ I) L).mpr (RingHom.kerLift_injective _)
  haveI : I.IsPrime := RingHom.ker_isPrime (algebraMap A L)
  haveI : IsDomain (A ⧸ I) := Ideal.Quotient.isDomain I
  haveI : Algebra.FiniteType k (A ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective
  haveI : Algebra.EssFiniteType (A ⧸ I) L := Algebra.EssFiniteType.of_comp A (A ⧸ I) L
  haveI : Module.Finite A (A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (A ⧸ I) (integralClosure (A ⧸ I) L) :=
    UpperTheory.integralClosure_finite_of_finiteType_perfect k (A ⧸ I) L
  exact GlobalTheory.finite_integralClosure_of_finite_tower A (A ⧸ I) L
