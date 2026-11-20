import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.NormFin

/- English proof (translation)
Use `letI := φ.toAlgebra`. Use `letI : Module R M := Module.compHom M φ`. Use `haveI : IsScalarTower R S M := ⟨fun r s m => mul_smul (φ r) s m⟩`. Use `haveI : Module.Finite R S := hφ`. Use `haveI : Module.Finite R M := Module.Finite.trans S M`.

Set `g : N →ₗ[R] M` to `{ toFun := f map_add' := f.map_add map_smul' := fun r x => f.map_smulₛₗ r x }`. Conclude with `Module.Finite.of_injective g hf`.
-/
theorem finite_of_semilinear_injective {R S N M : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [AddCommGroup N] [Module R N] [AddCommGroup M] [Module S M] [Module.Finite S M]
    (φ : R →+* S) (hφ : φ.Finite) (f : N →ₛₗ[φ] M) (hf : Function.Injective f) :
    Module.Finite R N := by
  letI := φ.toAlgebra
  letI : Module R M := Module.compHom M φ
  haveI : IsScalarTower R S M := ⟨fun r s m => mul_smul (φ r) s m⟩
  haveI : Module.Finite R S := hφ
  haveI : Module.Finite R M := Module.Finite.trans S M
  let g : N →ₗ[R] M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r x => f.map_smulₛₗ r x }
  exact Module.Finite.of_injective g hf

/- English proof (translation)
Use `RingHom.IsIntegral.to_finite ?_ ?_` and prove the remaining obligations. Introduce `x`. Use `⟨Polynomial.X ^ (p ^ e) - Polynomial.C x, Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (expChar_ne_zero k p)), ?_⟩` and prove the remaining obligations. Simplify using `[iterateFrobenius_def]`. Use `RingHom.FiniteType.of_comp_finiteType (f := algebraMap k P) ?_` and prove the remaining obligations.

Establish `h : (iterateFrobenius P p e).comp (algebraMap k P) = (algebraMap k P).comp (iterateFrobenius k p e)`. Use extensionality with `x`. Simplify using `[iterateFrobenius_def]`. Rewrite using `[h]`. Conclude with `(RingHom.finiteType_algebraMap.mpr inferInstance).comp (.of_surjective _ (bijective_iterateFrobenius k p e).2)`.
-/
theorem finite_iterateFrobenius (k P : Type*) [Field k] [PerfectField k] [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] (p : ℕ) [ExpChar k p] [ExpChar P p] (e : ℕ) :
    (iterateFrobenius P p e).Finite := by
  refine RingHom.IsIntegral.to_finite ?_ ?_
  · intro x
    refine ⟨Polynomial.X ^ (p ^ e) - Polynomial.C x,
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (expChar_ne_zero k p)), ?_⟩
    simp [iterateFrobenius_def]
  · refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k P) ?_
    have h : (iterateFrobenius P p e).comp (algebraMap k P) =
        (algebraMap k P).comp (iterateFrobenius k p e) := by
      ext x
      simp [iterateFrobenius_def]
    rw [h]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (.of_surjective _ (bijective_iterateFrobenius k p e).2)

/- English proof (translation)
Use `haveI : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P`. Take `⟨p, hp⟩` from `ExpChar.exists k`. Use `haveI : ExpChar P p := expChar_of_injective_algebraMap (algebraMap k P).injective p`. Use `haveI : ExpChar K p := expChar_of_injective_algebraMap (IsFractionRing.injective P K) p`. Use `haveI : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p`.

Set `E` to `separableClosure K F`. Use `haveI : ExpChar E p := expChar_of_injective_algebraMap (algebraMap K E).injective p`. Use `haveI : Module.Finite P (integralClosure P E) := IsIntegralClosure.finite P K E _`. Use `haveI : IsScalarTower P E F := .of_algebraMap_eq' rfl`. Set `e` to `IsPurelyInseparable.exponent E F`.

Establish `hE : ∀ z : F, z ^ p ^ e ∈ E` using `fun z => by`. Take `⟨y, hy⟩` from `IsPurelyInseparable.exponent_def' E p z`. Conclude with `hy ▸ y.2`. Set `f : integralClosure P F →ₛₗ[iterateFrobenius P p e] integralClosure P E` to `{ toFun := fun z => ⟨⟨z.1 ^ p ^ e, hE _⟩, (isIntegral_algHom_iff (IsScalarTower.toAlgHom P E F) Subtype.val_injective).mp (IsIntegral.pow z.2 _)⟩ map_add' := fun x y => Subtype.ext (Subtype.ext (add_pow_expChar_pow _ _ _ _)) map_smul' := fun r x => Subtype.ext (Subtype.ext (by`. Express the relevant statement in the definitionally equal form `(r • x.1) ^ p ^ e = (r ^ p ^ e) • x.1 ^ p ^ e`.

Rewrite using `[smul_pow])) }`. Use `finite_of_semilinear_injective _ (finite_iterateFrobenius k P p e) f fun x y h => ?_` and prove the remaining obligations. Establish `h1 : x.1 ^ p ^ e = y.1 ^ p ^ e` using `congrArg (fun w : integralClosure P E => (w.1.1 : F)) h`. Conclude with `Subtype.ext ((iterateFrobenius F p e).injective h1)`.
-/
theorem finite_integralClosure_of_isIntegrallyClosed (k P K F : Type*) [Field k] [PerfectField k]
    [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [Algebra k P] [Algebra.FiniteType k P]
    [Field K] [Algebra P K] [IsFractionRing P K] [Field F] [Algebra K F] [Algebra P F]
    [IsScalarTower P K F] [FiniteDimensional K F] : Module.Finite P (integralClosure P F) := by
  haveI : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  obtain ⟨p, hp⟩ := ExpChar.exists k
  haveI : ExpChar P p := expChar_of_injective_algebraMap (algebraMap k P).injective p
  haveI : ExpChar K p := expChar_of_injective_algebraMap (IsFractionRing.injective P K) p
  haveI : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let E := separableClosure K F
  haveI : ExpChar E p := expChar_of_injective_algebraMap (algebraMap K E).injective p
  haveI : Module.Finite P (integralClosure P E) := IsIntegralClosure.finite P K E _
  haveI : IsScalarTower P E F := .of_algebraMap_eq' rfl
  let e := IsPurelyInseparable.exponent E F
  have hE : ∀ z : F, z ^ p ^ e ∈ E := fun z => by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' E p z
    exact hy ▸ y.2
  let f : integralClosure P F →ₛₗ[iterateFrobenius P p e] integralClosure P E :=
    { toFun := fun z => ⟨⟨z.1 ^ p ^ e, hE _⟩,
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom P E F) Subtype.val_injective).mp
          (IsIntegral.pow z.2 _)⟩
      map_add' := fun x y => Subtype.ext (Subtype.ext (add_pow_expChar_pow _ _ _ _))
      map_smul' := fun r x => Subtype.ext (Subtype.ext (by
        change (r • x.1) ^ p ^ e = (r ^ p ^ e) • x.1 ^ p ^ e
        rw [smul_pow])) }
  refine finite_of_semilinear_injective _ (finite_iterateFrobenius k P p e) f fun x y h => ?_
  have h1 : x.1 ^ p ^ e = y.1 ^ p ^ e := congrArg (fun w : integralClosure P E => (w.1.1 : F)) h
  exact Subtype.ext ((iterateFrobenius F p e).injective h1)

/- English proof (translation)
Take `⟨s, g, hinj, hfin⟩` from `exists_finite_inj_algHom_of_fg k B`. Set `P` to `MvPolynomial (Fin s) k`. Use `letI : Algebra P B := g.toRingHom.toAlgebra`. Use `haveI : Module.Finite P B := hfin`. Use `haveI : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`.

Use `letI : Algebra P F := ((algebraMap B F).comp (algebraMap P B)).toAlgebra`. Use `haveI : IsScalarTower P B F := .of_algebraMap_eq' rfl`. Use `letI : Algebra P L := ((algebraMap B L).comp (algebraMap P B)).toAlgebra`. Use `haveI : IsScalarTower P B L := .of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower P F L := .of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply B F L _`.

Use `haveI : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective _ _).mpr ((IsFractionRing.injective B F).comp hinj)`. Set `K` to `FractionRing P`. Use `letI : Algebra K F := FractionRing.liftAlgebra P F`. Use `haveI : FiniteDimensional K F := Module.Finite.of_isLocalization P B (nonZeroDivisors P)`. Use `letI : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra`.

Use `haveI : IsScalarTower K F L := .of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower P K L := .of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply K F L, ← IsScalarTower.algebraMap_apply P K F, ← IsScalarTower.algebraMap_apply P F L]`. Use `haveI : FiniteDimensional K L := Module.Finite.trans F L`. Use `haveI := finite_integralClosure_of_isIntegrallyClosed k P K L`.

Establish `h : Module.Finite P ((integralClosure B L).restrictScalars P)`. Rewrite using `[integralClosure_restrictScalars_of_isIntegral]` and apply the resulting hypothesis. Use `haveI : Module.Finite P (integralClosure B L) := h`. Conclude with `Module.Finite.of_restrictScalars_finite P B _`.
-/
theorem finite_integralClosure_of_perfectField (k B F L : Type*) [Field k] [PerfectField k]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] [Field F] [Algebra B F]
    [IsFractionRing B F] [Field L] [Algebra F L] [Algebra B L] [IsScalarTower B F L]
    [FiniteDimensional F L] : Module.Finite B (integralClosure B L) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  let P := MvPolynomial (Fin s) k
  letI : Algebra P B := g.toRingHom.toAlgebra
  haveI : Module.Finite P B := hfin
  haveI : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : Algebra P F := ((algebraMap B F).comp (algebraMap P B)).toAlgebra
  haveI : IsScalarTower P B F := .of_algebraMap_eq' rfl
  letI : Algebra P L := ((algebraMap B L).comp (algebraMap P B)).toAlgebra
  haveI : IsScalarTower P B L := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P F L := .of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply B F L _
  haveI : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    ((IsFractionRing.injective B F).comp hinj)
  let K := FractionRing P
  letI : Algebra K F := FractionRing.liftAlgebra P F
  haveI : FiniteDimensional K F := Module.Finite.of_isLocalization P B (nonZeroDivisors P)
  letI : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  haveI : IsScalarTower K F L := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P K L := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K F L, ← IsScalarTower.algebraMap_apply P K F,
      ← IsScalarTower.algebraMap_apply P F L]
  haveI : FiniteDimensional K L := Module.Finite.trans F L
  haveI := finite_integralClosure_of_isIntegrallyClosed k P K L
  have h : Module.Finite P ((integralClosure B L).restrictScalars P) := by
    rwa [integralClosure_restrictScalars_of_isIntegral]
  haveI : Module.Finite P (integralClosure B L) := h
  exact Module.Finite.of_restrictScalars_finite P B _

/- English proof (translation)
Introduce `k B`. Use `haveI : Algebra.FiniteType k B := .adjoin_of_finite (Set.toFinite _)`. Conclude with `finite_integralClosure_of_perfectField k B (FractionRing B) (FractionRing B)`.
-/
example : let k := AlgebraicClosure (ZMod 2)
    let B := Algebra.adjoin k ({Polynomial.X ^ 2, Polynomial.X ^ 3} : Set (Polynomial k))
    Module.Finite B (integralClosure B (FractionRing B)) := by
  intro k B
  haveI : Algebra.FiniteType k B := .adjoin_of_finite (Set.toFinite _)
  exact finite_integralClosure_of_perfectField k B (FractionRing B) (FractionRing B)

/- English proof (translation)
Introduce `k _ _ B _ _ _ _ F _ _ _` and use `finite_integralClosure_of_perfectField k B F F`.
-/
theorem finite_integralClosure_of_isAlgClosed :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (F : Type) [Field F] [Algebra B F] [IsFractionRing B F],
      Module.Finite B (integralClosure B F) :=
  fun k _ _ B _ _ _ _ F _ _ _ => finite_integralClosure_of_perfectField k B F F

end GlobalTheory.NormFin
