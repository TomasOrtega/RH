import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.ExtExists

/- English proof (translation)
Use `haveI : Algebra.IsSeparable K L := inferInstance`. Use `haveI : IsDedekindDomain (integralClosure O L) := integralClosure.isDedekindDomain O K L`. Use `haveI : IsFractionRing (integralClosure O L) L := integralClosure.isFractionRing_of_finite_extension K L`. Use `haveI : Algebra.IsIntegral O (integralClosure O L) := inferInstance`. Establish `hinjOL : Function.Injective (algebraMap O L)`.

Rewrite using `[IsScalarTower.algebraMap_eq O K L]`. Conclude with `(algebraMap K L).injective.comp (IsFractionRing.injective O K)`. Establish `hinjA : Function.Injective (algebraMap O (integralClosure O L))` using `fun a b h => hinjOL (congrArg (fun w : integralClosure O L => (w : L)) h)`. Establish `hinjAL : Function.Injective (algebraMap (integralClosure O L) L)` using `Subtype.val_injective`. Take `⟨P, hPmax, hPover⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := integralClosure O L) (IsLocalRing.maximalIdeal O) (fun x hx => by`.

Rewrite `hx` using `[RingHom.mem_ker]`. Rewrite using `[hinjA (hx.trans (map_zero _).symm)]`. Conclude with `Ideal.zero_mem _)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hϖP : algebraMap O (integralClosure O L) ϖ ∈ P`.

Rewrite using `[← Ideal.mem_comap, hPover, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hϖ.not_isUnit`. Establish `hP0 : P ≠ ⊥`. Introduce `h`. Rewrite `hϖP` using `[h, Ideal.mem_bot]`.

Conclude with `hϖ.ne_zero (hinjA (hϖP.trans (map_zero _).symm))`. Use `haveI := hPmax.isPrime`. Use `haveI hdvr : IsDiscreteValuationRing (Localization.AtPrime P) := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hP0 _`. Establish `hAW : Function.Injective (algebraMap (integralClosure O L) (Localization.AtPrime P))` using `IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P)`. Establish `hunit : ∀ y : P.primeCompl, IsUnit (algebraMap (integralClosure O L) L y)` using `fun y => IsUnit.mk0 _ fun h => y.2 (by`.

Establish `: (y : integralClosure O L) = 0` using `hinjAL (h.trans (map_zero _).symm)`. Rewrite using `[this]`. Conclude with `Ideal.zero_mem _)`. Set `f : Localization.AtPrime P →+* L` to `IsLocalization.lift (M := P.primeCompl) hunit`. Establish `hf : ∀ a, f (algebraMap (integralClosure O L) (Localization.AtPrime P) a) = algebraMap (integralClosure O L) L a` using `fun a => IsLocalization.lift_eq hunit a`.

Establish `hfinj : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨⟨a, s⟩, h⟩` from `IsLocalization.surj P.primeCompl x`. Establish `h1` using `congrArg f h`.

Rewrite `h1` using `[map_mul, hx, zero_mul, hf]`. Establish `ha : a = 0` using `hinjAL (h1.symm.trans (map_zero _).symm)`. Rewrite `h` using `[ha, map_zero]`. Establish `hs : algebraMap (integralClosure O L) (Localization.AtPrime P) s ≠ 0` using `(IsLocalization.map_units (Localization.AtPrime P) s).ne_zero`. Conclude with `(mul_eq_zero.1 h).resolve_right hs`.

Use `letI algWL : Algebra (Localization.AtPrime P) L := f.toAlgebra`. Establish `hOW : ∀ x : O, algebraMap O (Localization.AtPrime P) x = algebraMap (integralClosure O L) (Localization.AtPrime P) (algebraMap O (integralClosure O L) x)` using `fun x => IsScalarTower.algebraMap_apply O (integralClosure O L) (Localization.AtPrime P) x`. Establish `hWL : ∀ x, algebraMap (Localization.AtPrime P) L x = f x` using `fun _ => rfl`. Use `haveI tower : IsScalarTower O (Localization.AtPrime P) L := IsScalarTower.of_algebraMap_eq (R := O) (S := Localization.AtPrime P) (A := L) fun x => by`. Rewrite using `[hOW, hWL, hf]`.

Both sides reduce to the same expression. Establish `hloc : IsLocalHom (algebraMap O (Localization.AtPrime P))` using `⟨fun x hx => by`. Assume the negation of the conclusion as `hxu`. Establish `hxm : x ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Conclude with `hxu`. Rewrite `hxm` using `[← hPover, Ideal.mem_comap]`. Establish `hm` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hxm`. Rewrite `hm` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hm (by rw [← hOW]; exact hx)⟩`.

Use `haveI hOLalg : Algebra.IsAlgebraic O L := (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := K) (C := L)).2 inferInstance`. Establish `halg : Algebra.IsAlgebraic O (Localization.AtPrime P)` using `⟨fun x => (isAlgebraic_algebraMap_iff (A := L) hfinj).1 (Algebra.IsAlgebraic.isAlgebraic _)⟩`. Establish `hzint : _root_.IsIntegral O z` using `IsIntegral.of_pow hn (hz.pow_eq_one ▸ isIntegral_one)`. Set `zA : integralClosure O L` to `⟨z, hzint⟩`. Establish `hfz : f (algebraMap (integralClosure O L) (Localization.AtPrime P) zA) = z` using `hf zA`.

Use `⟨Localization.AtPrime P, inferInstance, inferInstance, hdvr, inferInstance, hloc, halg, algWL, tower, algebraMap (integralClosure O L) (Localization.AtPrime P) zA, hfinj, ?_, hfz⟩` and prove the remaining obligations. Conclude with `IsPrimitiveRoot.of_map_of_injective (f := f) (by rw [hfz]; exact hz) hfinj`.
-/
theorem exists_dvr_in_finite_ext (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K]
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra O L] [IsScalarTower O K L]
    (z : L) (n : ℕ) (hn : 0 < n) (hz : IsPrimitiveRoot z n) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O')
      (_ : Algebra O' L) (_ : IsScalarTower O O' L) (ζ : O'),
      Function.Injective (algebraMap O' L) ∧ IsPrimitiveRoot ζ n ∧ algebraMap O' L ζ = z := by
  haveI : Algebra.IsSeparable K L := inferInstance
  haveI : IsDedekindDomain (integralClosure O L) := integralClosure.isDedekindDomain O K L
  haveI : IsFractionRing (integralClosure O L) L := integralClosure.isFractionRing_of_finite_extension K L
  haveI : Algebra.IsIntegral O (integralClosure O L) := inferInstance
  have hinjOL : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)
  have hinjA : Function.Injective (algebraMap O (integralClosure O L)) := fun a b h =>
    hinjOL (congrArg (fun w : integralClosure O L => (w : L)) h)
  have hinjAL : Function.Injective (algebraMap (integralClosure O L) L) := Subtype.val_injective
  obtain ⟨P, hPmax, hPover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := integralClosure O L) (IsLocalRing.maximalIdeal O)
    (fun x hx => by
      rw [RingHom.mem_ker] at hx
      rw [hinjA (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖP : algebraMap O (integralClosure O L) ϖ ∈ P := by
    rw [← Ideal.mem_comap, hPover, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hϖ.not_isUnit
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hϖP
    exact hϖ.ne_zero (hinjA (hϖP.trans (map_zero _).symm))
  haveI := hPmax.isPrime
  haveI hdvr : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hP0 _
  have hAW : Function.Injective (algebraMap (integralClosure O L) (Localization.AtPrime P)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap (integralClosure O L) L y) := fun y =>
    IsUnit.mk0 _ fun h => y.2 (by
      have : (y : integralClosure O L) = 0 := hinjAL (h.trans (map_zero _).symm)
      rw [this]; exact Ideal.zero_mem _)
  let f : Localization.AtPrime P →+* L := IsLocalization.lift (M := P.primeCompl) hunit
  have hf : ∀ a, f (algebraMap (integralClosure O L) (Localization.AtPrime P) a) =
      algebraMap (integralClosure O L) L a := fun a => IsLocalization.lift_eq hunit a
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj P.primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf] at h1
    have ha : a = 0 := hinjAL (h1.symm.trans (map_zero _).symm)
    rw [ha, map_zero] at h
    have hs : algebraMap (integralClosure O L) (Localization.AtPrime P) s ≠ 0 :=
      (IsLocalization.map_units (Localization.AtPrime P) s).ne_zero
    exact (mul_eq_zero.1 h).resolve_right hs
  letI algWL : Algebra (Localization.AtPrime P) L := f.toAlgebra
  have hOW : ∀ x : O, algebraMap O (Localization.AtPrime P) x =
      algebraMap (integralClosure O L) (Localization.AtPrime P) (algebraMap O (integralClosure O L) x) :=
    fun x => IsScalarTower.algebraMap_apply O (integralClosure O L) (Localization.AtPrime P) x
  have hWL : ∀ x, algebraMap (Localization.AtPrime P) L x = f x := fun _ => rfl
  haveI tower : IsScalarTower O (Localization.AtPrime P) L :=
    IsScalarTower.of_algebraMap_eq (R := O) (S := Localization.AtPrime P) (A := L) fun x => by
      rw [hOW, hWL, hf]; rfl
  have hloc : IsLocalHom (algebraMap O (Localization.AtPrime P)) := ⟨fun x hx => by
    by_contra hxu
    have hxm : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hxu
    rw [← hPover, Ideal.mem_comap] at hxm
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hxm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm (by rw [← hOW]; exact hx)⟩
  haveI hOLalg : Algebra.IsAlgebraic O L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := K) (C := L)).2 inferInstance
  have halg : Algebra.IsAlgebraic O (Localization.AtPrime P) :=
    ⟨fun x => (isAlgebraic_algebraMap_iff (A := L) hfinj).1 (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have hzint : _root_.IsIntegral O z := IsIntegral.of_pow hn (hz.pow_eq_one ▸ isIntegral_one)
  let zA : integralClosure O L := ⟨z, hzint⟩
  have hfz : f (algebraMap (integralClosure O L) (Localization.AtPrime P) zA) = z := hf zA
  refine ⟨Localization.AtPrime P, inferInstance, inferInstance, hdvr, inferInstance, hloc, halg, algWL, tower,
    algebraMap (integralClosure O L) (Localization.AtPrime P) zA, hfinj, ?_, hfz⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := f) (by rw [hfz]; exact hz) hfinj

/- English proof (translation)
Use `haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hinj`. Use `letI algKΩ : Algebra (FractionRing O) Ω := FractionRing.liftAlgebra O Ω`. Use `haveI towKΩ : IsScalarTower O (FractionRing O) Ω := FractionRing.isScalarTower_liftAlgebra O Ω`. Use `haveI : CharZero (FractionRing O) := ((algebraMap (FractionRing O) Ω).charZero_iff (algebraMap (FractionRing O) Ω).injective).2 inferInstance`. Use `letI algKΩ' : Algebra (FractionRing O) Ω' := ((algebraMap Ω Ω').comp (algebraMap (FractionRing O) Ω)).toAlgebra`.

Use `haveI towK : IsScalarTower O (FractionRing O) Ω' := IsScalarTower.of_algebraMap_eq fun x => by`. Express the relevant statement in the definitionally equal form `_ = algebraMap Ω Ω' (algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) x))`. Rewrite using `[← IsScalarTower.algebraMap_apply O (FractionRing O) Ω, ← IsScalarTower.algebraMap_apply O Ω Ω']`. Establish `hzi : _root_.IsIntegral (FractionRing O) z` using `IsIntegral.of_pow hn (hz.pow_eq_one ▸ isIntegral_one)`. Use `haveI : FiniteDimensional (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) := IntermediateField.adjoin.finiteDimensional hzi`.

Establish `hgen : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen (FractionRing O) z) n` using `IsPrimitiveRoot.of_map_of_injective (f := algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω') (by rw [IntermediateField.AdjoinSimple.algebraMap_gen]; exact hz) (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').injective`. Take `⟨O', i1, i2, i3, i4, i5, i6, i7, i8, ζ, hinjL, hζ, hζz⟩` from `exists_dvr_in_finite_ext O (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) (IntermediateField.AdjoinSimple.gen (FractionRing O) z) n hn hgen`. Use `haveI towL : IsScalarTower O (IntermediateField.adjoin (FractionRing O) {z}) Ω' := IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply O (FractionRing O) Ω', IsScalarTower.algebraMap_apply O (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}), ← IsScalarTower.algebraMap_apply (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) Ω']`. Use `letI algO'Ω' : Algebra O' Ω' := ((algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').comp (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}))).toAlgebra`.

Establish `hO'Ω' : ∀ x : O', algebraMap O' Ω' x = algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω' (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}) x)` using `fun _ => rfl`. Use `haveI tow : IsScalarTower O O' Ω' := IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[hO'Ω', ← IsScalarTower.algebraMap_apply O O' (IntermediateField.adjoin (FractionRing O) {z}), ← IsScalarTower.algebraMap_apply O (IntermediateField.adjoin (FractionRing O) {z}) Ω']`. Use `⟨O', i1, i2, i3, i4, i5, i6, algO'Ω', tow, ζ, ?_, hζ, ?_⟩` and prove the remaining obligations. Establish `: (algebraMap O' Ω' : O' → Ω') = (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω') ∘ (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}))` using `rfl`.

Rewrite using `[this]`. Conclude with `(algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').injective.comp hinjL`. Rewrite using `[hO'Ω', hζz, IntermediateField.AdjoinSimple.algebraMap_gen]`. Conclude with `htop`.
-/
theorem exists_dvr_of_generator (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (hinj : Function.Injective (algebraMap O Ω))
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O Ω'] [IsScalarTower O Ω Ω']
    (z : Ω') (n : ℕ) (hn : 0 < n) (hz : IsPrimitiveRoot z n) (htop : Algebra.adjoin Ω {z} = ⊤) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O')
      (_ : Algebra O' Ω') (_ : IsScalarTower O O' Ω') (ζ : O'),
      Function.Injective (algebraMap O' Ω') ∧ IsPrimitiveRoot ζ n ∧
        Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ := by
  haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hinj
  letI algKΩ : Algebra (FractionRing O) Ω := FractionRing.liftAlgebra O Ω
  haveI towKΩ : IsScalarTower O (FractionRing O) Ω := FractionRing.isScalarTower_liftAlgebra O Ω
  haveI : CharZero (FractionRing O) :=
    ((algebraMap (FractionRing O) Ω).charZero_iff (algebraMap (FractionRing O) Ω).injective).2 inferInstance
  letI algKΩ' : Algebra (FractionRing O) Ω' :=
    ((algebraMap Ω Ω').comp (algebraMap (FractionRing O) Ω)).toAlgebra
  haveI towK : IsScalarTower O (FractionRing O) Ω' := IsScalarTower.of_algebraMap_eq fun x => by
    change _ = algebraMap Ω Ω' (algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) x))
    rw [← IsScalarTower.algebraMap_apply O (FractionRing O) Ω, ← IsScalarTower.algebraMap_apply O Ω Ω']
  have hzi : _root_.IsIntegral (FractionRing O) z := IsIntegral.of_pow hn (hz.pow_eq_one ▸ isIntegral_one)
  haveI : FiniteDimensional (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) :=
    IntermediateField.adjoin.finiteDimensional hzi
  have hgen : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen (FractionRing O) z) n :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω')
      (by rw [IntermediateField.AdjoinSimple.algebraMap_gen]; exact hz)
      (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').injective
  obtain ⟨O', i1, i2, i3, i4, i5, i6, i7, i8, ζ, hinjL, hζ, hζz⟩ :=
    exists_dvr_in_finite_ext O (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z})
      (IntermediateField.AdjoinSimple.gen (FractionRing O) z) n hn hgen
  haveI towL : IsScalarTower O (IntermediateField.adjoin (FractionRing O) {z}) Ω' :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω',
        IsScalarTower.algebraMap_apply O (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}),
        ← IsScalarTower.algebraMap_apply (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) Ω']
  letI algO'Ω' : Algebra O' Ω' :=
    ((algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').comp
      (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}))).toAlgebra
  have hO'Ω' : ∀ x : O', algebraMap O' Ω' x =
      algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω'
        (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}) x) := fun _ => rfl
  haveI tow : IsScalarTower O O' Ω' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hO'Ω', ← IsScalarTower.algebraMap_apply O O' (IntermediateField.adjoin (FractionRing O) {z}),
      ← IsScalarTower.algebraMap_apply O (IntermediateField.adjoin (FractionRing O) {z}) Ω']
  refine ⟨O', i1, i2, i3, i4, i5, i6, algO'Ω', tow, ζ, ?_, hζ, ?_⟩
  · have : (algebraMap O' Ω' : O' → Ω') =
        (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω') ∘
          (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z})) := rfl
    rw [this]
    exact (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').injective.comp hinjL
  · rw [hO'Ω', hζz, IntermediateField.AdjoinSimple.algebraMap_gen]
    exact htop

end GlobalTheory.CompanionTheory.Ar.Num.ExtExists

namespace GlobalTheory.CompanionTheory.Ar.Num

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ _ hinj n hn`. Use `haveI : NeZero n := ⟨hn.ne'⟩`. Use `haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩`. Establish `hz` using `IsCyclotomicExtension.zeta_spec n Ω (CyclotomicField n Ω)`. Take `⟨O', i1, i2, i3, i4, i5, i6, i7, i8, ζ, h1, h2, h3⟩` from `ExtExists.exists_dvr_of_generator O Ω hinj (CyclotomicField n Ω) _ n hn hz (IsCyclotomicExtension.adjoin_primitive_root_eq_top hz)`.

Conclude with `⟨O', i1, i2, i3, i4, i5, i6, CyclotomicField n Ω, inferInstance, inferInstance, i7, inferInstance, i8, inferInstance, ζ, h1, h2, h3⟩`.
-/
theorem exists_ext_primitive_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ n : ℕ, 0 < n → ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O') (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (_ : Algebra O' Ω') (_ : Algebra O Ω') (_ : IsScalarTower O O' Ω') (_ : IsScalarTower O Ω Ω') (ζ : O'), Function.Injective (algebraMap O' Ω') ∧ IsPrimitiveRoot ζ n ∧ Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ := by
  intro O _ _ _ Ω _ _ _ hinj n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have hz := IsCyclotomicExtension.zeta_spec n Ω (CyclotomicField n Ω)
  obtain ⟨O', i1, i2, i3, i4, i5, i6, i7, i8, ζ, h1, h2, h3⟩ :=
    ExtExists.exists_dvr_of_generator O Ω hinj (CyclotomicField n Ω) _ n hn hz
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hz)
  exact ⟨O', i1, i2, i3, i4, i5, i6, CyclotomicField n Ω, inferInstance, inferInstance, i7, inferInstance, i8, inferInstance, ζ, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.Ar.Num
