import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.NormClosure

/- English proof (translation)
Use `IsLocalization.Away.mk _ (IsUnit.mk0 _ (by simpa using hϖ.ne_zero)) (fun z => ?_) fun a b h => ⟨0, by rw [IsFractionRing.injective O K h]⟩` and prove the remaining obligations. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := O) z`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ`. Use `⟨n, a * ↑u⁻¹, ?_⟩` and prove the remaining obligations.

Establish `h1 : algebraMap O K ϖ ≠ 0` using `by simpa using hϖ.ne_zero`. Establish `h2 : algebraMap O K u ≠ 0` using `by simp`. Establish `h3 : algebraMap O K ↑u⁻¹ = (algebraMap O K u)⁻¹` using `by simp`. Rewrite using `[map_mul, map_mul, map_pow, h3]`. Clear the denominators using the available nonvanishing facts.
-/
theorem isLocalization_away {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  refine IsLocalization.Away.mk _ (IsUnit.mk0 _ (by simpa using hϖ.ne_zero)) (fun z => ?_) fun a b h =>
    ⟨0, by rw [IsFractionRing.injective O K h]⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  have h1 : algebraMap O K ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have h2 : algebraMap O K u ≠ 0 := by simp
  have h3 : algebraMap O K ↑u⁻¹ = (algebraMap O K u)⁻¹ := by simp
  rw [map_mul, map_mul, map_pow, h3]
  field_simp

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ P F sP f hP hf hF hn hr`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Use `isLocalization_away (K := K) hϖ` as an intermediate fact. Establish `: IsOpenImmersion (spMap (algebraMap O K))` using `IsOpenImmersion.of_isLocalization ϖ`. Set `q : F ⟶ Sp K` to `IsOpenImmersion.lift (spMap (algebraMap O K)) (f ≫ sP) hr`.

Establish `hq : q ≫ spMap (algebraMap O K) = f ≫ sP` using `IsOpenImmersion.lift_fac _ _ _`. Establish `: IsProper sP`. Take `⟨N, i, hi, rfl⟩` from `hP`. Use `infer_instance`. Establish `: LocallyOfFiniteType (q ≫ spMap (algebraMap O K))` using `by rw [hq]; infer_instance`.

Establish `: LocallyOfFiniteType q` using `locallyOfFiniteType_of_comp q (spMap (algebraMap O K))`. Establish `: IsLocallyNoetherian F` using `LocallyOfFiniteType.isLocallyNoetherian q`. Establish `: IsNoetherian F` using `{}`. Establish `: QuasiCompact f` using `inferInstance`. Establish `: GlobalTheory.IsNormalScheme F` using `.of_pred hn`.

Establish `hfin : IsFinite f.fromNormalization` using `GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of O) f sP K q hq.symm`. Establish `hfl : Flat (f.fromNormalization ≫ sP)` using `GlobalTheory.flat_fromNormalization_comp f K sP q hq.symm`. Take `⟨n, e, he, hes⟩` from `GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hP`. Establish `hN : GlobalTheory.IsNormalScheme e.image` using `.of_isIso e.toImage`. Use `⟨n, e.ker, inv e.toImage ≫ f.fromNormalization, f.toNormalization ≫ e.toImage, ?_, GlobalTheory.IsNormalScheme.pred e.image, ?_, inferInstance, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, ← hes, IsIso.inv_comp_eq, ← Category.assoc]`. Conclude with `congrArg (· ≫ _) e.toImage_imageι.symm`. Rewrite using `[Category.assoc]`. Use `infer_instance`. Simplify using the standard rewrite rules.

Conclude with `(f.toNormalization ≫ e.toImage).denseRange`.
-/
theorem exists_normal_closure : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field K] [Algebra O K] [IsFractionRing O K] (P F : Scheme.{0}) (sP : P ⟶ Sp O) (f : F ⟶ P), IsProjOver sP → IsImmersion f → CompactSpace F → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme F → Set.range (f ≫ sP) ⊆ Set.range (spMap (algebraMap O K)) → ∃ (n : ℕ) (I : (PSpace O n).IdealSheafData) (ν : I.subscheme ⟶ P) (j : F ⟶ I.subscheme), ν ≫ sP = I.subschemeι ≫ PSpace.str O n ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme I.subscheme ∧ Flat (ν ≫ sP) ∧ IsOpenImmersion j ∧ j ≫ ν = f ∧ Dense (Set.range j) := by
  intro O K _ _ _ _ _ _ _ P F sP f hP hf hF hn hr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := isLocalization_away (K := K) hϖ
  have : IsOpenImmersion (spMap (algebraMap O K)) := IsOpenImmersion.of_isLocalization ϖ
  let q : F ⟶ Sp K := IsOpenImmersion.lift (spMap (algebraMap O K)) (f ≫ sP) hr
  have hq : q ≫ spMap (algebraMap O K) = f ≫ sP := IsOpenImmersion.lift_fac _ _ _
  have : IsProper sP := by
    obtain ⟨N, i, hi, rfl⟩ := hP
    infer_instance
  have : LocallyOfFiniteType (q ≫ spMap (algebraMap O K)) := by rw [hq]; infer_instance
  have : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q (spMap (algebraMap O K))
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian F := {}
  have : QuasiCompact f := inferInstance
  have : GlobalTheory.IsNormalScheme F := .of_pred hn
  have hfin : IsFinite f.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of O) f sP K q hq.symm
  have hfl : Flat (f.fromNormalization ≫ sP) := GlobalTheory.flat_fromNormalization_comp f K sP q hq.symm
  obtain ⟨n, e, he, hes⟩ := GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hP
  have hN : GlobalTheory.IsNormalScheme e.image := .of_isIso e.toImage
  refine ⟨n, e.ker, inv e.toImage ≫ f.fromNormalization, f.toNormalization ≫ e.toImage, ?_,
    GlobalTheory.IsNormalScheme.pred e.image, ?_, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hes, IsIso.inv_comp_eq, ← Category.assoc]
    exact congrArg (· ≫ _) e.toImage_imageι.symm
  · rw [Category.assoc]; infer_instance
  · simp
  · exact (f.toNormalization ≫ e.toImage).denseRange

end GlobalTheory.NormClosure
