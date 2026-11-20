import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StIntClosureLocFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.StRelAlgClosureFinite
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

/- English proof (translation)
Introduce `F L _ _ φ S hS A T hDA hloc`. Set `: Algebra A L` to `(φ.comp A.subtype).toAlgebra`. Set `D : Subring F` to `Subring.closure (T : Set F)`. Establish `: Algebra.FiniteType ℤ D` using `Algebra.FiniteType.equiv ((Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T)) (Subring.closureEquivAdjoinInt _).symm`. Set `: Algebra D L` to `(φ.comp D.subtype).toAlgebra`.

Set `: Algebra D A` to `(Subring.inclusion hDA).toAlgebra`. Establish `: IsScalarTower D A L` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `K` to `FractionRing D`. Establish `hinj : Function.Injective (φ.comp D.subtype)` using `φ.injective.comp Subtype.val_injective`. Set `: Algebra K L` to `(IsFractionRing.lift hinj).toAlgebra`.

Establish `: IsScalarTower D K L` using `IsScalarTower.of_algebraMap_eq fun d => (IsFractionRing.lift_algebraMap hinj d).symm`. Establish `hKS : IntermediateField.adjoin K (S : Set L) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : x ∈ Subfield.closure (S : Set L)` using `hS ▸ Subfield.mem_top x`.

Conclude with `(Subfield.closure_le (t := (IntermediateField.adjoin K (S : Set L)).toSubfield)).mpr (IntermediateField.subset_adjoin K _) hx`. Set `M` to `algebraicClosure K L`. Establish `: FiniteDimensional K M` using `h K L S hKS`. Establish `: IsScalarTower D M L` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hfin : Module.Finite D (integralClosure D M)` using `GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full D K M`.

Take `⟨s, hs⟩` from `hfin.fg_top`. Use `⟨s.image fun g : integralClosure D M => ((g : M) : L), fun x hx => ?_⟩` and prove the remaining obligations. Set `U : Submonoid D` to `(IsUnit.submonoid A).comap (Subring.inclusion hDA)`. Establish `: IsLocalization U A`. Rewrite using `[isLocalization_iff]`.

Use `⟨fun y => y.2, fun z => ?_, fun {d₁ d₂} hd => ⟨1, ?_⟩⟩` and prove the remaining obligations. Take `⟨b, hb, c, hc, hc0, hcA, hzc⟩` from `hloc z z.2`. Establish `hunit : IsUnit (Subring.inclusion hDA ⟨c, hc⟩)` using `IsUnit.of_mul_eq_one (⟨c⁻¹, hcA⟩ : A) (Subtype.ext (mul_inv_cancel₀ hc0))`. Conclude with `⟨(⟨b, hb⟩, ⟨⟨c, hc⟩, hunit⟩), Subtype.ext hzc⟩`. Rewrite using `[Subring.inclusion_injective hDA hd]`.

Take `⟨⟨m, hm⟩, hmx⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := A) U x hx`. Take `⟨y, hy⟩ : ∃ y : L, y = (⟨m, hm⟩ : U) • x` from `⟨_, rfl⟩`. Rewrite `hmx` using `[← hy]`. Establish `hyK : IsIntegral K y` using `hmx.tower_top`. Set `yM : M` to `⟨y, hyK⟩`.

Establish `hyMint : IsIntegral D yM`. Rewrite using `[← isIntegral_algHom_iff (IsScalarTower.toAlgHom D M L) (fun a b hab => Subtype.ext hab)]`. Conclude with `hmx`. Establish `hyspan : (⟨yM, hyMint⟩ : integralClosure D M) ∈ Submodule.span D (s : Set _)` using `hs ▸ Submodule.mem_top`. Set `f : integralClosure D M →ₗ[D] L` to `(IsScalarTower.toAlgHom D M L).toLinearMap ∘ₗ (integralClosure D M).val.toLinearMap`.

Establish `hyD : y ∈ Submodule.span D ((s.image fun g : integralClosure D M => ((g : M) : L)) : Set L)`. Establish `hmap` using `Submodule.mem_map_of_mem (f := f) hyspan`. Rewrite `hmap` using `[Submodule.map_span]`. Rewrite using `[Finset.coe_image]`. Conclude with `hmap`.

Establish `hyA` using `Submodule.span_subset_span D A _ hyD`. Establish `hu : IsUnit (algebraMap D A m)` using `hm`. Establish `hyu : y = (hu.unit : A) • x`. Rewrite using `[hy, Submonoid.smul_def, IsUnit.unit_spec, algebraMap_smul]`. Establish `hx' : x = ((hu.unit⁻¹ : Aˣ) : A) • y`.

Rewrite using `[hyu, smul_smul, Units.inv_mul, one_smul]`. Rewrite using `[hx']`. Conclude with `Submodule.smul_mem _ _ hyA`.
-/
theorem IntClosureLocFinite.proof (h : RelAlgClosureFinite.Statement) :
    IntClosureLocFinite.Statement := by
  classical
  intro F L _ _ φ S hS A T hDA hloc
  let : Algebra A L := (φ.comp A.subtype).toAlgebra

  let D : Subring F := Subring.closure (T : Set F)
  have : Algebra.FiniteType ℤ D :=
    Algebra.FiniteType.equiv ((Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T))
      (Subring.closureEquivAdjoinInt _).symm
  let : Algebra D L := (φ.comp D.subtype).toAlgebra
  let : Algebra D A := (Subring.inclusion hDA).toAlgebra
  have : IsScalarTower D A L := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let K := FractionRing D
  have hinj : Function.Injective (φ.comp D.subtype) := φ.injective.comp Subtype.val_injective
  let : Algebra K L := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower D K L :=
    IsScalarTower.of_algebraMap_eq fun d => (IsFractionRing.lift_algebraMap hinj d).symm
  have hKS : IntermediateField.adjoin K (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subfield.closure (S : Set L) := hS ▸ Subfield.mem_top x
    exact (Subfield.closure_le (t := (IntermediateField.adjoin K (S : Set L)).toSubfield)).mpr
      (IntermediateField.subset_adjoin K _) hx

  let M := algebraicClosure K L
  have : FiniteDimensional K M := h K L S hKS
  have : IsScalarTower D M L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfin : Module.Finite D (integralClosure D M) :=
    GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full D K M
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨s.image fun g : integralClosure D M => ((g : M) : L), fun x hx => ?_⟩

  let U : Submonoid D := (IsUnit.submonoid A).comap (Subring.inclusion hDA)
  have : IsLocalization U A := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_, fun {d₁ d₂} hd => ⟨1, ?_⟩⟩
    · obtain ⟨b, hb, c, hc, hc0, hcA, hzc⟩ := hloc z z.2
      have hunit : IsUnit (Subring.inclusion hDA ⟨c, hc⟩) :=
        IsUnit.of_mul_eq_one (⟨c⁻¹, hcA⟩ : A) (Subtype.ext (mul_inv_cancel₀ hc0))
      exact ⟨(⟨b, hb⟩, ⟨⟨c, hc⟩, hunit⟩), Subtype.ext hzc⟩
    · rw [Subring.inclusion_injective hDA hd]
  obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := A) U x hx

  obtain ⟨y, hy⟩ : ∃ y : L, y = (⟨m, hm⟩ : U) • x := ⟨_, rfl⟩
  rw [← hy] at hmx
  have hyK : IsIntegral K y := hmx.tower_top
  let yM : M := ⟨y, hyK⟩
  have hyMint : IsIntegral D yM := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom D M L) (fun a b hab => Subtype.ext hab)]
    exact hmx
  have hyspan : (⟨yM, hyMint⟩ : integralClosure D M) ∈ Submodule.span D (s : Set _) :=
    hs ▸ Submodule.mem_top
  let f : integralClosure D M →ₗ[D] L :=
    (IsScalarTower.toAlgHom D M L).toLinearMap ∘ₗ (integralClosure D M).val.toLinearMap
  have hyD : y ∈ Submodule.span D ((s.image fun g : integralClosure D M => ((g : M) : L)) : Set L) := by
    have hmap := Submodule.mem_map_of_mem (f := f) hyspan
    rw [Submodule.map_span] at hmap
    rw [Finset.coe_image]
    exact hmap
  have hyA := Submodule.span_subset_span D A _ hyD

  have hu : IsUnit (algebraMap D A m) := hm
  have hyu : y = (hu.unit : A) • x := by
    rw [hy, Submonoid.smul_def, IsUnit.unit_spec, algebraMap_smul]
  have hx' : x = ((hu.unit⁻¹ : Aˣ) : A) • y := by
    rw [hyu, smul_smul, Units.inv_mul, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ hyA

end GroundTheory.Heights₂.Heights.Inter
