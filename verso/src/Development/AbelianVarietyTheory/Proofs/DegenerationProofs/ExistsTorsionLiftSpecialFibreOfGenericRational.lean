import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntermediateFieldOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `: FaithfulSMul V W` using `(faithfulSMul_iff_algebraMap_injective V W).2 hinj`. Establish `hfl : Module.Flat V W` using `inferInstance`. Establish `: Flat (spMap (algebraMap V W))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 hfl`.

Establish `: Surjective (spMap (algebraMap V W))` using `⟨Algebra.IsIntegral.comap_surjective V W⟩`. Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_spMap_of_finite_of_injective (V W : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [Algebra V W] [Module.Finite V W]
    (hinj : Function.Injective (algebraMap V W)) : Epi (spMap (algebraMap V W)) := by
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
  have hfl : Module.Flat V W := inferInstance
  have : Flat (spMap (algebraMap V W)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 hfl
  have : Surjective (spMap (algebraMap V W)) :=
    ⟨Algebra.IsIntegral.comap_surjective V W⟩
  exact Flat.epi_of_flat_of_surjective _

/- English proof (translation)
Introduce `hD hU V _ _ _ hV G _ _ _ _ C _ _ ga m hm hrat κ _ _ f hf x hx`. Take `⟨W, _, _, _, _, _, f', hfin, hinj, hloc, -, hcomp, hy⟩` from `exists_finite_extension_torsion_lift hU V G m hm κ f hf {x} (by simpa using hx)`. Take `⟨y, hy, hy'⟩` from `hy x (Finset.mem_singleton_self x)`. Set `: Algebra V C` to `(ga.comp (algebraMap V (FractionRing V))).toAlgebra`. Establish `hC : Function.Injective (algebraMap V C)` using `ga.injective.comp (IsFractionRing.injective V (FractionRing V))`.

Establish `: FaithfulSMul V W` using `(faithfulSMul_iff_algebraMap_injective V W).2 hinj`. Establish `: FaithfulSMul V C` using `(faithfulSMul_iff_algebraMap_injective V C).2 hC`. Set `β : W →ₐ[V] C` to `IsAlgClosed.lift`. Establish `hβ : Function.Injective β.toRingHom`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`.

Use `Ideal.eq_bot_of_comap_eq_bot (R := V) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comap_ker]`. Use `(RingHom.injective_iff_ker_eq_bot _).1 ?_` and prove the remaining obligations. Rewrite using `[show β.toRingHom.comp (algebraMap V W) = algebraMap V C from β.comp_algebraMap]`. Conclude with `hC`.

Establish `hβα : β.toRingHom.comp (algebraMap V W) = ga.comp (algebraMap V (FractionRing V))` using `β.comp_algebraMap`. Establish `hw : spMap β.toRingHom ≫ spMap (algebraMap V W) = spMap ga ≫ jK V`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hβα]`. Set `j : Over.mk (spMap ga ≫ jK V) ⟶ Over.mk (spMap (algebraMap V W))` to `Over.homMk (spMap β.toRingHom) hw`. Take `⟨x₀, hx₀⟩` from `hrat (j ≫ y) (by rw [← comp_pow, hy, comp_one])`.

Take `⟨h₀, hh₀, -⟩` from `hD V W C (algebraMap V W) β.toRingHom ga hloc hβ hβα G.left y.left x₀ hx₀.symm`. Establish `hepi` using `epi_spMap_of_finite_of_injective V W hinj`. Set `h : baseOver (Sp V) ⟶ G` to `Over.homMk h₀ (by`. Rewrite using `[← cancel_epi (spMap (algebraMap V W))]`. Conclude with `((reassoc_of% hh₀) _).trans ((Over.w y).trans (Category.comp_id _).symm))`.

Set `a : Over.mk (spMap (algebraMap V W)) ⟶ baseOver (Sp V)` to `Over.homMk (spMap (algebraMap V W)) (Category.comp_id _)`. Establish `ha : a ≫ h = y` using `Over.OverMorphism.ext hh₀`. Establish `: Epi a.left` using `hepi`. Establish `: Epi a` using `Over.epi_of_epi_left a`. Use `⟨h, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← cancel_epi a, comp_pow, ha, hy, comp_one]`. Rewrite using `[← hy', ← hh₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]`. Both sides reduce to the same expression.
-/
theorem exists_torsion_lift_of_generic_rational : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x) → UnramExtSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (C : Type) [Field C] [IsAlgClosed C] (ga : FractionRing V →+* C) (m : ℕ), IsUnit (m : V) → (∀ y : Over.mk (spMap ga ≫ jK V) ⟶ G, y ^ m = 1 → ∃ x : Sp (FractionRing V) ⟶ G.left, spMap ga ≫ x = y.left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∀ x : Over.mk (spMap f) ⟶ G, x ^ m = 1 → ∃ h : baseOver (Sp V) ⟶ G, h ^ m = 1 ∧ spMap f ≫ h.left = x.left := by
  intro hD hU V _ _ _ hV G _ _ _ _ C _ _ ga m hm hrat κ _ _ f hf x hx
  obtain ⟨W, _, _, _, _, _, f', hfin, hinj, hloc, -, hcomp, hy⟩ :=
    exists_finite_extension_torsion_lift hU V G m hm κ f hf {x} (by simpa using hx)
  obtain ⟨y, hy, hy'⟩ := hy x (Finset.mem_singleton_self x)
  let : Algebra V C := (ga.comp (algebraMap V (FractionRing V))).toAlgebra
  have hC : Function.Injective (algebraMap V C) :=
    ga.injective.comp (IsFractionRing.injective V (FractionRing V))
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
  have : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hC
  let β : W →ₐ[V] C := IsAlgClosed.lift
  have hβ : Function.Injective β.toRingHom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    rw [RingHom.comap_ker]
    refine (RingHom.injective_iff_ker_eq_bot _).1 ?_
    rw [show β.toRingHom.comp (algebraMap V W) = algebraMap V C from β.comp_algebraMap]
    exact hC
  have hβα : β.toRingHom.comp (algebraMap V W) = ga.comp (algebraMap V (FractionRing V)) :=
    β.comp_algebraMap
  have hw : spMap β.toRingHom ≫ spMap (algebraMap V W) = spMap ga ≫ jK V := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hβα]
  let j : Over.mk (spMap ga ≫ jK V) ⟶ Over.mk (spMap (algebraMap V W)) :=
    Over.homMk (spMap β.toRingHom) hw
  obtain ⟨x₀, hx₀⟩ := hrat (j ≫ y) (by rw [← comp_pow, hy, comp_one])
  obtain ⟨h₀, hh₀, -⟩ := hD V W C (algebraMap V W) β.toRingHom ga hloc hβ hβα G.left y.left x₀
    hx₀.symm
  have hepi := epi_spMap_of_finite_of_injective V W hinj
  let h : baseOver (Sp V) ⟶ G := Over.homMk h₀ (by
    rw [← cancel_epi (spMap (algebraMap V W))]
    exact ((reassoc_of% hh₀) _).trans ((Over.w y).trans (Category.comp_id _).symm))
  let a : Over.mk (spMap (algebraMap V W)) ⟶ baseOver (Sp V) :=
    Over.homMk (spMap (algebraMap V W)) (Category.comp_id _)
  have ha : a ≫ h = y := Over.OverMorphism.ext hh₀
  have : Epi a.left := hepi
  have : Epi a := Over.epi_of_epi_left a
  refine ⟨h, ?_, ?_⟩
  · rw [← cancel_epi a, comp_pow, ha, hy, comp_one]
  · rw [← hy', ← hh₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    rfl

end GlobalTheory
