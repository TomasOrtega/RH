import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitLocal

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem comap_maximalIdeal_of_irreducible {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (ϖ : V) (hϖ : Irreducible (h ϖ)) :
    Ideal.comap h (maximalIdeal V') = maximalIdeal V := by
  have hne : Ideal.comap h (maximalIdeal V') ≠ ⊥ := by
    intro h0
    have : ϖ ∈ Ideal.comap h (maximalIdeal V') := hϖ.not_isUnit
    rw [h0, Ideal.mem_bot] at this
    exact hϖ.ne_zero (by rw [this, map_zero])
  haveI : (Ideal.comap h (maximalIdeal V')).IsPrime := Ideal.comap_isPrime _ _
  exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem maximalIdeal_le_map {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R]
    [IsLocalRing R] (j : O →+* R) (hj : IsCpl j) : maximalIdeal R ≤ Ideal.map j (maximalIdeal O) := by
  obtain ⟨e, he⟩ := hj
  have fg : (maximalIdeal O).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal O) O) := AdicCompletion.isLocalRing_of_fg fg
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  intro r hr
  have h1 : e.symm r ∈ maximalIdeal (AdicCompletion (maximalIdeal O) O) := by
    intro hu
    have := hu.map e
    rw [RingEquiv.apply_symm_apply] at this
    exact hr this
  rw [hm] at h1
  have h2 := Ideal.mem_map_of_mem (e : AdicCompletion (maximalIdeal O) O →+* R) h1
  rw [Ideal.map_map] at h2
  have h3 : (e : AdicCompletion (maximalIdeal O) O →+* R).comp (algebraMap O _) = j := by
    first | exact he | exact RingHom.ext he | exact he.symm
  rw [h3] at h2
  simpa using h2

end GlobalTheory.Poinc.TraitLocal

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction.

A detailed English derivation is pending.
-/
theorem GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (g' : R →+* V') (ξ : Sp V ⟶ M.Z), Irreducible (h ϖ) → ξ (IsLocalRing.closedPoint V) = x → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → IsLocalHom g' := by
  intro o' Ω _ _ _ hA M x R _ _ j hj V _ _ _ ϖ V' _ _ _ h g' ξ hϖ hξ hsq
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have h1 : spMap h (closedPoint V') = closedPoint V :=
    PrimeSpectrum.ext (GlobalTheory.Poinc.TraitLocal.comap_maximalIdeal_of_irreducible h ϖ hϖ)
  have h2 : (spMap h ≫ ξ) (closedPoint V') = x :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg ξ h1).trans hξ)
  rw [← hsq] at h2
  have h3 : M.Z.fromSpecStalk x (spMap j (spMap g' (closedPoint V'))) =
      M.Z.fromSpecStalk x (closedPoint (M.Z.presheaf.stalk x)) :=
    h2.trans Scheme.fromSpecStalk_closedPoint.symm
  have h4 := (M.Z.fromSpecStalk x).isEmbedding.injective h3
  have h5 : Ideal.comap j (Ideal.comap g' (maximalIdeal V')) = maximalIdeal (M.Z.presheaf.stalk x) :=
    congrArg PrimeSpectrum.asIdeal h4
  have h6 : maximalIdeal R ≤ Ideal.comap g' (maximalIdeal V') :=
    (GlobalTheory.Poinc.TraitLocal.maximalIdeal_le_map j hj).trans (Ideal.map_le_iff_le_comap.2 h5.ge)
  refine ⟨fun r hr => ?_⟩
  by_contra hn
  exact h6 (show r ∈ maximalIdeal R from hn) hr
