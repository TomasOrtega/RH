import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalkOfArithBase
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ClosedPt

/- English proof (translation)
Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem exists_prime_eq_zero_of_finiteType (κ : Type) [Field κ] [Algebra.FiniteType ℤ κ] :
    ∃ p : ℕ, p.Prime ∧ (p : κ) = 0 := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ κ := finite_of_finite_type_of_isJacobsonRing ℤ κ
  obtain ⟨q, hq⟩ := CharP.exists κ
  rcases CharP.char_is_prime_or_zero κ q with hqp | hq0
  · exact ⟨q, hqp, CharP.cast_eq_zero κ q⟩
  · subst hq0
    haveI : CharZero κ := CharP.charP_to_charZero κ
    exact absurd (isField_of_isIntegral_of_isField (R := ℤ) (S := κ) (algebraMap ℤ κ).injective_int (Field.toIsField κ))
      Int.not_isField

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isLocalHom_of_isCpl {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] {j : O →+* R} (h : IsCpl j) :
    IsLocalHom j := by
  obtain ⟨e, he⟩ := h
  refine ⟨fun a ha => ?_⟩
  rw [← he] at ha
  have h1 : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) a) := by
    simpa using ha.map e.symm
  have h2 := h1.map (AdicCompletion.evalₐ (maximalIdeal O) 1)
  rw [AlgHom.commutes] at h2
  by_contra hn
  have hm : a ∈ maximalIdeal O ^ 1 := by rw [pow_one]; exact hn
  have h0 : algebraMap O (O ⧸ maximalIdeal O ^ 1) a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  haveI : Nontrivial (O ⧸ maximalIdeal O ^ 1) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [pow_one]; exact (maximalIdeal.isMaximal O).ne_top)
  rw [h0] at h2
  exact not_isUnit_zero h2

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. A detailed English derivation is pending.
-/
theorem finiteType_residueField {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    (M : RatModel o' Ω) (x : M.Z) (hx : IsClosed ({x} : Set M.Z)) :
    Algebra.FiniteType ℤ (M.Z.residueField x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  haveI : IsClosedImmersion (M.Z.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.1 hx
  have h : LocallyOfFiniteType (M.Z.fromSpecResidueField x ≫ M.s) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of o') (M.Z.fromSpecResidueField x ≫ M.s)
  rw [← hφ] at h
  have h₁ : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  rw [← RingHom.finiteType_algebraMap]
  convert h₁.comp h₀
  exact RingHom.ext_int _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem closedPoint_cpl_residueChar : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsLocalHom j ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ maximalIdeal R := by
  intro o' Ω _ _ _ _ M x hx
  refine ⟨RatModel.essFiniteType_int_stalk_of_arithBase M x, fun R _ _ j hj => ?_⟩
  haveI hl := isLocalHom_of_isCpl hj
  refine ⟨hl, ?_⟩
  haveI := finiteType_residueField M x hx
  obtain ⟨p, hp, h0⟩ := exists_prime_eq_zero_of_finiteType (M.Z.residueField x)
  refine ⟨p, hp, ?_⟩
  have hm : (p : M.Z.presheaf.stalk x) ∈ maximalIdeal (M.Z.presheaf.stalk x) := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact h0
  rw [← map_natCast j p]
  exact map_nonunit j _ hm

end GlobalTheory.UPoinc.ClosedPt
