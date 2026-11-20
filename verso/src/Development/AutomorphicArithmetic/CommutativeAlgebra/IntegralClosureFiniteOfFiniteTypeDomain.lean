import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.EtaleCohomology.EtaleSheaves.LeafIntClosureAlgPf
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherReduction
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherCharP

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

open scoped IntermediateField.algebraAdjoinAdjoin in
/- English proof (translation)
Introduce `Ω L _ _ _ u _ hfd`. Establish `: Algebra.FiniteType Ω (Algebra.adjoin Ω {u})` using `.adjoin_of_finite (Set.finite_singleton u)`. Use `GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_of_forall_mvPolynomial Ω (Algebra.adjoin Ω {u}) (IntermediateField.adjoin Ω {u}) L ?_` and prove the remaining obligations. Introduce `s L' _ _ _ _ _`. Take `⟨p, hp⟩` from `CharP.exists Ω`.

Break down `CharP.char_is_prime_or_zero Ω p with hpr | rfl` into its components or cases. Use `haveI : Fact p.Prime := ⟨hpr⟩`. Conclude with `GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charP Ω p s L'`. Use `haveI : CharZero Ω := CharP.charP_to_charZero Ω`. Conclude with `GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charZero Ω s L'`.
-/
theorem UpperTheory.integralClosure_finite_of_finiteType_domain :
    LateralTheory.E.LeafIntClosureAlgPf.LeafIntClFinite := by
  intro Ω L _ _ _ u _ hfd
  have : Algebra.FiniteType Ω (Algebra.adjoin Ω {u}) :=
    .adjoin_of_finite (Set.finite_singleton u)
  refine GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_of_forall_mvPolynomial
    Ω (Algebra.adjoin Ω {u}) (IntermediateField.adjoin Ω {u}) L ?_
  intro s L' _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists Ω
  rcases CharP.char_is_prime_or_zero Ω p with hpr | rfl
  · haveI : Fact p.Prime := ⟨hpr⟩
    exact GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charP Ω p s L'
  · haveI : CharZero Ω := CharP.charP_to_charZero Ω
    exact GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charZero Ω s L'
