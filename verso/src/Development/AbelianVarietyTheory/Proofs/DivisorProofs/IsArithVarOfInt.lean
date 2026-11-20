import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

namespace GlobalTheory.AlterationOrder

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem isFinite_spMap_int (k : Type) [CommRing k] (h : Module.Finite ℤ k) :
    IsFinite (spMap (Int.castRingHom k)) := by
  unfold spMap
  rw [IsFinite.SpecMap_iff]
  change (algebraMap ℤ k).Finite
  exact RingHom.finite_algebraMap.2 h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hom_ext_int {X : Scheme.{0}} (f g : X ⟶ Sp ℤ) : f = g :=
  specZIsTerminal.hom_ext f g

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isArithVar_int {k : Type} [CommRing k] {Z : Scheme.{0}} {r : Z ⟶ Sp k} {d : ℕ}
    (h : IsArithVar r d) : IsArithVar (r ≫ spMap (Int.castRingHom k)) d := by
  have := isFinite_spMap_int k h.finite
  obtain ⟨hp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB r).1 h.isProjOver
  refine ⟨inferInstance, inferInstance, h.isIntegral, hL.isProjOver _, ?_, h.dim_eq⟩
  rw [hom_ext_int (_ ≫ spMap (Int.castRingHom ℤ)) (r ≫ spMap (Int.castRingHom k))]
  exact h.flat

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isArithVar_of_int {k : Type} [CommRing k] (hd : IsDomain k) (hf : Module.Finite ℤ k)
    {Z : Scheme.{0}} {r : Z ⟶ Sp k} {d : ℕ} (h : IsArithVar (r ≫ spMap (Int.castRingHom k)) d) :
    IsArithVar r d := by
  have := isFinite_spMap_int k hf
  obtain ⟨hp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 h.isProjOver
  have : IsProper r := IsProper.of_comp r (spMap (Int.castRingHom k))
  refine ⟨hd, hf, h.isIntegral, hL.isProjOver _, ?_, h.dim_eq⟩
  rw [hom_ext_int (r ≫ spMap (Int.castRingHom k))
    ((r ≫ spMap (Int.castRingHom k)) ≫ spMap (Int.castRingHom ℤ))]
  exact h.flat

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
theorem regularAlteration_order : RegularAlteration → ∀ (k : Type) [CommRing k] (Z : Scheme.{0}) [IsIntegral Z] (r : Z ⟶ Sp k) (d : ℕ),
    IsArithVar r d → ∃ (B' : Scheme.{0}) (_ : IsIntegral B') (ρ : B' ⟶ Z), IsArithVar (ρ ≫ r) d ∧
      (∀ b : B', IsRegularLocalRing (B'.presheaf.stalk b)) ∧ ρ (genericPoint B') = genericPoint Z ∧
      ρ.residueDegree (genericPoint B') ≠ 0 := by
  intro H k _ Z _ r d h
  obtain ⟨Y, hY, ρ, h1, h2, h3, h4⟩ := H Z _ d (isArithVar_int h)
  refine ⟨Y, hY, ρ, isArithVar_of_int h.isDomain h.finite ?_, h2, h3, h4⟩
  rwa [Category.assoc]

end GlobalTheory.AlterationOrder
