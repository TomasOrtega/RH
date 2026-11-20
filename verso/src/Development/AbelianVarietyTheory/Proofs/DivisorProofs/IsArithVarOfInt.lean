import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

namespace GlobalTheory.AlterationOrder

/- English proof (translation)
Unfold `spMap`. Rewrite using `[IsFinite.SpecMap_iff]`. Express the relevant statement in the definitionally equal form `(algebraMap ℤ k).Finite`. Conclude with `RingHom.finite_algebraMap.2 h`.
-/
theorem isFinite_spMap_int (k : Type) [CommRing k] (h : Module.Finite ℤ k) :
    IsFinite (spMap (Int.castRingHom k)) := by
  unfold spMap
  rw [IsFinite.SpecMap_iff]
  change (algebraMap ℤ k).Finite
  exact RingHom.finite_algebraMap.2 h

/- English proof (translation)
The claim follows from `specZIsTerminal.hom_ext f g`.
-/
theorem hom_ext_int {X : Scheme.{0}} (f g : X ⟶ Sp ℤ) : f = g :=
  specZIsTerminal.hom_ext f g

/- English proof (translation)
Use `isFinite_spMap_int k h.finite` as an intermediate fact. Take `⟨hp, L, hL⟩` from `(isProjOver_iff_isProper_and_exists_isAmpleLB r).1 h.isProjOver`. Use `⟨inferInstance, inferInstance, h.isIntegral, hL.isProjOver _, ?_, h.dim_eq⟩` and prove the remaining obligations. Rewrite using `[hom_ext_int (_ ≫ spMap (Int.castRingHom ℤ)) (r ≫ spMap (Int.castRingHom k))]`. Conclude with `h.flat`.
-/
theorem isArithVar_int {k : Type} [CommRing k] {Z : Scheme.{0}} {r : Z ⟶ Sp k} {d : ℕ}
    (h : IsArithVar r d) : IsArithVar (r ≫ spMap (Int.castRingHom k)) d := by
  have := isFinite_spMap_int k h.finite
  obtain ⟨hp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB r).1 h.isProjOver
  refine ⟨inferInstance, inferInstance, h.isIntegral, hL.isProjOver _, ?_, h.dim_eq⟩
  rw [hom_ext_int (_ ≫ spMap (Int.castRingHom ℤ)) (r ≫ spMap (Int.castRingHom k))]
  exact h.flat

/- English proof (translation)
Use `isFinite_spMap_int k hf` as an intermediate fact. Take `⟨hp, L, hL⟩` from `(isProjOver_iff_isProper_and_exists_isAmpleLB _).1 h.isProjOver`. Establish `: IsProper r` using `IsProper.of_comp r (spMap (Int.castRingHom k))`. Use `⟨hd, hf, h.isIntegral, hL.isProjOver _, ?_, h.dim_eq⟩` and prove the remaining obligations. Rewrite using `[hom_ext_int (r ≫ spMap (Int.castRingHom k)) ((r ≫ spMap (Int.castRingHom k)) ≫ spMap (Int.castRingHom ℤ))]`.

Conclude with `h.flat`.
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
Introduce `H k _ Z _ r d h`. Take `⟨Y, hY, ρ, h1, h2, h3, h4⟩` from `H Z _ d (isArithVar_int h)`. Use `⟨Y, hY, ρ, isArithVar_of_int h.isDomain h.finite ?_, h2, h3, h4⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]` and apply the resulting hypothesis.
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
