import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AffineLineExt

open Polynomial

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun J => by rw [← IsLocalization.map_under (Submonoid.powers r) (Localization.Away r) J] obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (J.under R)).principal rw [ha] exact ⟨⟨_, by rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]⟩⟩⟩`.
-/
theorem isPrincipalIdealRing_away {R : Type} [CommRing R] [IsPrincipalIdealRing R] (r : R) :
    IsPrincipalIdealRing (Localization.Away r) := ⟨fun J => by
  rw [← IsLocalization.map_under (Submonoid.powers r) (Localization.Away r) J]
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (J.under R)).principal
  rw [ha]
  exact ⟨⟨_, by rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]⟩⟩⟩

/- English proof (translation)
Introduce `k _ B _ _ P c hP u hu`. Establish `hQ0 : P * (X - C c) ≠ 0` using `mul_ne_zero hP (X_sub_C_ne_zero c)`. Use `haveI : IsDomain (Localization.Away P) := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hP)`. Use `haveI : IsDomain (Localization.Away (P * (X - C c))) := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hQ0)`. Use `haveI : IsPrincipalIdealRing (Localization.Away P) := isPrincipalIdealRing_away P`.

Establish `hφ : ∀ a : k[X], IsLocalization.Away.awayToAwayRight (S` using `Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c) (algebraMap k[X] (Localization.Away P) a) = algebraMap k[X] (Localization.Away (P * (X - C c))) a := IsLocalization.Away.awayToAwayRight_eq P (X - C c)`. Establish `hcomp : spMap (algebraMap k[X] (Localization.Away (P * (X - C c)))) = spMap (IsLocalization.Away.awayToAwayRight (S` using `Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫ spMap (algebraMap k[X] (Localization.Away P)) := by`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Conclude with `(RingHom.ext hφ).symm`.

Use `haveI : IsOpenImmersion (spMap (algebraMap k[X] (Localization.Away P))) := IsOpenImmersion.of_isLocalization P`. Use `haveI : IsOpenImmersion (spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫ spMap (algebraMap k[X] (Localization.Away P))) := by`. Rewrite using `[← hcomp]`. Conclude with `IsOpenImmersion.of_isLocalization (P * (X - C c))`. Use `haveI := IsOpenImmersion.of_comp (spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c))) (spMap (algebraMap k[X] (Localization.Away P)))`.

Use `haveI : B.left.IsSeparated := ⟨by`. Rewrite using `[show terminal.from B.left = B.hom ≫ terminal.from (Sp k) from terminal.hom_ext _ _]`. Use the proof step `infer_instance⟩`. Establish `hu' : u ≫ B.hom = spMap (IsLocalization.Away.awayToAwayRight (S` using `Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫ spMap (algebraMap k (Localization.Away P)) := by`. Rewrite using `[hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 2`. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[IsScalarTower.algebraMap_apply k k[X] (Localization.Away P), hφ, ← IsScalarTower.algebraMap_apply]`. Take `⟨g, h1, h2⟩` from `TorusConst.exists_extension (Z := Sp (Localization.Away P)) (fun x => TorusConst.valuationRing_stalk (Localization.Away P) x) _ (spMap (algebraMap k (Localization.Away P))) B.hom u hu'`.

Conclude with `⟨g, h2, h1⟩`.
-/
theorem extend : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by
  intro k _ B _ _ P c hP u hu
  have hQ0 : P * (X - C c) ≠ 0 := mul_ne_zero hP (X_sub_C_ne_zero c)
  haveI : IsDomain (Localization.Away P) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hP)
  haveI : IsDomain (Localization.Away (P * (X - C c))) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hQ0)
  haveI : IsPrincipalIdealRing (Localization.Away P) := isPrincipalIdealRing_away P
  have hφ : ∀ a : k[X], IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c) (algebraMap k[X] (Localization.Away P) a) =
      algebraMap k[X] (Localization.Away (P * (X - C c))) a :=
    IsLocalization.Away.awayToAwayRight_eq P (X - C c)
  have hcomp : spMap (algebraMap k[X] (Localization.Away (P * (X - C c)))) =
      spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  haveI : IsOpenImmersion (spMap (algebraMap k[X] (Localization.Away P))) :=
    IsOpenImmersion.of_isLocalization P
  haveI : IsOpenImmersion (spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P))) := by
    rw [← hcomp]
    exact IsOpenImmersion.of_isLocalization (P * (X - C c))
  haveI := IsOpenImmersion.of_comp (spMap (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c)))
    (spMap (algebraMap k[X] (Localization.Away P)))
  haveI : B.left.IsSeparated := ⟨by
    rw [show terminal.from B.left = B.hom ≫ terminal.from (Sp k) from terminal.hom_ext _ _]
    infer_instance⟩
  have hu' : u ≫ B.hom = spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫ spMap (algebraMap k (Localization.Away P)) := by
    rw [hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply k k[X] (Localization.Away P), hφ,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, h1, h2⟩ := TorusConst.exists_extension (Z := Sp (Localization.Away P))
    (fun x => TorusConst.valuationRing_stalk (Localization.Away P) x) _
    (spMap (algebraMap k (Localization.Away P))) B.hom u hu'
  exact ⟨g, h2, h1⟩

end GlobalTheory.AffineLineExt
