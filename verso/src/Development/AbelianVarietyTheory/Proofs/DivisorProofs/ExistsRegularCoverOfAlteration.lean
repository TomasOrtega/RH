import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RegCoverExists

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
/- English proof (translation)
Establish `: IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)` using `by show IsAffine (Spec (CommRingCat.of R)); infer_instance`. Establish `: IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R')` using `by show IsAffine (Spec (CommRingCat.of R')); infer_instance`. Use `infer_instance`.
-/
private theorem isSeparated_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c) := by
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
    show IsAffine (Spec (CommRingCat.of R)); infer_instance
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') := by
    show IsAffine (Spec (CommRingCat.of R')); infer_instance
  infer_instance

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in

/- English proof (translation)
Take `⟨N, i, hi, hif⟩` from `h`. Establish `hP` using `_root_.GlobalTheory.ProjSpace.isPullback_baseChange N c`. Use `haveI := isSeparated_spMap c`. Use `haveI : IsSeparated (_root_.GlobalTheory.ProjSpace.baseChange N c) := MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance`. Use `⟨N, hP.lift i f hif, ?_, hP.lift_snd _ _ _⟩` and prove the remaining obligations.

Use `haveI : IsClosedImmersion (hP.lift i f hif ≫ _root_.GlobalTheory.ProjSpace.baseChange N c) := by`. Rewrite using `[hP.lift_fst]`. Conclude with `hi`. Conclude with `IsClosedImmersion.of_comp _ (_root_.GlobalTheory.ProjSpace.baseChange N c)`.
-/
theorem _root_.GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    {Y : Scheme.{0}} {f : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (f ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f := by
  obtain ⟨N, i, hi, hif⟩ := h
  have hP := _root_.GlobalTheory.ProjSpace.isPullback_baseChange N c
  haveI := isSeparated_spMap c
  haveI : IsSeparated (_root_.GlobalTheory.ProjSpace.baseChange N c) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  refine ⟨N, hP.lift i f hif, ?_, hP.lift_snd _ _ _⟩
  haveI : IsClosedImmersion (hP.lift i f hif ≫ _root_.GlobalTheory.ProjSpace.baseChange N c) := by
    rw [hP.lift_fst]; exact hi
  exact IsClosedImmersion.of_comp _ (_root_.GlobalTheory.ProjSpace.baseChange N c)

/- English proof (translation)
Assemble the required witnesses or components as `⟨hd, hf, h.isIntegral, isProjOver_of_comp_spMap (Int.castRingHom k) (specZIsTerminal.hom_ext s (f ≫ spMap (Int.castRingHom k)) ▸ h.isProjOver), specZIsTerminal.hom_ext (s ≫ spMap (Int.castRingHom ℤ)) (f ≫ spMap (Int.castRingHom k)) ▸ h.flat, h.dim_eq⟩`.
-/
theorem isArithVar_of_toSpZ {k : Type} [CommRing k] (hd : IsDomain k) (hf : Module.Finite ℤ k) {Y : Scheme.{0}}
    (f : Y ⟶ Sp k) {s : Y ⟶ Sp ℤ} {D : ℕ} (h : IsArithVar s D) : IsArithVar f D :=
  ⟨hd, hf, h.isIntegral,
    isProjOver_of_comp_spMap (Int.castRingHom k)
      (specZIsTerminal.hom_ext s (f ≫ spMap (Int.castRingHom k)) ▸ h.isProjOver),
    specZIsTerminal.hom_ext (s ≫ spMap (Int.castRingHom ℤ)) (f ≫ spMap (Int.castRingHom k)) ▸ h.flat, h.dim_eq⟩

/- English proof (translation)
Introduce `H k _ Y q _ h`. Take `⟨Z, _, ρ, hZ, hr, hg, hd⟩` from `H Y _ 1 (ShFam.Pad.isArithVar_toSpZ h)`. Conclude with `⟨⟨Z, ρ, ⟨isArithVar_of_toSpZ h.isDomain h.finite _ hZ, hr⟩, hg, hd⟩⟩`.
-/
theorem nonempty_regCover : Published.RegularAlteration → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k)
    [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q) := by
  intro H k _ Y q _ h
  obtain ⟨Z, _, ρ, hZ, hr, hg, hd⟩ := H Y _ 1 (ShFam.Pad.isArithVar_toSpZ h)
  exact ⟨⟨Z, ρ, ⟨isArithVar_of_toSpZ h.isDomain h.finite _ hZ, hr⟩, hg, hd⟩⟩

end GlobalTheory.RegCoverExists

end
