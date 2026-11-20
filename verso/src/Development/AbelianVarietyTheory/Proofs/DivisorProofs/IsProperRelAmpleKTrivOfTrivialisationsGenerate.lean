import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianProperUniformisedWhereTrivialisationsGene
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTripleAbelianLocusProperRelAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.Principal

/- English proof (translation)
Use `⟨inferInstance, ?_, fun T _ s x _ => ?_⟩` and prove the remaining obligations. Use `t.semi.quasiCompact` as an intermediate fact. Use `t.semi.separated` as an intermediate fact. Conclude with `GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance fun q => isEmptyElim q`. Establish `: IsEmpty (Over.mk s).left` using `⟨fun p => isEmptyElim (s p)⟩`.

Conclude with `Over.OverMorphism.ext ((isInitialOfIsEmpty (X := (Over.mk s).left)).hom_ext _ _)`.
-/
theorem of_isEmpty {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Type} [CommRing S]
    [IsEmpty (Sp S)] (t : SAB H (Sp S)) :
    IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  refine ⟨inferInstance, ?_, fun T _ s x _ => ?_⟩
  · have := t.semi.quasiCompact
    have := t.semi.separated
    exact GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance
      fun q => isEmptyElim q
  · have : IsEmpty (Over.mk s).left := ⟨fun p => isEmptyElim (s p)⟩
    exact Over.OverMorphism.ext ((isInitialOfIsEmpty (X := (Over.mk s).left)).hom_ext _ _)

/- English proof (translation)
Introduce `E _ _ _ H R _ _ _ hR t P f hψ tf mf`. Set `Rf` to `Localization.Away f`. Establish `hrange : Set.range (spMap (algebraMap R Rf)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))` using `PrimeSpectrum.localization_away_comap_range Rf f`. Distinguish the cases in `hf : f = 0`. Establish `: IsEmpty (Sp Rf)` using `⟨fun z => by`.

Establish `hz : f ∉ (spMap (algebraMap R Rf) z).asIdeal` using `hrange.le ⟨z, rfl⟩`. Conclude with `hz ((congrArg (· ∈ (spMap (algebraMap R Rf) z).asIdeal) hf).mpr (Ideal.zero_mem _))⟩`. Conclude with `of_isEmpty tf`. Take `⟨hab, -⟩` from `GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn R hR P.D P.A t.G t.semi P.U (PrimeSpectrum.basicOpen f) hψ`. Establish `: IsNoetherianRing R` using `hR.1.1`.

Establish `: CharZero R` using `hR.2`. Establish `hle` using `powers_le_nonZeroDivisors_of_noZeroDivisors hf`. Establish `hi : Function.Injective (algebraMap R Rf)` using `IsLocalization.injective Rf hle`. Establish `: IsDomain Rf` using `IsLocalization.isDomain_localization hle`. Establish `: CharZero Rf` using `charZero_of_injective_algebraMap hi`.

Establish `habf : abLocus tf.G = Set.univ` using `Set.eq_univ_of_forall fun z => (abLocus_pullback abLocusOne t.semi mf.cart.1 z).1 (hab (hrange.le ⟨z, rfl⟩))`. Establish `hg : GlobalTheory.LN.PolAt tf (Out.jK Rf)` using `GlobalTheory.PolNormal.polAt_generic_pull _ hi mf (GlobalTheory.DatUniq.polAt_of_unif P)`. Establish `hpf : IsProper tf.G.hom` using `GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H Rf tf hg habf`. Conclude with `⟨hpf, GlobalTheory.AbLocusPol.relAmple_kTriv_of_generic tf hpf hg⟩`.
-/
theorem isProper_relAmple_kTriv_of_psiUnitOn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (f : R), (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∀ tO : SAB H (Sp (Localization.Away f)), SABMap tO t (spMap (algebraMap R (Localization.Away f))) → IsProper tO.G.hom ∧ Out.RelAmple tO.G tO.PP.L ∧ Out.KTriv tO.G tO.PP.L := by
  intro E _ _ _ H R _ _ _ hR t P f hψ tf mf
  let Rf := Localization.Away f
  have hrange : Set.range (spMap (algebraMap R Rf)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range Rf f
  by_cases hf : f = 0
  · have : IsEmpty (Sp Rf) := ⟨fun z => by
      have hz : f ∉ (spMap (algebraMap R Rf) z).asIdeal := hrange.le ⟨z, rfl⟩
      exact hz ((congrArg (· ∈ (spMap (algebraMap R Rf) z).asIdeal) hf).mpr (Ideal.zero_mem _))⟩
    exact of_isEmpty tf
  obtain ⟨hab, -⟩ := GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn R hR P.D P.A t.G t.semi P.U
    (PrimeSpectrum.basicOpen f) hψ
  have : IsNoetherianRing R := hR.1.1
  have : CharZero R := hR.2
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hi : Function.Injective (algebraMap R Rf) := IsLocalization.injective Rf hle
  have : IsDomain Rf := IsLocalization.isDomain_localization hle
  have : CharZero Rf := charZero_of_injective_algebraMap hi
  have habf : abLocus tf.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi mf.cart.1 z).1 (hab (hrange.le ⟨z, rfl⟩))
  have hg : GlobalTheory.LN.PolAt tf (Out.jK Rf) := GlobalTheory.PolNormal.polAt_generic_pull _ hi mf (GlobalTheory.DatUniq.polAt_of_unif P)
  have hpf : IsProper tf.G.hom := GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H Rf tf hg habf
  exact ⟨hpf, GlobalTheory.AbLocusPol.relAmple_kTriv_of_generic tf hpf hg⟩

end GlobalTheory.UCanon.Principal
