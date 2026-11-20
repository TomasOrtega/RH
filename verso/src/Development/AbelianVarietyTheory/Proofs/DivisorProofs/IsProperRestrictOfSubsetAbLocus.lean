import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfProperSpecialFibreUniversallyOpenDvrStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyUniformisationTraitInAbelianLocus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusIsOpenOfOpenImmersionCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AbLocusProperNormal

/- English proof (translation)
Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact. Use `hG.geomConnected` as an intermediate fact. Use `GlobalTheory.grpObj_geometricallyIntegral_of_smooth (Sp V) G` as an intermediate fact.

Establish `p : Sp (ResidueField V)` using `IsLocalRing.closedPoint (ResidueField V)`. Use `GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr V G.left G.hom inferInstance inferInstance inferInstance inferInstance inferInstance ?_` and prove the remaining obligations. Conclude with `GlobalTheory.AbelianTrait.isProper_snd_of_mem_abLocus G (K := ResidueField V) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))) p (by rw [hab]; trivial)`.
-/
theorem isProper_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
    [GrpObj G] (hG : IsSemiAbelian G) (hab : abLocus G = Set.univ) : IsProper G.hom := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth (Sp V) G
  have p : Sp (ResidueField V) := IsLocalRing.closedPoint (ResidueField V)
  refine GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr V G.left G.hom inferInstance inferInstance inferInstance inferInstance inferInstance ?_
  exact GlobalTheory.AbelianTrait.isProper_snd_of_mem_abLocus G (K := ResidueField V)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))) p (by rw [hab]; trivial)

/- English proof (translation)
Use `haveI : IsSemiAbelian G := hG`. Use `haveI := hG.separated`. Use `haveI := hG.quasiCompact`. Use `haveI := hG.smooth`. Use `haveI : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G`.

Use `GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint R G.left G.hom ?_` and prove the remaining obligations. Introduce `V K _ _ _ _ _ _ _ x y _ hxy`. Establish `hGV : IsSemiAbelian ((Over.pullback y).obj G)` using `IsSemiAbelian.pullback y G hG`. Establish `habV : abLocus ((Over.pullback y).obj G) = Set.univ` using `Set.eq_univ_of_forall fun z => (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom y) z).1 (hab ▸ Set.mem_univ _)`. Establish `hpV : IsProper (pullback.snd G.hom y)` using `isProper_dvr V _ hGV habV`.

Set `xV : Sp K ⟶ pullback G.hom y` to `pullback.lift x (spMap (algebraMap V K)) hxy`. Establish `hE : ValuativeCriterion.Existence (pullback.snd G.hom y)`. Establish `h : UniversallyClosed (pullback.snd G.hom y)` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`.

Set `S : ValuativeCommSq (pullback.snd G.hom y)` to `{ R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨by rw [Category.comp_id]; exact pullback.lift_snd _ _ _⟩ }`. Take `⟨l⟩` from `(hE S).exists_lift`. Use `⟨l.l ≫ pullback.fst G.hom y, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc]`. Use `l.fac_left` as an intermediate fact.

Express the relevant statement in the definitionally equal form `spMap (algebraMap V K) ≫ l.l = xV at this`. Rewrite using `[this]`. Conclude with `pullback.lift_fst _ _ _`.
-/
theorem isProper_of_abLocus_eq_univ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R))
    [GrpObj G] (hG : IsSemiAbelian G) (hab : abLocus G = Set.univ) : IsProper G.hom := by
  haveI : IsSemiAbelian G := hG
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI := hG.smooth
  haveI : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  refine GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint R G.left G.hom ?_
  intro V K _ _ _ _ _ _ _ x y _ hxy
  have hGV : IsSemiAbelian ((Over.pullback y).obj G) := IsSemiAbelian.pullback y G hG
  have habV : abLocus ((Over.pullback y).obj G) = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom y) z).1 (hab ▸ Set.mem_univ _)
  have hpV : IsProper (pullback.snd G.hom y) := isProper_dvr V _ hGV habV
  let xV : Sp K ⟶ pullback G.hom y := pullback.lift x (spMap (algebraMap V K)) hxy
  have hE : ValuativeCriterion.Existence (pullback.snd G.hom y) := by
    have h : UniversallyClosed (pullback.snd G.hom y) := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq (pullback.snd G.hom y) :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨by rw [Category.comp_id]; exact pullback.lift_snd _ _ _⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  refine ⟨l.l ≫ pullback.fst G.hom y, ?_⟩
  rw [← Category.assoc]
  have := l.fac_left
  change spMap (algebraMap V K) ≫ l.l = xV at this
  rw [this]
  exact pullback.lift_fst _ _ _

/- English proof (translation)
Introduce `R _ _ _ _ G _ hG W hW`. Set `I` to `{r : R // r ≠ 0 ∧ ((PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) : Set (Sp R)) ⊆ (W : Set (Sp R))}`. Set `t : ∀ i : I, Sp (Localization.Away i.1) ⟶ Sp R` to `fun i => spMap (algebraMap R (Localization.Away i.1))`. Establish `hrange : ∀ i : I, Set.range (t i) = (PrimeSpectrum.basicOpen i.1 : Set (PrimeSpectrum R))` using `fun i => PrimeSpectrum.localization_away_comap_range (Localization.Away i.1) i.1`. Establish `hprop : ∀ i : I, IsProper (pullback.snd G.hom (t i) ∣_ ⊤)`.

Introduce `i`. Use `haveI : IsDomain (Localization.Away i.1) := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors i.2.1)`. Use `haveI : IsNoetherianRing (Localization.Away i.1) := IsLocalization.isNoetherianRing (Submonoid.powers i.1) _ inferInstance`. Establish `hGi : IsSemiAbelian ((Over.pullback (t i)).obj G)` using `IsSemiAbelian.pullback (t i) G hG`. Establish `hab : abLocus ((Over.pullback (t i)).obj G) = Set.univ` using `Set.eq_univ_of_forall fun z => (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom (t i)) z).1 (hW (i.2.2 (by rw [← hrange i]; exact ⟨z, rfl⟩)))`.

Establish `: IsProper (pullback.snd G.hom (t i))` using `isProper_of_abLocus_eq_univ _ _ hGi hab`. Use `infer_instance`. Use `GlobalTheory.AbLocusLocal.isProper_restrict_of_cover G.hom t (fun i => pullback.snd G.hom (t i)) (fun i => pullback.fst G.hom (t i)) (fun i => IsPullback.of_hasPullback G.hom (t i)) (fun _ => ⊤) hprop W (fun i => ?_) (fun z hz => ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Use `i.2.2 ?_` and prove the remaining obligations. Rewrite using `[← hrange i]`. Conclude with `⟨_, rfl⟩`. Take `⟨_, ⟨r, rfl⟩, hzr, hrW⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz W.isOpen`. Establish `hr : r ≠ 0` using `fun h0 => hzr (by rw [h0]; exact zero_mem _)`.

Set `i : I` to `⟨r, hr, hrW⟩`. Take `⟨y, hy⟩ : z ∈ Set.range (t i)` from `by rw [hrange i]; exact hzr`. Apply the tactic sequence `exact ⟨i, ⟨y, trivial⟩, by first | exact hy | (erw [Scheme.Hom.comp_apply]; exact hy) | simpa using hy⟩`.
-/
theorem isProper_restrict_of_subset_abLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ W : (Sp R).Opens, (W : Set (Sp R)) ⊆ abLocus G → IsProper (G.hom ∣_ W) := by
  intro R _ _ _ _ G _ hG W hW
  let I := {r : R // r ≠ 0 ∧ ((PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) : Set (Sp R)) ⊆ (W : Set (Sp R))}
  let t : ∀ i : I, Sp (Localization.Away i.1) ⟶ Sp R := fun i => spMap (algebraMap R (Localization.Away i.1))
  have hrange : ∀ i : I, Set.range (t i) = (PrimeSpectrum.basicOpen i.1 : Set (PrimeSpectrum R)) := fun i =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away i.1) i.1
  have hprop : ∀ i : I, IsProper (pullback.snd G.hom (t i) ∣_ ⊤) := by
    intro i
    haveI : IsDomain (Localization.Away i.1) :=
      IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors i.2.1)
    haveI : IsNoetherianRing (Localization.Away i.1) :=
      IsLocalization.isNoetherianRing (Submonoid.powers i.1) _ inferInstance
    have hGi : IsSemiAbelian ((Over.pullback (t i)).obj G) := IsSemiAbelian.pullback (t i) G hG
    have hab : abLocus ((Over.pullback (t i)).obj G) = Set.univ := Set.eq_univ_of_forall fun z =>
      (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom (t i)) z).1
        (hW (i.2.2 (by rw [← hrange i]; exact ⟨z, rfl⟩)))
    have : IsProper (pullback.snd G.hom (t i)) := isProper_of_abLocus_eq_univ _ _ hGi hab
    infer_instance
  refine GlobalTheory.AbLocusLocal.isProper_restrict_of_cover G.hom t (fun i => pullback.snd G.hom (t i))
    (fun i => pullback.fst G.hom (t i)) (fun i => IsPullback.of_hasPullback G.hom (t i)) (fun _ => ⊤) hprop W
    (fun i => ?_) (fun z hz => ?_)
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine i.2.2 ?_
    rw [← hrange i]
    exact ⟨_, rfl⟩
  · obtain ⟨_, ⟨r, rfl⟩, hzr, hrW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz W.isOpen
    have hr : r ≠ 0 := fun h0 => hzr (by rw [h0]; exact zero_mem _)
    let i : I := ⟨r, hr, hrW⟩
    obtain ⟨y, hy⟩ : z ∈ Set.range (t i) := by rw [hrange i]; exact hzr
    exact ⟨i, ⟨y, trivial⟩, by first | exact hy | (erw [Scheme.Hom.comp_apply]; exact hy) | simpa using hy⟩

end GlobalTheory.AbLocusProperNormal
