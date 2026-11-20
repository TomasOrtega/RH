import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
/- English proof (translation)
Rewrite using `[← PrimeSpectrum.le_iff_specializes]`. Introduce `a ha`. Establish `h0 : x.asIdeal = ⊥` using `Ideal.eq_bot_of_prime _`. Rewrite `ha` using `[PrimeSpectrum.comap_asIdeal, h0, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O F)]`. Rewrite using `[Ideal.mem_bot.mp ha]`.

Conclude with `zero_mem _`.
-/
private lemma comap_algebraMap_fractionRing_specializes (O F : Type) [CommRing O] [IsDomain O] [Field F]
    [Algebra O F] [IsFractionRing O F] (x : PrimeSpectrum F) (y : PrimeSpectrum O) :
    PrimeSpectrum.comap (algebraMap O F) x ⤳ y := by
  rw [← PrimeSpectrum.le_iff_specializes]
  intro a ha
  have h0 : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [PrimeSpectrum.comap_asIdeal, h0, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O F)] at ha
  rw [Ideal.mem_bot.mp ha]
  exact zero_mem _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

/- English proof (translation)
Introduce `O F _ _ _ _ _ X U s jQ hflat hproj hopen hdense`. Take `⟨N, i, hi, hsi⟩` from `hproj`. Use `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N` as an intermediate fact. Establish `hprop : IsProper s` using `by rw [← hsi]; infer_instance`. Establish `hnO : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)` using `by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance`.

Establish `hnF : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F)` using `by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance`. Establish `hcF : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F)` using `by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance`. Establish `hcO : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)` using `by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance`. Establish `hsepO : IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O).toSpecΓ` using `by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance`. Establish `hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))`.

Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap`. Conclude with `IsPreimmersion.of_isLocalization (nonZeroDivisors O)`. Establish `hflg : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]`.

Conclude with `IsLocalization.flat F (nonZeroDivisors O)`. Establish `hnP : IsLocallyNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))`. Establish `hcP : CompactSpace ↥(pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))`. Establish `: IsNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))` using `⟨⟩`. Establish `: TopologicalSpace.NoetherianSpace U` using `jQ.isOpenEmbedding.isInducing.noetherianSpace`.

Establish `hdomj : IsDominant jQ` using `⟨hdense⟩`. Establish `hdomf : IsDominant (pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))`. Prove the components needed by the constructor for the conclusion. Introduce `x`. Take `⟨p⟩ : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F)` from `by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance`.

Establish `hp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F) p ⤳ s x` using `comap_algebraMap_fractionRing_specializes O F p (s x)`. Take `⟨x', hx', hsx'⟩` from `Flat.generalizingMap s hp`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) x' p hsx'`. Conclude with `closure_mono (show {x'} ⊆ Set.range _ from Set.singleton_subset_iff.mpr ⟨z, hz⟩) (specializes_iff_mem_closure.mp hx')`. Use `⟨LocallyOfFiniteType.isLocallyNoetherian s, QuasiCompact.compactSpace_of_compactSpace s, ?_, inferInstance, inferInstance, inferInstance, inferInstance⟩` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Rewrite using `[← terminal.comp_from s]`. Use `infer_instance`.
-/
theorem _root_.GlobalTheory.genericPart_dense_proOpen : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F] (X U : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (jQ : U ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))), Flat s → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s → IsOpenImmersion jQ → Dense (Set.range jQ) → IsLocallyNoetherian X ∧ CompactSpace X ∧ X.IsSeparated ∧ IsPreimmersion (jQ ≫ pullback.fst _ _) ∧ Flat (jQ ≫ pullback.fst _ _) ∧ IsDominant (jQ ≫ pullback.fst _ _) ∧ QuasiCompact (jQ ≫ pullback.fst _ _) := by
  intro O F _ _ _ _ _ X U s jQ hflat hproj hopen hdense
  obtain ⟨N, i, hi, hsi⟩ := hproj
  have := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
  have hprop : IsProper s := by rw [← hsi]; infer_instance
  have hnO : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hnF : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hcF : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hcO : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hsepO : IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O).toSpecΓ := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have hflg : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat F (nonZeroDivisors O)
  have hnP : IsLocallyNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))
  have hcP : CompactSpace ↥(pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))
  have : IsNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := jQ.isOpenEmbedding.isInducing.noetherianSpace
  have hdomj : IsDominant jQ := ⟨hdense⟩
  have hdomf : IsDominant (pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) := by
    constructor
    intro x
    obtain ⟨p⟩ : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
    have hp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F) p ⤳ s x := comap_algebraMap_fractionRing_specializes O F p (s x)
    obtain ⟨x', hx', hsx'⟩ := Flat.generalizingMap s hp
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) x' p hsx'
    exact closure_mono (show {x'} ⊆ Set.range _ from Set.singleton_subset_iff.mpr ⟨z, hz⟩)
      (specializes_iff_mem_closure.mp hx')
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian s, QuasiCompact.compactSpace_of_compactSpace s,
    ?_, inferInstance, inferInstance, inferInstance, inferInstance⟩
  constructor
  rw [← terminal.comp_from s]
  infer_instance

end GlobalTheory
