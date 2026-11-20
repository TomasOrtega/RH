import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionAndGeometricallyConnect
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ProperFlatNearFibre

/- English proof (translation)
Establish `hz : z ∈ s.smoothLocus`. Use `GlobalTheory.VeryDenseFibres.mem_smoothLocus_of_smooth_fiber s z ?_` and prove the remaining obligations. Rewrite using `[hw]`. Establish `: Smooth (pullback.snd s t)` using `SmoothOfRelativeDimension.smooth g _`. Conclude with `GlobalTheory.VeryDenseFibres.smooth_fiber_of_smooth_fiber s t w (inferInstanceAs (Smooth (pullback.snd (pullback.snd s t) (T.fromSpecResidueField w))))`.

Establish `: Smooth (s.smoothLocus.ι ≫ s)`. Rewrite using `[← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]`. Simplify using the standard rewrite rules. Establish `h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (s.smoothLocus.ι ≫ s) t)`. Rewrite using `[← pullbackRightPullbackFstIso_inv_snd_snd]`.

Use `infer_instance`. Take `⟨W, hW, hW'⟩` from `GlobalTheory.VeryDenseFibres.exists_opens_smoothOfRelativeDimension (s.smoothLocus.ι ≫ s) t g (by simpa using h2) ⟨z, hz⟩ w hw`. Set `j` to `W.ι ≫ s.smoothLocus.ι`. Use `⟨j.opensRange, ⟨⟨⟨z, hz⟩, hW⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e : j.opensRange.ι ≫ s = j.isoOpensRange.inv ≫ (W.ι ≫ s.smoothLocus.ι ≫ s)`.

Rewrite using `[← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]`. Establish `h3 : SmoothOfRelativeDimension (0 + g) (j.isoOpensRange.inv ≫ (W.ι ≫ s.smoothLocus.ι ≫ s))` using `inferInstance`. Rewrite using `[e]`. Simplify using `using h3`.
-/
theorem exists_opens_smoothOfRelativeDimension_of_flat {R : CommRingCat.{0}} {Z T : Scheme.{0}}
    (s : Z ⟶ Spec R) [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  have hz : z ∈ s.smoothLocus := by
    refine GlobalTheory.VeryDenseFibres.mem_smoothLocus_of_smooth_fiber s z ?_
    rw [hw]
    have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
    exact GlobalTheory.VeryDenseFibres.smooth_fiber_of_smooth_fiber s t w
      (inferInstanceAs (Smooth (pullback.snd (pullback.snd s t) (T.fromSpecResidueField w))))
  have : Smooth (s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (s.smoothLocus.ι ≫ s) t) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨W, hW, hW'⟩ := GlobalTheory.VeryDenseFibres.exists_opens_smoothOfRelativeDimension
    (s.smoothLocus.ι ≫ s) t g (by simpa using h2) ⟨z, hz⟩ w hw
  let j := W.ι ≫ s.smoothLocus.ι
  refine ⟨j.opensRange, ⟨⟨⟨z, hz⟩, hW⟩, rfl⟩, ?_⟩
  have e : j.opensRange.ι ≫ s = j.isoOpensRange.inv ≫ (W.ι ≫ s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]
  have h3 : SmoothOfRelativeDimension (0 + g)
      (j.isoOpensRange.inv ≫ (W.ι ≫ s.smoothLocus.ι ≫ s)) := inferInstance
  rw [e]
  simpa using h3

/- English proof (translation)
Set `V : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)} → (pullback s t).Opens` to `fun W => pullback.fst s t ⁻¹ᵁ W.1`. Establish `htop : iSup V = ⊤`. Rewrite using `[← top_le_iff]`. Introduce `y _`. Take `⟨W, hW, hW'⟩` from `h (pullback.fst s t y) (pullback.snd s t y) (by`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩`. Establish `: IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g)` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `smoothOfRelativeDimension_isStableUnderBaseChange.{0} g` as an intermediate fact. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) V htop fun W => ?_` and prove the remaining obligations.

Conclude with `MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{0} g) ((isPullback_morphismRestrict (pullback.fst s t) W.1).paste_vert (IsPullback.of_hasPullback s t)) W.2`.
-/
theorem smoothOfRelativeDimension_pullback_snd {Z T S : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S)
    (g : ℕ) (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  let V : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)} → (pullback s t).Opens :=
    fun W => pullback.fst s t ⁻¹ᵁ W.1
  have htop : iSup V = ⊤ := by
    rw [← top_le_iff]
    intro y _
    obtain ⟨W, hW, hW'⟩ := h (pullback.fst s t y) (pullback.snd s t y) (by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) V htop
    fun W => ?_
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{0} g)
    ((isPullback_morphismRestrict (pullback.fst s t) W.1).paste_vert
      (IsPullback.of_hasPullback s t)) W.2

/- English proof (translation)
Introduce `R _ _ Z s g K _ x hs hf h`. Establish `: LocallyOfFinitePresentation s` using `inferInstance`. Set `U : Z.Opens` to `⨆ W : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)}, W.1`. Establish `hc : IsClosed (s '' (U : Set Z)ᶜ)` using `s.isClosedMap _ U.2.isClosed_compl`. Set `w : Sp K` to `(default : PrimeSpectrum K)`.

Establish `hp : spMap x w ∈ (s '' (U : Set Z)ᶜ)ᶜ`. Introduce and unpack `⟨z, hz, e⟩`. Take `⟨W, hW, hW'⟩` from `exists_opens_smoothOfRelativeDimension_of_flat s (spMap x) g h z w e`. Conclude with `hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩)`. Take `⟨_, ⟨f, rfl⟩, hf1, hf2⟩` from `(PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp hc.isOpen_compl`.

Use `⟨f, ?_, smoothOfRelativeDimension_pullback_snd _ _ g fun z y e => ?_⟩` and prove the remaining obligations. Establish `h1 : f ∉ (spMap x w).asIdeal` using `hf1`. Rewrite `h1` using `[GlobalTheory.VeryDenseFibres.spMap_apply_asIdeal, RingHom.mem_ker]`. Then use the resulting hypothesis. Establish `h1 : s z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))`. Rewrite using `[← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]`.

Conclude with `⟨y, e.symm⟩`. Establish `h2 : z ∈ U`. Assume the negation of the conclusion as `hz`. Conclude with `hf2 h1 ⟨z, hz, rfl⟩`. Take `⟨W, hW⟩` from `TopologicalSpace.Opens.mem_iSup.1 h2`.

Conclude with `⟨W.1, hW, W.2⟩`.
-/
theorem exists_away_smoothOfRelativeDimension :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s g K _ x hs hf h
  have : LocallyOfFinitePresentation s := inferInstance
  let U : Z.Opens := ⨆ W : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)}, W.1
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  let w : Sp K := (default : PrimeSpectrum K)
  have hp : spMap x w ∈ (s '' (U : Set Z)ᶜ)ᶜ := by
    rintro ⟨z, hz, e⟩
    obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension_of_flat s (spMap x) g h z w e
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩)
  obtain ⟨_, ⟨f, rfl⟩, hf1, hf2⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp
      hc.isOpen_compl
  refine ⟨f, ?_, smoothOfRelativeDimension_pullback_snd _ _ g fun z y e => ?_⟩
  · have h1 : f ∉ (spMap x w).asIdeal := hf1
    rwa [GlobalTheory.VeryDenseFibres.spMap_apply_asIdeal, RingHom.mem_ker] at h1
  · have h1 : s z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨y, e.symm⟩
    have h2 : z ∈ U := by
      by_contra hz
      exact hf2 h1 ⟨z, hz, rfl⟩
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact ⟨W.1, hW, W.2⟩

end GlobalTheory.ProperFlatNearFibre
