import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionAndGeometricallyConnect

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SmoothNearFibre

open GlobalTheory.VeryDenseFibres

/- English proof (translation)
Rewrite using `[← pullbackRightPullbackFstIso_inv_snd_snd s t W.ι, MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]`. Conclude with `IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension g) h _`.
-/
private lemma smoothOfRelativeDimension_pullback_snd_restrict {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (W : Z.Opens)
    (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd s t)) :
    SmoothOfRelativeDimension g (pullback.snd (W.ι ≫ s) t) := by
  rw [← pullbackRightPullbackFstIso_inv_snd_snd s t W.ι,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension g) h _

/- English proof (translation)
Rewrite using `[← i.isoOpensRange_inv_comp, Category.assoc, MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]`. Conclude with `h`.
-/
private lemma smoothOfRelativeDimension_opensRange_ι_comp' {U Z S : Scheme.{0}} (i : U ⟶ Z) [IsOpenImmersion i] (s : Z ⟶ S)
    (g : ℕ) (h : SmoothOfRelativeDimension g (i ≫ s)) :
    SmoothOfRelativeDimension g (i.opensRange.ι ≫ s) := by
  rw [← i.isoOpensRange_inv_comp, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
  exact h

/- English proof (translation)
Establish `: Smooth (pullback.snd s t)` using `SmoothOfRelativeDimension.smooth g _`. Establish `hF : Smooth ((pullback.snd s t).fiberToSpecResidueField w)`. Unfold `Scheme.Hom.fiberToSpecResidueField`. Use `infer_instance`. Establish `hF' : Smooth (s.fiberToSpecResidueField (s z))`.

Rewrite using `[hw]`. Conclude with `smooth_fiber_of_smooth_fiber s t w hF`. Establish `hz : z ∈ s.smoothLocus` using `mem_smoothLocus_of_smooth_fiber s z hF'`. Establish `: Smooth (s.smoothLocus.ι ≫ s)`. Rewrite using `[← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]`.

Use extensionality with `a`. Simplify using the standard rewrite rules. Establish `h' : SmoothOfRelativeDimension g (pullback.snd (s.smoothLocus.ι ≫ s) t)` using `smoothOfRelativeDimension_pullback_snd_restrict s t _ g h`. Take `⟨V, hV, hVg⟩` from `exists_opens_smoothOfRelativeDimension (s.smoothLocus.ι ≫ s) t g h' ⟨z, hz⟩ w (by simpa using hw)`. Use `⟨(V.ι ≫ s.smoothLocus.ι).opensRange, ⟨⟨⟨z, hz⟩, hV⟩, by simp⟩, ?_⟩` and prove the remaining obligations.

Apply `smoothOfRelativeDimension_opensRange_ι_comp'` to reduce the goal to its premises. Simplify using `using hVg`.
-/
theorem exists_opens_of_flat {R : CommRingCat.{0}} {Z T : Scheme.{0}} (s : Z ⟶ Spec R)
    [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
  have hF : Smooth ((pullback.snd s t).fiberToSpecResidueField w) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have hF' : Smooth (s.fiberToSpecResidueField (s z)) := by
    rw [hw]
    exact smooth_fiber_of_smooth_fiber s t w hF
  have hz : z ∈ s.smoothLocus := mem_smoothLocus_of_smooth_fiber s z hF'
  have : Smooth (s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext a
    simp
  have h' : SmoothOfRelativeDimension g (pullback.snd (s.smoothLocus.ι ≫ s) t) :=
    smoothOfRelativeDimension_pullback_snd_restrict s t _ g h
  obtain ⟨V, hV, hVg⟩ :=
    exists_opens_smoothOfRelativeDimension (s.smoothLocus.ι ≫ s) t g h' ⟨z, hz⟩ w (by simpa using hw)
  refine ⟨(V.ι ≫ s.smoothLocus.ι).opensRange, ⟨⟨⟨z, hz⟩, hV⟩, by simp⟩, ?_⟩
  apply smoothOfRelativeDimension_opensRange_ι_comp'
  simpa using hVg

/- English proof (translation)
Establish `hb` using `smoothOfRelativeDimension_isStableUnderBaseChange (n := g)`. Establish `key : ∀ p : ↥(pullback s t), ∃ U : (pullback s t).Opens, p ∈ U ∧ SmoothOfRelativeDimension g (U.ι ≫ pullback.snd s t)`. Introduce `p`. Establish `hc : s (pullback.fst s t p) = t (pullback.snd s t p)`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]`.

Take `⟨W, hzW, hW⟩` from `h _ _ hc`. Set `e` to `pullbackRightPullbackFstIso s t W.ι`. Set `j` to `e.inv ≫ pullback.snd W.ι (pullback.fst s t)`. Establish `hj : j ≫ pullback.snd s t = pullback.snd (W.ι ≫ s) t`. Simplify using `[j, e]`.

Use `⟨j.opensRange, ?_, ?_⟩` and prove the remaining obligations. Take `⟨q, -, hq2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := W.ι) (g := pullback.fst s t) ⟨_, hzW⟩ p (by simp)`. Use `⟨e.hom q, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply]`. Simplify `hq2` using `[j]`.

Rewrite using `[← j.isoOpensRange_inv_comp, Category.assoc, hj, MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]`. Conclude with `MorphismProperty.pullback_snd _ _ hW`. Use `choose U hU hP using key`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) U ?_ hP` and prove the remaining obligations. Rewrite using `[eq_top_iff]`.

Introduce `p _`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hU p⟩`.
-/
theorem smoothOfRelativeDimension_pullback_snd {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (g : ℕ)
    (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  have hb := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
  have key : ∀ p : ↥(pullback s t), ∃ U : (pullback s t).Opens,
      p ∈ U ∧ SmoothOfRelativeDimension g (U.ι ≫ pullback.snd s t) := by
    intro p
    have hc : s (pullback.fst s t p) = t (pullback.snd s t p) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    obtain ⟨W, hzW, hW⟩ := h _ _ hc
    let e := pullbackRightPullbackFstIso s t W.ι
    let j := e.inv ≫ pullback.snd W.ι (pullback.fst s t)
    have hj : j ≫ pullback.snd s t = pullback.snd (W.ι ≫ s) t := by
      simp [j, e]
    refine ⟨j.opensRange, ?_, ?_⟩
    · obtain ⟨q, -, hq2⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := W.ι) (g := pullback.fst s t) ⟨_, hzW⟩ p (by simp)
      refine ⟨e.hom q, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      simpa [j] using hq2
    · rw [← j.isoOpensRange_inv_comp, Category.assoc, hj,
        MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
      exact MorphismProperty.pullback_snd _ _ hW
  choose U hU hP using key
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) U ?_ hP
  rw [eq_top_iff]
  intro p _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hU p⟩

/- English proof (translation)
Introduce `R _ _ Z s g K _ x hprop hflat hsm`. Establish `: LocallyOfFinitePresentation s` using `inferInstance`. Set `U : Z.Opens` to `sSup {W : Z.Opens | SmoothOfRelativeDimension g (W.ι ≫ s)}`. Establish `hpt : ∀ w : Sp K, ∀ z : Z, (s z).asIdeal = RingHom.ker x → z ∈ U`. Introduce `w z hz`.

Establish `hzw : s z = spMap x w` using `PrimeSpectrum.ext (by rw [hz, spMap_apply_asIdeal])`. Take `⟨W, hzW, hW⟩` from `exists_opens_of_flat (R := CommRingCat.of R) s (spMap x) g hsm z w hzw`. Conclude with `TopologicalSpace.Opens.mem_sSup.mpr ⟨W, hW, hzW⟩`. Set `w₀ : Sp K` to `IsLocalRing.closedPoint K`. Set `C : Set (Sp R)` to `s '' (U : Set Z)ᶜ`.

Establish `hC : IsClosed C` using `s.isClosedMap _ U.isOpen.isClosed_compl`. Establish `hp : spMap x w₀ ∈ Cᶜ`. Introduce and unpack `⟨z, hzU, hzp⟩`. Apply `hzU` to reduce the goal to its premises. Apply `hpt w₀ z` to reduce the goal to its premises.

Rewrite using `[hzp, spMap_apply_asIdeal]`. Take `⟨_, ⟨f, rfl⟩, hpf, hfC⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hC.isOpen_compl`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Introduce `hf0`. Apply `hpf` to reduce the goal to its premises.

Use `show f ∈ (spMap x w₀).asIdeal`. Rewrite using `[spMap_apply_asIdeal]`. Conclude with `hf0`. Introduce `R' _ φ hφ`. Apply `smoothOfRelativeDimension_pullback_snd` to reduce the goal to its premises.

Introduce `z w hzw`. Establish `hzU : z ∈ U`. Assume the negation of the conclusion as `hzU`. Establish `hmem : s z ∈ C` using `⟨z, hzU, rfl⟩`. Apply `hfC (PrimeSpectrum.mem_basicOpen _ _ |>.mpr ?_) hmem` to reduce the goal to its premises.

Rewrite using `[hzw]`. Use `show f ∉ (PrimeSpectrum.comap (CommRingCat.ofHom φ).hom w).asIdeal`. Introduce `hfw`. Conclude with `w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hfw hφ)`. Take `⟨W, hW, hzW⟩` from `TopologicalSpace.Opens.mem_sSup.mp hzU`.

Conclude with `⟨W, hzW, hW⟩`.
-/
theorem exists_smoothOfRelativeDimension_of_isUnit :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → SmoothOfRelativeDimension g (pullback.snd s (spMap φ)) := by
  intro R _ _ Z s g K _ x hprop hflat hsm
  have : LocallyOfFinitePresentation s := inferInstance
  let U : Z.Opens := sSup {W : Z.Opens | SmoothOfRelativeDimension g (W.ι ≫ s)}
  have hpt : ∀ w : Sp K, ∀ z : Z, (s z).asIdeal = RingHom.ker x → z ∈ U := by
    intro w z hz
    have hzw : s z = spMap x w := PrimeSpectrum.ext (by rw [hz, spMap_apply_asIdeal])
    obtain ⟨W, hzW, hW⟩ :=
      exists_opens_of_flat (R := CommRingCat.of R) s (spMap x) g hsm z w hzw
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨W, hW, hzW⟩
  let w₀ : Sp K := IsLocalRing.closedPoint K
  let C : Set (Sp R) := s '' (U : Set Z)ᶜ
  have hC : IsClosed C := s.isClosedMap _ U.isOpen.isClosed_compl
  have hp : spMap x w₀ ∈ Cᶜ := by
    rintro ⟨z, hzU, hzp⟩
    apply hzU
    apply hpt w₀ z
    rw [hzp, spMap_apply_asIdeal]
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfC⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hC.isOpen_compl
  refine ⟨f, ?_, ?_⟩
  · intro hf0
    apply hpf
    show f ∈ (spMap x w₀).asIdeal
    rw [spMap_apply_asIdeal]
    exact hf0
  · intro R' _ φ hφ
    apply smoothOfRelativeDimension_pullback_snd
    intro z w hzw
    have hzU : z ∈ U := by
      by_contra hzU
      have hmem : s z ∈ C := ⟨z, hzU, rfl⟩
      apply hfC (PrimeSpectrum.mem_basicOpen _ _ |>.mpr ?_) hmem
      rw [hzw]
      show f ∉ (PrimeSpectrum.comap (CommRingCat.ofHom φ).hom w).asIdeal
      intro hfw
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hfw hφ)
    obtain ⟨W, hW, hzW⟩ := TopologicalSpace.Opens.mem_sSup.mp hzU
    exact ⟨W, hzW, hW⟩

end GlobalTheory.SmoothNearFibre
