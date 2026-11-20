import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

/- English proof (translation)
Introduce `Y s' M _ W hd hc y`. Set `x0 : (Sp ℂ : Scheme.{0})` to `IsLocalRing.closedPoint ℂ`. Establish `hone : ∀ a : (Sp ℂ : Scheme.{0}), a = x0` using `fun a => Subsingleton.elim a x0`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, y.1 x0 ∈ W m := by`. Establish `h : y.1 x0 ∈ iSup W`.

Rewrite using `[hc]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.mp h`. Establish `hr : Set.range y.1 ⊆ Set.range (W m).ι`. Introduce and unpack `_ ⟨a, rfl⟩`.

Rewrite using `[hone a, Scheme.Opens.range_ι]`. Conclude with `hm`. Use `⟨m, ?_, ?_⟩` and prove the remaining obligations. Use `⟨⟨IsOpenImmersion.lift (W m).ι y.1 hr, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac]`.

Conclude with `y.2`. Conclude with `IsOpenImmersion.lift_fac _ _ _`. Introduce `z hz`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← cancel_mono (W m).ι, hz]`.

Conclude with `(IsOpenImmersion.lift_fac _ _ _).symm`. Introduce and unpack `m' ⟨z, hz, -⟩`. Assume the negation of the conclusion as `hne`. Establish `h1 : y.1 x0 ∈ W m'`. Establish `hz' : z.1 ≫ (W m').ι = y.1` using `hz`.

Rewrite using `[← hz', Scheme.Hom.comp_apply]`. Conclude with `(z.1 x0).2`. Establish `h2 : y.1 x0 ∈ W m' ⊓ W m` using `⟨h1, hm⟩`. Rewrite `h2` using `[hd m' m hne]`. Conclude with `h2`.
-/
theorem UpperTheory.Cb.existsUnique_complexPoint_lift_clopen_cover :
    ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (M : Type) [Fintype M] (W : M → Y.Opens), (∀ i j, i ≠ j → W i ⊓ W j = ⊥) → iSup W = ⊤ → ∀ y : CxPts s' (RingHom.id ℂ), ∃! m : M, ∃! y' : CxPts ((W m).ι ≫ s') (RingHom.id ℂ), y'.1 ≫ (W m).ι = y.1 := by
  intro Y s' M _ W hd hc y
  let x0 : (Sp ℂ : Scheme.{0}) := IsLocalRing.closedPoint ℂ
  have hone : ∀ a : (Sp ℂ : Scheme.{0}), a = x0 := fun a => Subsingleton.elim a x0
  obtain ⟨m, hm⟩ : ∃ m, y.1 x0 ∈ W m := by
    have h : y.1 x0 ∈ iSup W := by
      rw [hc]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h
  have hr : Set.range y.1 ⊆ Set.range (W m).ι := by
    rintro _ ⟨a, rfl⟩
    rw [hone a, Scheme.Opens.range_ι]
    exact hm
  refine ⟨m, ?_, ?_⟩
  · refine ⟨⟨IsOpenImmersion.lift (W m).ι y.1 hr, ?_⟩, ?_, ?_⟩
    · rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact y.2
    · exact IsOpenImmersion.lift_fac _ _ _
    · intro z hz
      apply Subtype.ext
      rw [← cancel_mono (W m).ι, hz]
      exact (IsOpenImmersion.lift_fac _ _ _).symm
  · rintro m' ⟨z, hz, -⟩
    by_contra hne
    have h1 : y.1 x0 ∈ W m' := by
      have hz' : z.1 ≫ (W m').ι = y.1 := hz
      rw [← hz', Scheme.Hom.comp_apply]
      exact (z.1 x0).2
    have h2 : y.1 x0 ∈ W m' ⊓ W m := ⟨h1, hm⟩
    rw [hd m' m hne] at h2
    exact h2
