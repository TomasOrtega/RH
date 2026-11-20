import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

/- English proof (translation)
Introduce `Z Z' _ _ π hπ _ V hV`. Use `haveI : IsFinite π := hπ`. Establish `hCc : IsClosed ((V : Set Z')ᶜ)` using `V.isOpen.isClosed_compl`. Use `⟨⟨(π '' (V : Set Z')ᶜ)ᶜ, (π.isClosedMap _ hCc).isOpen_compl⟩, ⟨genericPoint Z, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show genericPoint Z ∉ π '' (V : Set Z')ᶜ`.

Introduce and unpack `⟨x, hxC, hx⟩`. Establish `h1 : genericPoint Z' ⤳ x` using `(genericPoint_spec Z').specializes (Set.mem_univ x)`. Establish `h2 : π (genericPoint Z') = genericPoint Z`. Establish `a : π (genericPoint Z') ⤳ π x` using `h1.map π.continuous`. Rewrite `a` using `[hx]`.

Conclude with `(a.antisymm ((genericPoint_spec Z).specializes (Set.mem_univ _))).eq`. Use `haveI hd := (π.isDiscrete_preimage_singleton (genericPoint Z)).to_subtype`. Establish `m2 : genericPoint Z' ∈ (π ⁻¹' {genericPoint Z} : Set Z')` using `h2`. Establish `mx : x ∈ (π ⁻¹' {genericPoint Z} : Set Z')` using `hx`. Establish `h3 : (⟨genericPoint Z', m2⟩ : (π ⁻¹' {genericPoint Z} : Set Z')) ⤳ ⟨x, mx⟩` using `Topology.IsInducing.subtypeVal.specializes_iff.mp h1`.

Establish `h4 : genericPoint Z' = x` using `congrArg Subtype.val (specializes_iff_eq.mp h3)`. Apply `hxC` to reduce the goal to its premises. Rewrite using `[← h4]`. Conclude with `((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr (by simpa using hV)`. Introduce `x hx`.

Assume the negation of the conclusion as `h`. Conclude with `hx ⟨x, h, rfl⟩`.
-/
theorem PositivityTheory.Xgn.finite_surjective_image_open : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V := by
  intro Z Z' _ _ π hπ _ V hV
  haveI : IsFinite π := hπ
  have hCc : IsClosed ((V : Set Z')ᶜ) := V.isOpen.isClosed_compl
  refine ⟨⟨(π '' (V : Set Z')ᶜ)ᶜ, (π.isClosedMap _ hCc).isOpen_compl⟩, ⟨genericPoint Z, ?_⟩, ?_⟩
  · show genericPoint Z ∉ π '' (V : Set Z')ᶜ
    rintro ⟨x, hxC, hx⟩
    have h1 : genericPoint Z' ⤳ x := (genericPoint_spec Z').specializes (Set.mem_univ x)
    have h2 : π (genericPoint Z') = genericPoint Z := by
      have a : π (genericPoint Z') ⤳ π x := h1.map π.continuous
      rw [hx] at a
      exact (a.antisymm ((genericPoint_spec Z).specializes (Set.mem_univ _))).eq
    haveI hd := (π.isDiscrete_preimage_singleton (genericPoint Z)).to_subtype
    have m2 : genericPoint Z' ∈ (π ⁻¹' {genericPoint Z} : Set Z') := h2
    have mx : x ∈ (π ⁻¹' {genericPoint Z} : Set Z') := hx
    have h3 : (⟨genericPoint Z', m2⟩ : (π ⁻¹' {genericPoint Z} : Set Z')) ⤳ ⟨x, mx⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp h1
    have h4 : genericPoint Z' = x := congrArg Subtype.val (specializes_iff_eq.mp h3)
    apply hxC
    rw [← h4]
    exact ((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩
