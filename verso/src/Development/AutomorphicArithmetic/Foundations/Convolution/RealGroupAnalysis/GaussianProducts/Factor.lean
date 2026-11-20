import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

/- English proof (translation)
Introduce `X Y _ _ _ _ _ _ r H hr hH hf`. Establish `key : ∀ F : Set X, IsClosed F → MeasurableSet (r '' F)`. Introduce `F hF`. Establish `e : r '' F = ⋃ n, r '' (F ∩ compactCovering X n)`. Rewrite using `[← Set.image_iUnion, ← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]`.

Rewrite using `[e]`. Use `MeasurableSet.iUnion fun n => ?_` and prove the remaining obligations. Conclude with `(((isCompact_compactCovering X n).inter_left hF).image hr).isClosed.measurableSet`. Establish `hrange : MeasurableSet (Set.range r)`. Rewrite using `[← Set.image_univ]`.

Conclude with `key _ isClosed_univ`. Set `h : Y → ℂ` to `fun y => if hy : ∃ x, r x = y then H hy.choose else 0`. Establish `hh : ∀ x, h (r x) = H x`. Introduce `x`. Establish `hy : ∃ x', r x' = r x` using `⟨x, rfl⟩`.

Simplify using `only [h, dif_pos hy]`. Conclude with `hf _ _ hy.choose_spec`. Use `⟨h, measurable_of_isClosed fun C hC => ?_, hh⟩` and prove the remaining obligations. Establish `himg : MeasurableSet (r '' (H ⁻¹' C))` using `key _ (hC.preimage hH)`. Establish `hout : ∀ y, y ∉ Set.range r → h y = 0`.

Introduce `y hy`. Establish `hy' : ¬ ∃ x, r x = y` using `hy`. Simplify using `only [h, dif_neg hy']`. Distinguish the cases in `h0 : (0 : ℂ) ∈ C`. Establish `e : h ⁻¹' C = r '' (H ⁻¹' C) ∪ (Set.range r)ᶜ`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Distinguish the cases in `hyr : y ∈ Set.range r`. Take `⟨x, rfl⟩` from `hyr`.

Use `Or.inl ⟨x, ?_, rfl⟩` and prove the remaining obligations. Establish `: h (r x) ∈ C` using `hy`. Rewrite `this` using `[hh]`. Conclude with `this`. Conclude with `Or.inr hyr`.

Introduce and unpack `(⟨x, hx, rfl⟩ | hy)`. Use `show h (r x) ∈ C`. Rewrite using `[hh]`. Conclude with `hx`. Use `show h y ∈ C`.

Rewrite using `[hout y hy]`. Conclude with `h0`. Rewrite using `[e]`. Conclude with `himg.union hrange.compl`. Establish `e : h ⁻¹' C = r '' (H ⁻¹' C)`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Distinguish the cases in `hyr : y ∈ Set.range r`. Take `⟨x, rfl⟩` from `hyr`.

Use `⟨x, ?_, rfl⟩` and prove the remaining obligations. Establish `: h (r x) ∈ C` using `hy`. Rewrite `this` using `[hh]`. Conclude with `this`. Establish `: h y ∈ C` using `hy`.

Rewrite `this` using `[hout y hyr]`. Conclude with `absurd this h0`. Introduce and unpack `⟨x, hx, rfl⟩ show h (r x) ∈ C`. Rewrite using `[hh]`. Conclude with `hx`.

Rewrite using `[e]`. Conclude with `himg`.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.factor :
    ∀ (X Y : Type) [TopologicalSpace X] [SigmaCompactSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (r : X → Y) (H : X → ℂ), Continuous r → Continuous H → (∀ x x', r x = r x' → H x = H x') → ∃ h : Y → ℂ, Measurable h ∧ ∀ x, h (r x) = H x := by
  intro X Y _ _ _ _ _ _ r H hr hH hf
  have key : ∀ F : Set X, IsClosed F → MeasurableSet (r '' F) := by
    intro F hF
    have e : r '' F = ⋃ n, r '' (F ∩ compactCovering X n) := by
      rw [← Set.image_iUnion, ← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
    rw [e]
    refine MeasurableSet.iUnion fun n => ?_
    exact (((isCompact_compactCovering X n).inter_left hF).image hr).isClosed.measurableSet
  have hrange : MeasurableSet (Set.range r) := by
    rw [← Set.image_univ]
    exact key _ isClosed_univ
  let h : Y → ℂ := fun y => if hy : ∃ x, r x = y then H hy.choose else 0
  have hh : ∀ x, h (r x) = H x := by
    intro x
    have hy : ∃ x', r x' = r x := ⟨x, rfl⟩
    simp only [h, dif_pos hy]
    exact hf _ _ hy.choose_spec
  refine ⟨h, measurable_of_isClosed fun C hC => ?_, hh⟩
  have himg : MeasurableSet (r '' (H ⁻¹' C)) := key _ (hC.preimage hH)
  have hout : ∀ y, y ∉ Set.range r → h y = 0 := by
    intro y hy
    have hy' : ¬ ∃ x, r x = y := hy
    simp only [h, dif_neg hy']
  by_cases h0 : (0 : ℂ) ∈ C
  · have e : h ⁻¹' C = r '' (H ⁻¹' C) ∪ (Set.range r)ᶜ := by
      ext y
      constructor
      · intro hy
        by_cases hyr : y ∈ Set.range r
        · obtain ⟨x, rfl⟩ := hyr
          refine Or.inl ⟨x, ?_, rfl⟩
          have : h (r x) ∈ C := hy
          rw [hh] at this
          exact this
        · exact Or.inr hyr
      · rintro (⟨x, hx, rfl⟩ | hy)
        · show h (r x) ∈ C
          rw [hh]
          exact hx
        · show h y ∈ C
          rw [hout y hy]
          exact h0
    rw [e]
    exact himg.union hrange.compl
  · have e : h ⁻¹' C = r '' (H ⁻¹' C) := by
      ext y
      constructor
      · intro hy
        by_cases hyr : y ∈ Set.range r
        · obtain ⟨x, rfl⟩ := hyr
          refine ⟨x, ?_, rfl⟩
          have : h (r x) ∈ C := hy
          rw [hh] at this
          exact this
        · have : h y ∈ C := hy
          rw [hout y hyr] at this
          exact absurd this h0
      · rintro ⟨x, hx, rfl⟩
        show h (r x) ∈ C
        rw [hh]
        exact hx
    rw [e]
    exact himg
