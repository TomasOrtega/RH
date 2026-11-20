import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Establish `hq' : q ∈ e.source`. Assume the negation of the conclusion as `h`. Conclude with `hq (Set.indicator_of_notMem h _)`. Rewrite `hq` using `[Set.indicator_of_mem hq']`. Conclude with `⟨e q, subset_tsupport _ hq, e.left_inv hq'⟩`.
-/
theorem extend_support_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (q : M)
    (hq : e.source.indicator (G ∘ e) q ≠ 0) : q ∈ e.symm '' tsupport G := by
  have hq' : q ∈ e.source := by
    by_contra h; exact hq (Set.indicator_of_notMem h _)
  rw [Set.indicator_of_mem hq'] at hq
  exact ⟨e q, subset_tsupport _ hq, e.left_inv hq'⟩

/- English proof (translation)
Establish `hopen : IsOpen (e'.target ∩ e'.symm ⁻¹' e.source)` using `e'.isOpen_inter_preimage_symm e.open_source`. Use `filter_upwards [hopen.mem_nhds ⟨hy, hs⟩] with w hw`. Take `⟨hw1, hw2⟩` from `hw`. Establish `hw3 : e'.symm w ∈ e'.source` using `e'.map_target hw1`. Rewrite using `[Function.comp_apply, Set.indicator_of_mem (show e'.symm w ∈ e.source from hw2), Function.comp_apply, ← he hw2, he' hw3, e'.right_inv hw1]`.
-/
theorem extend_eventuallyEq {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (he : IsChart n z e)
    (he' : IsChart n z e') (y : V n) (hy : y ∈ e'.target) (hs : e'.symm y ∈ e.source) :
    (e.source.indicator (G ∘ e) ∘ e'.symm) =ᶠ[𝓝 y] G := by
  have hopen : IsOpen (e'.target ∩ e'.symm ⁻¹' e.source) :=
    e'.isOpen_inter_preimage_symm e.open_source
  filter_upwards [hopen.mem_nhds ⟨hy, hs⟩] with w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hw3 : e'.symm w ∈ e'.source := e'.map_target hw1
  rw [Function.comp_apply, Set.indicator_of_mem (show e'.symm w ∈ e.source from hw2), Function.comp_apply, ← he hw2, he' hw3,
    e'.right_inv hw1]

/- English proof (translation)
Introduce `z _hz e G he hG hGc hGt`. Establish `hK : IsCompact (e.symm '' tsupport G)` using `hGc.image_of_continuousOn (e.continuousOn_symm.mono hGt)`. Establish `hKs : e.symm '' tsupport G ⊆ e.source`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `e.map_target (hGt hy)`.

Establish `hts : tsupport (e.source.indicator (G ∘ e)) ⊆ e.symm '' tsupport G` using `closure_minimal (fun q hq => extend_support_subset e G q hq) hK.isClosed`. Establish `hw : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → ∀ x ∈ e''.source, x ∈ e.source → (e.source.indicator (G ∘ e) ∘ e''.symm) =ᶠ[𝓝 (z x)] G ∧ z x = e x`. Introduce `e'' h1 x h2 hx`. Establish `hzx : z x = e'' x` using `h1 h2`. Use `⟨?_, he hx⟩` and prove the remaining obligations.

Rewrite using `[hzx]`. Use `extend_eventuallyEq z e e'' G he h1 (e'' x) (e''.map_source h2) ?_` and prove the remaining obligations. Rewrite using `[e''.left_inv h2]`. Conclude with `hx`. Use `⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKs, ?_⟩` and prove the remaining obligations.

Introduce `e' he' y hy`. Distinguish the cases in `hs : e'.symm y ∈ e.source`. Conclude with `(hG.contDiffAt.congr_of_eventuallyEq (extend_eventuallyEq z e e' G he he' y hy hs)).contDiffWithinAt`. Establish `hq : e'.symm y ∉ tsupport (e.source.indicator (G ∘ e))` using `fun h => hs (hKs (hts h))`. Establish `h0` using `notMem_tsupport_iff_eventuallyEq.1 hq`.

Establish `h0'` using `h0.comp_tendsto (e'.continuousAt_symm hy).tendsto`. Conclude with `(contDiffAt_const.congr_of_eventuallyEq h0').contDiffWithinAt`. Introduce `j x hx`. Establish `key : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → x ∈ e''.source → wd n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wd n j G (e x) ∧ wdb n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wdb n j G (e x)`. Introduce `e'' h1 h2`.

Take `⟨hev, hzx⟩` from `hw e'' h1 x h2 hx`. Prove the components needed by the constructor for the conclusion. Unfold `wd`. Rewrite using `[hev.fderiv_eq, hzx]`. Unfold `wdb`.

Rewrite using `[hev.fderiv_eq, hzx]`. Establish `hex : ∃ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' ∧ x ∈ e''.source` using `⟨e, he, hx⟩`. Prove the components needed by the constructor for the conclusion. Simplify using `only [d, dif_pos hex]`. Conclude with `(key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).1`.

Simplify using `only [db, dif_pos hex]`. Conclude with `(key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).2`.
-/
theorem extend (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : ExtendStatement n M := by
  intro z _hz e G he hG hGc hGt
  have hK : IsCompact (e.symm '' tsupport G) :=
    hGc.image_of_continuousOn (e.continuousOn_symm.mono hGt)
  have hKs : e.symm '' tsupport G ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩; exact e.map_target (hGt hy)
  have hts : tsupport (e.source.indicator (G ∘ e)) ⊆ e.symm '' tsupport G :=
    closure_minimal (fun q hq => extend_support_subset e G q hq) hK.isClosed
  have hw : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → ∀ x ∈ e''.source, x ∈ e.source →
      (e.source.indicator (G ∘ e) ∘ e''.symm) =ᶠ[𝓝 (z x)] G ∧ z x = e x := by
    intro e'' h1 x h2 hx
    have hzx : z x = e'' x := h1 h2
    refine ⟨?_, he hx⟩
    rw [hzx]
    refine extend_eventuallyEq z e e'' G he h1 (e'' x) (e''.map_source h2) ?_
    rw [e''.left_inv h2]; exact hx
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKs, ?_⟩
  · intro e' he' y hy
    by_cases hs : e'.symm y ∈ e.source
    · exact (hG.contDiffAt.congr_of_eventuallyEq
        (extend_eventuallyEq z e e' G he he' y hy hs)).contDiffWithinAt
    · have hq : e'.symm y ∉ tsupport (e.source.indicator (G ∘ e)) := fun h => hs (hKs (hts h))
      have h0 := notMem_tsupport_iff_eventuallyEq.1 hq
      have h0' := h0.comp_tendsto (e'.continuousAt_symm hy).tendsto
      exact (contDiffAt_const.congr_of_eventuallyEq h0').contDiffWithinAt
  · intro j x hx
    have key : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → x ∈ e''.source →
        wd n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wd n j G (e x) ∧
        wdb n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wdb n j G (e x) := by
      intro e'' h1 h2
      obtain ⟨hev, hzx⟩ := hw e'' h1 x h2 hx
      constructor
      · unfold wd; rw [hev.fderiv_eq, hzx]
      · unfold wdb; rw [hev.fderiv_eq, hzx]
    have hex : ∃ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' ∧ x ∈ e''.source := ⟨e, he, hx⟩
    constructor
    · simp only [d, dif_pos hex]
      exact (key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).1
    · simp only [db, dif_pos hex]
      exact (key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).2

end

end ReciprocityTheory.L2DbarEstimates.F
