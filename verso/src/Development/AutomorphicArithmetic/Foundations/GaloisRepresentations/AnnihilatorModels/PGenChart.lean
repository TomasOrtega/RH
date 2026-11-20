import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `Y π U hU V _ _ f hmin`. Use `set πU := Y.presheaf.map (homOfLE le_top).op π with hπU`. Set `P : PrimeSpectrum Γ(Y, U)` to `⟨Ideal.comap f (IsLocalRing.maximalIdeal V), inferInstance⟩`. Establish `hx : ptOf hU V f (IsLocalRing.closedPoint V) = hU.fromSpec P` using `rfl`. Establish `hinU : ∀ q : PrimeSpectrum Γ(Y, U), hU.fromSpec q ∈ U`.

Introduce `q`. Establish `: hU.fromSpec q ∈ Set.range hU.fromSpec` using `⟨q, rfl⟩`. Rewrite `this` using `[hU.range_fromSpec]`. Conclude with `this`. Establish `hmem : ∀ q : PrimeSpectrum Γ(Y, U), hU.fromSpec q ∈ Y.basicOpen π ↔ πU ∉ q.asIdeal`.

Introduce `q`. Establish `h1 : q ∈ PrimeSpectrum.basicOpen πU ↔ hU.fromSpec q ∈ Y.basicOpen πU`. Rewrite using `[← hU.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression. Rewrite using `[← PrimeSpectrum.mem_basicOpen, h1, hπU, Scheme.basicOpen_res]`.

Conclude with `⟨fun h => ⟨hinU q, h⟩, fun h => h.2⟩`. Rewrite using `[hx]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmem, not_not]`. Conclude with `hmin.1.2 (Ideal.subset_span (Set.mem_singleton _))`.

Introduce `x' hx' hsp`. Establish `hx'U : x' ∈ U` using `hsp.mem_open U.isOpen (hinU P)`. Choose the witnesses or unpack the hypotheses as in `⟨q, rfl⟩ : x' ∈ Set.range hU.fromSpec := by`. Rewrite using `[hU.range_fromSpec]`. Conclude with `hx'U`.

Establish `hqp : q ⤳ P` using `hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hsp`. Establish `hqp' : q.asIdeal ≤ P.asIdeal` using `(PrimeSpectrum.le_iff_specializes (R := Γ(Y, U)) q P).mpr hqp`. Establish `hπq : πU ∈ q.asIdeal`. Assume the negation of the conclusion as `h`. Conclude with `hx' ((hmem q).mpr h)`.

Establish `hPq : P.asIdeal ≤ q.asIdeal` using `hmin.2 ⟨q.2, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπq)⟩ hqp'`. Use `congr 1`. Conclude with `PrimeSpectrum.ext (le_antisymm hqp' hPq)`.
-/
theorem UpperTheory.Gal.crystallineComparison.genChart_of :
    GenChart := by
  intro Y π U hU V _ _ f hmin
  set πU := Y.presheaf.map (homOfLE le_top).op π with hπU
  let P : PrimeSpectrum Γ(Y, U) := ⟨Ideal.comap f (IsLocalRing.maximalIdeal V), inferInstance⟩
  have hx : ptOf hU V f (IsLocalRing.closedPoint V) = hU.fromSpec P := rfl
  have hinU : ∀ q : PrimeSpectrum Γ(Y, U), hU.fromSpec q ∈ U := by
    intro q
    have : hU.fromSpec q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
    rw [hU.range_fromSpec] at this
    exact this
  have hmem : ∀ q : PrimeSpectrum Γ(Y, U), hU.fromSpec q ∈ Y.basicOpen π ↔ πU ∉ q.asIdeal := by
    intro q
    have h1 : q ∈ PrimeSpectrum.basicOpen πU ↔ hU.fromSpec q ∈ Y.basicOpen πU := by
      rw [← hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← PrimeSpectrum.mem_basicOpen, h1, hπU, Scheme.basicOpen_res]
    exact ⟨fun h => ⟨hinU q, h⟩, fun h => h.2⟩
  rw [hx]
  refine ⟨?_, ?_⟩
  · rw [hmem, not_not]
    exact hmin.1.2 (Ideal.subset_span (Set.mem_singleton _))
  · intro x' hx' hsp
    have hx'U : x' ∈ U := hsp.mem_open U.isOpen (hinU P)
    obtain ⟨q, rfl⟩ : x' ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact hx'U
    have hqp : q ⤳ P := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hsp
    have hqp' : q.asIdeal ≤ P.asIdeal := (PrimeSpectrum.le_iff_specializes (R := Γ(Y, U)) q P).mpr hqp
    have hπq : πU ∈ q.asIdeal := by
      by_contra h
      exact hx' ((hmem q).mpr h)
    have hPq : P.asIdeal ≤ q.asIdeal :=
      hmin.2 ⟨q.2, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπq)⟩ hqp'
    congr 1
    exact PrimeSpectrum.ext (le_antisymm hqp' hPq)
