import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RingOfIntegersCovering
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PackingSeparation

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField InfinitePlace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Introduce `r X`. Use `⟨fun w' => ?_, fun R hR => PackingSeparation.count R hR⟩` and prove the remaining obligations. Establish `hconjmem : ∀ φ : E →+* ℂ, φ ∉ X.Ψ → ComplexEmbedding.conjugate φ ∈ X.Ψ`. Introduce `φ h`. Use `X.cmType (ComplexEmbedding.conjugate φ)` as an intermediate fact.

Rewrite `this` using `[TraceIntegralBasis.conj_conj]`. Conclude with `this.mpr h`. Set `Z : TraceIntegralBasis.VS E` to `WithLp.toLp 2 (fun w : TraceIntegralBasis.CP E => if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩ else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩))`. Take `⟨α, hα⟩` from `RingOfIntegersCovering.cover_OE Z`. Use `⟨α, fun τ => ?_⟩` and prove the remaining obligations.

Use `set w : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩ with hw`. Establish `hcoord : ‖Z w - w.1.embedding (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E`. Establish `h` using `PiLp.norm_apply_le (Z - TraceIntegralBasis.iota E (α : E)) w`. Rewrite `h` using `[PiLp.sub_apply, TraceIntegralBasis.iota_apply]`. Conclude with `h.trans hα`.

Establish `hZw : Z w = if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩ else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩)` using `rfl`. Establish `hmk : InfinitePlace.mk w.1.embedding = InfinitePlace.mk τ.1` using `mk_embedding _`. Break down `InfinitePlace.mk_eq_iff.mp hmk with h | h` into its components or cases. Establish `hmem : w.1.embedding ∈ X.Ψ` using `h ▸ τ.2`. Establish `hZ : Z w = w' τ`.

Rewrite using `[hZw, dif_pos hmem]`. Use `congr 1`. Conclude with `Subtype.ext h`. Rewrite `hcoord` using `[hZ, h]`. Rewrite `hcoord` using `[norm_sub_rev]`. Then use the resulting hypothesis.

Establish `hnot : w.1.embedding ∉ X.Ψ`. Introduce `hm`. Conclude with `((X.cmType _).mp hm) (h ▸ τ.2)`. Establish `hZ : Z w = conj (w' τ)`. Rewrite using `[hZw, dif_neg hnot]`.

Use `congr 2`. Conclude with `Subtype.ext h`. Establish `hemb : w.1.embedding (α : E) = conj (τ.1 (α : E))`. Rewrite using `[← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]`. Rewrite `hcoord` using `[hZ, hemb, ← map_sub, Complex.norm_conj]`.

Rewrite `hcoord` using `[norm_sub_rev]`. Then use the resulting hypothesis.
-/
theorem integerApproximationCount_holds : IntegerApproximationCount (E := E) := by
  intro r X
  refine ⟨fun w' => ?_, fun R hR => PackingSeparation.count R hR⟩
  classical
  have hconjmem : ∀ φ : E →+* ℂ, φ ∉ X.Ψ → ComplexEmbedding.conjugate φ ∈ X.Ψ := by
    intro φ h
    have := X.cmType (ComplexEmbedding.conjugate φ)
    rw [TraceIntegralBasis.conj_conj] at this
    exact this.mpr h
  let Z : TraceIntegralBasis.VS E := WithLp.toLp 2 (fun w : TraceIntegralBasis.CP E =>
    if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
    else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩))
  obtain ⟨α, hα⟩ := RingOfIntegersCovering.cover_OE Z
  refine ⟨α, fun τ => ?_⟩
  set w : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩ with hw
  have hcoord : ‖Z w - w.1.embedding (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have h := PiLp.norm_apply_le (Z - TraceIntegralBasis.iota E (α : E)) w
    rw [PiLp.sub_apply, TraceIntegralBasis.iota_apply] at h
    exact h.trans hα
  have hZw : Z w = if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
      else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩) := rfl
  have hmk : InfinitePlace.mk w.1.embedding = InfinitePlace.mk τ.1 := mk_embedding _
  rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
  · have hmem : w.1.embedding ∈ X.Ψ := h ▸ τ.2
    have hZ : Z w = w' τ := by
      rw [hZw, dif_pos hmem]
      congr 1
      exact Subtype.ext h
    rw [hZ, h] at hcoord
    rwa [norm_sub_rev] at hcoord
  · have hnot : w.1.embedding ∉ X.Ψ := by
      intro hm
      exact ((X.cmType _).mp hm) (h ▸ τ.2)
    have hZ : Z w = conj (w' τ) := by
      rw [hZw, dif_neg hnot]
      congr 2
      exact Subtype.ext h
    have hemb : w.1.embedding (α : E) = conj (τ.1 (α : E)) := by
      rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    rw [hZ, hemb, ← map_sub, Complex.norm_conj] at hcoord
    rwa [norm_sub_rev] at hcoord

end ReciprocityTheory.ChartRestriction.G.FD
