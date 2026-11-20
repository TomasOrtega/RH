import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartIff

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

/- English proof (translation)
Use `h.isFinite` as an intermediate fact. Establish `hsat : ∀ u v : V.toScheme, q u = q v → V.ι u ∈ V' → V.ι v ∈ V'`. Introduce `u v huv hu`. Take `⟨p, hpa, hpb⟩` from `(h.apply_eq_iff u v).1 huv`. Establish `hp : p ∈ a ⁻¹ᵁ V'` using `by show a p ∈ V'`.

Rewrite using `[hpa]`. Conclude with `hu`. Rewrite `hp` using `[hs]`. Establish `hb : b p ∈ V'` using `hp`. Rewrite `hb` using `[hpb]`. Then use the resulting hypothesis.

Set `C : Set V.toScheme` to `((V.ι ⁻¹ᵁ V' : V.toScheme.Opens) : Set V.toScheme)ᶜ`. Establish `hC : IsClosed C` using `(V.ι ⁻¹ᵁ V').isOpen.isClosed_compl`. Establish `hqC : IsClosed (q '' C)` using `q.isClosedMap C hC`. Use `⟨⟨(q '' C)ᶜ, hqC.isOpen_compl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Assume the negation of the conclusion as `hx`. Conclude with `hu ⟨u, hx, rfl⟩`. Introduce `hx`.

Choose the witnesses or unpack the hypotheses as in `⟨u, rfl⟩ : ∃ u, V.ι u = x := by`. Rewrite using `[← Set.mem_range, Scheme.Opens.range_ι]`. Conclude with `hV hx`. Use `⟨u, ?_, rfl⟩` and prove the remaining obligations. Introduce and unpack `⟨v, hv, hvu⟩`.

Conclude with `hv (hsat u v hvu.symm hx)`.
-/
theorem IsChart.exists_opens_image_preimage {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens}
    {q : V.toScheme ⟶ Y} (h : IsChart a b V q) (V' : X.Opens) (hV : V' ≤ V)
    (hs : a ⁻¹ᵁ V' = b ⁻¹ᵁ V') : ∃ D : Y.Opens, V.ι ''ᵁ (q ⁻¹ᵁ D) = V' := by
  have := h.isFinite
  have hsat : ∀ u v : V.toScheme, q u = q v → V.ι u ∈ V' → V.ι v ∈ V' := by
    intro u v huv hu
    obtain ⟨p, hpa, hpb⟩ := (h.apply_eq_iff u v).1 huv
    have hp : p ∈ a ⁻¹ᵁ V' := by
      show a p ∈ V'
      rw [hpa]
      exact hu
    rw [hs] at hp
    have hb : b p ∈ V' := hp
    rwa [hpb] at hb
  let C : Set V.toScheme := ((V.ι ⁻¹ᵁ V' : V.toScheme.Opens) : Set V.toScheme)ᶜ
  have hC : IsClosed C := (V.ι ⁻¹ᵁ V').isOpen.isClosed_compl
  have hqC : IsClosed (q '' C) := q.isClosedMap C hC
  refine ⟨⟨(q '' C)ᶜ, hqC.isOpen_compl⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_contra hx
    exact hu ⟨u, hx, rfl⟩
  · intro hx
    obtain ⟨u, rfl⟩ : ∃ u, V.ι u = x := by
      rw [← Set.mem_range, Scheme.Opens.range_ι]
      exact hV hx
    refine ⟨u, ?_, rfl⟩
    rintro ⟨v, hv, hvu⟩
    exact hv (hsat u v hvu.symm hx)

end GlobalTheory.CompanionTheory.FreeQuotGlue
