import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.PrimeAvoid

/- English proof (translation)
Set `W : Set (PrimeSpectrum Γ(X, U))` to `hU.fromSpec ⁻¹' (V₀ : Set X)`. Establish `hWo : IsOpen W` using `(hU.fromSpec ⁻¹ᵁ V₀).isOpen`. Set `I : Ideal Γ(X, U)` to `PrimeSpectrum.vanishingIdeal Wᶜ`. Set `s : Set (Ideal Γ(X, U))` to `PrimeSpectrum.asIdeal '' (hU.fromSpec ⁻¹' K)`. Establish `hs : s.Finite` using `(hK.preimage hU.fromSpec.isOpenEmbedding.injective.injOn).image _`.

Establish `hnot : ¬ ((I : Set Γ(X, U)) ⊆ ⋃ P ∈ s, (P : Set Γ(X, U)))`. Introduce `h`. Take `⟨P, ⟨p, hpK, rfl⟩, hIp⟩` from `(Ideal.subset_union_prime_finite (f := fun P : Ideal Γ(X, U) => P) hs ⊥ ⊥ (fun P hP _ _ => by obtain ⟨p, -, rfl⟩ := hP; exact p.isPrime)).1 h`. Establish `hpW : p ∈ W` using `hKV hpK`. Establish `hcl : p ∈ closure Wᶜ`.

Rewrite using `[← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]`. Conclude with `(PrimeSpectrum.mem_zeroLocus _ _).2 hIp`. Rewrite `hcl` using `[hWo.isClosed_compl.closure_eq]`. Conclude with `hcl hpW`. Take `⟨g, hgI, hgs⟩` from `Set.not_subset.1 hnot`.

Use `⟨g, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Choose the witnesses or unpack the hypotheses as in `⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by`. Rewrite using `[hU.range_fromSpec]`. Conclude with `hV (hKV hx)`.

Establish `hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g`. Rewrite using `[hU.fromSpec_preimage_basicOpen]`. Conclude with `(PrimeSpectrum.mem_basicOpen g p).2 fun hg => hgs (Set.mem_biUnion ⟨p, hx, rfl⟩ hg)`. Conclude with `hp`. Introduce `x hx`.

Choose the witnesses or unpack the hypotheses as in `⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by`. Rewrite using `[hU.range_fromSpec]`. Conclude with `X.basicOpen_le g hx`. Establish `hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g` using `hx`. Rewrite `hp` using `[hU.fromSpec_preimage_basicOpen]`.

Establish `hp'` using `(PrimeSpectrum.mem_basicOpen g p).1 hp`. Assume the negation of the conclusion as `hpV`. Conclude with `hp' ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hgI p hpV)`.
-/
theorem exists_basicOpen_between {X : Scheme.{0}} (U V₀ : X.Opens) (hU : IsAffineOpen U)
    (hV : V₀ ≤ U) (K : Set X) (hK : K.Finite) (hKV : K ⊆ V₀) :
    ∃ f : Γ(X, U), K ⊆ X.basicOpen f ∧ X.basicOpen f ≤ V₀ := by
  classical
  let W : Set (PrimeSpectrum Γ(X, U)) := hU.fromSpec ⁻¹' (V₀ : Set X)
  have hWo : IsOpen W := (hU.fromSpec ⁻¹ᵁ V₀).isOpen
  let I : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal Wᶜ
  let s : Set (Ideal Γ(X, U)) := PrimeSpectrum.asIdeal '' (hU.fromSpec ⁻¹' K)
  have hs : s.Finite := (hK.preimage hU.fromSpec.isOpenEmbedding.injective.injOn).image _
  have hnot : ¬ ((I : Set Γ(X, U)) ⊆ ⋃ P ∈ s, (P : Set Γ(X, U))) := by
    intro h
    obtain ⟨P, ⟨p, hpK, rfl⟩, hIp⟩ :=
      (Ideal.subset_union_prime_finite (f := fun P : Ideal Γ(X, U) => P) hs ⊥ ⊥
        (fun P hP _ _ => by obtain ⟨p, -, rfl⟩ := hP; exact p.isPrime)).1 h
    have hpW : p ∈ W := hKV hpK
    have hcl : p ∈ closure Wᶜ := by
      rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact (PrimeSpectrum.mem_zeroLocus _ _).2 hIp
    rw [hWo.isClosed_compl.closure_eq] at hcl
    exact hcl hpW
  obtain ⟨g, hgI, hgs⟩ := Set.not_subset.1 hnot
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact hV (hKV hx)
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen g p).2 fun hg => hgs (Set.mem_biUnion ⟨p, hx, rfl⟩ hg)
    exact hp
  · intro x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact X.basicOpen_le g hx
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := hx
    rw [hU.fromSpec_preimage_basicOpen] at hp
    have hp' := (PrimeSpectrum.mem_basicOpen g p).1 hp
    by_contra hpV
    exact hp' ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hgI p hpV)

end GlobalTheory.CompanionTheory.PrimeAvoid
