import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `X W hW V hVW s hs`. Break down `s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩` into its components or cases. Use `⟨0, ?_, fun x hx => absurd hx (Finset.notMem_empty x)⟩` and prove the remaining obligations. Rewrite using `[Scheme.basicOpen_zero]`. Conclude with `bot_le`.

Use `set Z : Set (PrimeSpectrum Γ(X, W)) := {p | hW.fromSpec p ∉ V} with hZ`. Establish `hZc : IsClosed Z`. Establish `h` using `(hW.fromSpec ⁻¹ᵁ V).isOpen.isClosed_compl`. Conclude with `h`. Set `P : X → Ideal Γ(X, W)` to `fun x => if h : x ∈ W then (hW.primeIdealOf ⟨x, h⟩).asIdeal else ⊤`.

Establish `hPx : ∀ x (h : x ∈ W), P x = (hW.primeIdealOf ⟨x, h⟩).asIdeal` using `fun x h => by`. Simplify using `only [P, dif_pos h]`. Establish `hP : ∀ i ∈ s, i ≠ x₀ → i ≠ x₀ → (P i).IsPrime`. Introduce `x hx _ _`. Rewrite using `[hPx x (hVW (hs x hx))]`.

Conclude with `(hW.primeIdealOf _).isPrime`. Establish `key : ¬ ((PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) ⊆ ⋃ i ∈ (↑s : Set X), (P i : Set Γ(X, W)))`. Rewrite using `[Ideal.subset_union_prime x₀ x₀ hP]`. Introduce and unpack `⟨x, hx, hle⟩`. Establish `hxW : x ∈ W` using `hVW (hs x hx)`.

Rewrite `hle` using `[hPx x hxW]`. Establish `hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈ PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W))` using `(PrimeSpectrum.mem_zeroLocus _ _).2 hle`. Rewrite `hmem` using `[PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq]`. Apply `hmem` to reduce the goal to its premises. Use `show hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ V`.

Rewrite using `[hW.fromSpec_primeIdealOf]`. Conclude with `hs x hx`. Take `⟨f, hfI, hfP⟩` from `Set.not_subset.mp key`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Establish `hyW : y ∈ W` using `X.basicOpen_le f hy`. Take `⟨p, rfl⟩ : y ∈ Set.range hW.fromSpec` from `by rw [hW.range_fromSpec]; exact hyW`. Establish `hp : p ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f` using `hy`. Rewrite `hp` using `[hW.fromSpec_preimage_basicOpen]`. Assume the negation of the conclusion as `hnot`.

Establish `hpZ : p ∈ Z` using `hnot`. Conclude with `(PrimeSpectrum.mem_basicOpen _ _).1 hp ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hfI p hpZ)`. Introduce `x hx`. Establish `hxW : x ∈ W` using `hVW (hs x hx)`. Establish `hf : f ∉ (hW.primeIdealOf ⟨x, hxW⟩).asIdeal`.

Introduce `h`. Apply `hfP` to reduce the goal to its premises. Rewrite using `[Set.mem_iUnion₂]`. Conclude with `⟨x, hx, by rw [hPx x hxW]; exact h⟩`. Establish `hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f`.

Rewrite using `[hW.fromSpec_preimage_basicOpen]`. Conclude with `(PrimeSpectrum.mem_basicOpen _ _).2 hf`. Establish `h2 : hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ X.basicOpen f` using `hmem`. Rewrite `h2` using `[hW.fromSpec_primeIdealOf]`. Then use the resulting hypothesis.
-/
theorem exists_basicOpen_between_finset_and_open : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (V : X.Opens), V ≤ W → ∀ s : Finset X, (∀ x ∈ s, x ∈ V) → ∃ f : Γ(X, W), X.basicOpen f ≤ V ∧ ∀ x ∈ s, x ∈ X.basicOpen f := by
  classical
  intro X W hW V hVW s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · refine ⟨0, ?_, fun x hx => absurd hx (Finset.notMem_empty x)⟩
    rw [Scheme.basicOpen_zero]
    exact bot_le
  set Z : Set (PrimeSpectrum Γ(X, W)) := {p | hW.fromSpec p ∉ V} with hZ
  have hZc : IsClosed Z := by
    have h := (hW.fromSpec ⁻¹ᵁ V).isOpen.isClosed_compl
    exact h
  let P : X → Ideal Γ(X, W) := fun x => if h : x ∈ W then (hW.primeIdealOf ⟨x, h⟩).asIdeal else ⊤
  have hPx : ∀ x (h : x ∈ W), P x = (hW.primeIdealOf ⟨x, h⟩).asIdeal := fun x h => by
    simp only [P, dif_pos h]
  have hP : ∀ i ∈ s, i ≠ x₀ → i ≠ x₀ → (P i).IsPrime := by
    intro x hx _ _
    rw [hPx x (hVW (hs x hx))]
    exact (hW.primeIdealOf _).isPrime
  have key : ¬ ((PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) ⊆
      ⋃ i ∈ (↑s : Set X), (P i : Set Γ(X, W))) := by
    rw [Ideal.subset_union_prime x₀ x₀ hP]
    rintro ⟨x, hx, hle⟩
    have hxW : x ∈ W := hVW (hs x hx)
    rw [hPx x hxW] at hle
    have hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈
        PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) :=
      (PrimeSpectrum.mem_zeroLocus _ _).2 hle
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq] at hmem
    apply hmem
    show hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ V
    rw [hW.fromSpec_primeIdealOf]
    exact hs x hx
  obtain ⟨f, hfI, hfP⟩ := Set.not_subset.mp key
  refine ⟨f, ?_, ?_⟩
  · intro y hy
    have hyW : y ∈ W := X.basicOpen_le f hy
    obtain ⟨p, rfl⟩ : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
    have hp : p ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f := hy
    rw [hW.fromSpec_preimage_basicOpen] at hp
    by_contra hnot
    have hpZ : p ∈ Z := hnot
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hp
      ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hfI p hpZ)
  · intro x hx
    have hxW : x ∈ W := hVW (hs x hx)
    have hf : f ∉ (hW.primeIdealOf ⟨x, hxW⟩).asIdeal := by
      intro h
      apply hfP
      rw [Set.mem_iUnion₂]
      exact ⟨x, hx, by rw [hPx x hxW]; exact h⟩
    have hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hW.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).2 hf
    have h2 : hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ X.basicOpen f := hmem
    rwa [hW.fromSpec_primeIdealOf] at h2

end GlobalTheory.Mum
