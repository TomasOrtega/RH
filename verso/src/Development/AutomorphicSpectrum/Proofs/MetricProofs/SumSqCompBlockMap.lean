import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

/- English proof (translation)
Take `⟨hκ, hvi, hblk, hsurj⟩` from `hv`. Establish `key : ∀ m : ιk k', ∃ i : ι (κ k'), v ⟨k', m⟩ = ⟨κ k', i⟩`. Introduce `m`. Establish `h` using `hblk ⟨k', m⟩`. Break down `hh : v ⟨k', m⟩ with ⟨c, i⟩` into its components or cases.

Rewrite `h` using `[hh]`. Simplify using `only at h`. Substitute `h` using the available equality. Conclude with `⟨i, rfl⟩`. Use `choose g hg using key`.

Establish `hinj : Function.Injective g`. Introduce `m m' hmm`. Establish `h : v ⟨k', m⟩ = v ⟨k', m'⟩` using `by rw [hg, hg, hmm]`. Establish `h'` using `hvi h`. Simplify using `using h'`.

Establish `hsur : Function.Surjective g`. Introduce `i`. Take `⟨⟨k'', m⟩, hp⟩` from `hsurj ⟨κ k', i⟩ ⟨k', rfl⟩`. Establish `h` using `hblk ⟨k'', m⟩`. Rewrite `h` using `[hp]`.

Establish `hk : k'' = k'` using `(hκ h).symm`. Substitute `hk` using the available equality. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite `hp` using `[hg]`. Simplify using `using hp`.

Establish `hbij : Function.Bijective g` using `⟨hinj, hsur⟩`. Rewrite using `[← hbij.sum_comp (fun i => ‖z ⟨κ k', i⟩‖ ^ 2)]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, hg]`.
-/
theorem sum_sq_comp_blockMap {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]
    {Kk : Type} {ιk : Kk → Type} [∀ k, Fintype (ιk k)]
    {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hv : IsBlockMap κ v)
    (z : (Σ k, ι k) → ℂ) (k' : Kk) :
    ∑ m, ‖(z ∘ v) ⟨k', m⟩‖ ^ 2 = ∑ i, ‖z ⟨κ k', i⟩‖ ^ 2 := by
  obtain ⟨hκ, hvi, hblk, hsurj⟩ := hv
  have key : ∀ m : ιk k', ∃ i : ι (κ k'), v ⟨k', m⟩ = ⟨κ k', i⟩ := by
    intro m
    have h := hblk ⟨k', m⟩
    rcases hh : v ⟨k', m⟩ with ⟨c, i⟩
    rw [hh] at h
    simp only at h
    subst h
    exact ⟨i, rfl⟩
  choose g hg using key
  have hinj : Function.Injective g := by
    intro m m' hmm
    have h : v ⟨k', m⟩ = v ⟨k', m'⟩ := by rw [hg, hg, hmm]
    have h' := hvi h
    simpa using h'
  have hsur : Function.Surjective g := by
    intro i
    obtain ⟨⟨k'', m⟩, hp⟩ := hsurj ⟨κ k', i⟩ ⟨k', rfl⟩
    have h := hblk ⟨k'', m⟩
    rw [hp] at h
    have hk : k'' = k' := (hκ h).symm
    subst hk
    refine ⟨m, ?_⟩
    rw [hg] at hp
    simpa using hp
  have hbij : Function.Bijective g := ⟨hinj, hsur⟩
  rw [← hbij.sum_comp (fun i => ‖z ⟨κ k', i⟩‖ ^ 2)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Function.comp_apply, hg]

/- English proof (translation)
Introduce `K _ ι _ Kk _ ιk _ κ v a z hv ha`. Rewrite using `[fsHerm_h, fsHerm_h]`. Unfold `refNorm`. Use `symm`. Use `Fintype.prod_of_injective κ hv.1 _ _ ?_ ?_` and prove the remaining obligations.

Introduce `k hk`. Establish `h0 : a k = 0`. Assume the negation of the conclusion as `h`. Conclude with `hk (ha k h)`. Simplify using `[h0]`.

Introduce `k'`. Rewrite using `[sum_sq_comp_blockMap hv z k']`.
-/
theorem fsHerm_h_blockMap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (a : K → ℤ) (z : (Σ k, ι k) → ℂ), IsBlockMap κ v → (∀ k, a k ≠ 0 → k ∈ Set.range κ) → (fsHerm ι a).h z = (fsHerm ιk fun k => a (κ k)).h (z ∘ v) := by
  intro K _ ι _ Kk _ ιk _ κ v a z hv ha
  rw [fsHerm_h, fsHerm_h]
  unfold refNorm
  symm
  refine Fintype.prod_of_injective κ hv.1 _ _ ?_ ?_
  · intro k hk
    have h0 : a k = 0 := by
      by_contra h
      exact hk (ha k h)
    simp [h0]
  · intro k'
    rw [sum_sq_comp_blockMap hv z k']

end GlobalTheory.CompanionTheory.Ar.PB.StepW
