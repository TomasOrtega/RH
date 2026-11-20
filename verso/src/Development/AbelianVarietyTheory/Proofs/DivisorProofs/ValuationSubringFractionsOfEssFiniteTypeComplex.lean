import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ ψ V hψ h`. Use `letI : Algebra ℂ V := (ψ.codRestrict V hψ).toAlgebra`. Establish `h' : Algebra.EssFiniteType ℂ V` using `h`. Take `⟨s, hs⟩` from `h'.cond`. Use `⟨s.image (fun x : V => (x : L)), ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Rewrite `hx` using `[Finset.mem_image]`. Take `⟨y, -, rfl⟩` from `hx`. Conclude with `y.2`. Establish `key : ∀ x ∈ Algebra.adjoin ℂ (s : Set V), ((x : V) : L) ∈ Subring.closure (Set.range ψ ∪ ↑(s.image (fun x : V => (x : L))))`.

Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `right`.

Rewrite using `[Finset.coe_image]`. Conclude with `⟨x, hx, rfl⟩`. Consider the case `algebraMap r`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `left`.

Conclude with `⟨r, rfl⟩`. Consider the case `add x y _ _ hx hy`. Simplify using `using Subring.add_mem _ hx hy`. Consider the case `mul x y _ _ hx hy`. Simplify using `using Subring.mul_mem _ hx hy`.

Introduce `v hv`. Take `⟨⟨a, m⟩, hm⟩` from `IsLocalization.surj (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set V))) V) (IsUnit.submonoid V)) (⟨v, hv⟩ : V)`. Establish `hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set V)) : V)` using `m.2`. Take `⟨u, hu'⟩` from `hu`. Establish `hinv : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) * (((u⁻¹ : Vˣ) : V) : L) = 1`.

Rewrite using `[← hu']`. Express the relevant statement in the definitionally equal form `(((u : V) * ((u⁻¹ : Vˣ) : V) : V) : L) = ((1 : V) : L)`. Rewrite using `[u.mul_inv]`. Establish `hd0 : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) ≠ 0`. Introduce `h0`.

Rewrite `hinv` using `[h0, zero_mul]`. Conclude with `zero_ne_one hinv`. Establish `hmL` using `congrArg (fun z : V => (z : L)) hm`. Simplify using `only at hmL`. Use `⟨((a : V) : L), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L), key _ (m : Algebra.adjoin ℂ (s : Set V)).2, hd0, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_eq_of_mul_eq_one_right hinv]`. Conclude with `((u⁻¹ : Vˣ) : V).2`. Rewrite using `[eq_div_iff hd0]`. Simplify using `using hmL`.
-/
theorem valuationSubring_fractions_of_essFiniteType : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  classical
  intro L _ ψ V hψ h
  letI : Algebra ℂ V := (ψ.codRestrict V hψ).toAlgebra
  have h' : Algebra.EssFiniteType ℂ V := h
  obtain ⟨s, hs⟩ := h'.cond
  refine ⟨s.image (fun x : V => (x : L)), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have key : ∀ x ∈ Algebra.adjoin ℂ (s : Set V),
      ((x : V) : L) ∈ Subring.closure (Set.range ψ ∪ ↑(s.image (fun x : V => (x : L)))) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Subring.subset_closure
      right
      rw [Finset.coe_image]
      exact ⟨x, hx, rfl⟩
    | algebraMap r =>
      apply Subring.subset_closure
      left
      exact ⟨r, rfl⟩
    | add x y _ _ hx hy =>
      simpa using Subring.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      simpa using Subring.mul_mem _ hx hy
  intro v hv
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set V))) V) (IsUnit.submonoid V)) (⟨v, hv⟩ : V)
  have hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set V)) : V) := m.2
  obtain ⟨u, hu'⟩ := hu
  have hinv : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) * (((u⁻¹ : Vˣ) : V) : L) = 1 := by
    rw [← hu']
    change (((u : V) * ((u⁻¹ : Vˣ) : V) : V) : L) = ((1 : V) : L)
    rw [u.mul_inv]
  have hd0 : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have hmL := congrArg (fun z : V => (z : L)) hm
  simp only at hmL
  refine ⟨((a : V) : L), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L),
    key _ (m : Algebra.adjoin ℂ (s : Set V)).2, hd0, ?_, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((u⁻¹ : Vˣ) : V).2
  · rw [eq_div_iff hd0]
    simpa using hmL

end GlobalTheory
