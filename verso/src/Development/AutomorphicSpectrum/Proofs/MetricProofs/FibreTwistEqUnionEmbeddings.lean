import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use `⟨fun k => hu.1 (some k), fun f hf => ?_⟩` and prove the remaining obligations. Establish `hg : glue (basePart₂ u) (fun j => u ⟨none, j⟩) = u`. Use function extensionality and compare the values at `⟨o, i⟩`. Apply the tactic sequence `cases o <;> rfl`. Establish `h1` using `hu.2 (inc f) (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))`.

Establish `h2` using `eval_inc (basePart₂ u) (fun j => u ⟨none, j⟩) f`. Rewrite `h2` using `[hg]`. Rewrite using `[← h2]`. Conclude with `h1`.
-/
theorem oldPart_mem_mcPts {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : basePart₂ u ∈ mcPts Q := by
  refine ⟨fun k => hu.1 (some k), fun f hf => ?_⟩
  have hg : glue (basePart₂ u) (fun j => u ⟨none, j⟩) = u := by
    funext ⟨o, i⟩
    cases o <;> rfl
  have h1 := hu.2 (inc f) (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
  have h2 := eval_inc (basePart₂ u) (fun j => u ⟨none, j⟩) f
  rw [hg] at h2
  rw [← h2]
  exact h1

/- English proof (translation)
Take `⟨k0⟩` from `‹Nonempty K›`. Apply the tactic sequence `refine ⟨_, mcPts_smul hQ (fun k => if k = k0 then c else 1) (fun k => by by_cases h : k = k0 <;> simp [h, hc]) (oldPart_mem_mcPts hu), ?_⟩`. Use function extensionality and compare the values at `J`. Use `show ∏ o, u ⟨o, J o⟩ = (∏ k, (if k = k0 then c else 1) * basePart₂ u ⟨k, J (some k)⟩) * v (J none)`. Rewrite using `[Fintype.prod_option, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k0]`.

Establish `h1 : u ⟨none, J none⟩ = c * v (J none)` using `hv (J none)`. Rewrite using `[h1]`. Simplify using `only [Finset.mem_univ, if_true]`. Establish `h2 : ∀ k, basePart₂ u ⟨k, J (some k)⟩ = u ⟨some k, J (some k)⟩` using `fun _ => rfl`. Simplify using `only [h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_segre_eq_embL [Nonempty K] {p : ℕ} {Q : Ideal (MRing ι)} (hQ : IsMultiHomogIdeal Q)
    {u : (Σ o, Tb ι o) → ℂ} (hu : u ∈ mcPts (twist p Q)) {v : Fin 2 → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hv : ∀ j : Fin 2, u ⟨none, j⟩ = c * v j) :
    ∃ z ∈ mcPts Q, segre u = embL v (segre z) := by
  classical
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨_, mcPts_smul hQ (fun k => if k = k0 then c else 1)
    (fun k => by by_cases h : k = k0 <;> simp [h, hc]) (oldPart_mem_mcPts hu), ?_⟩
  funext J
  show ∏ o, u ⟨o, J o⟩ =
    (∏ k, (if k = k0 then c else 1) * basePart₂ u ⟨k, J (some k)⟩) * v (J none)
  rw [Fintype.prod_option, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k0]
  have h1 : u ⟨none, J none⟩ = c * v (J none) := hv (J none)
  rw [h1]
  simp only [Finset.mem_univ, if_true]
  have h2 : ∀ k, basePart₂ u ⟨k, J (some k)⟩ = u ⟨some k, J (some k)⟩ := fun _ => rfl
  simp only [h2]
  ring

/- English proof (translation)
Establish `hq : u ⟨none, (0 : Fin 2)⟩ ^ 2 + (p : ℂ) * u ⟨none, (1 : Fin 2)⟩ ^ 2 = 0`. Rewrite using `[← eval_quad]`. Conclude with `hu.2 _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hy : u ⟨none, (1 : Fin 2)⟩ ≠ 0`. Introduce `h0`.

Rewrite `hq` using `[h0]`. Establish `hx : u ⟨none, (0 : Fin 2)⟩ = 0` using `by simpa using hq`. Take `⟨i, hi⟩` from `hu.1 none`. Establish `hall : ∀ j : Fin 2, u ⟨none, j⟩ = 0`. Introduce `j`.

Use `fin_cases j`. Conclude with `hx`. Conclude with `h0`. Conclude with `hi (hall i)`. Use `⟨u ⟨none, (1 : Fin 2)⟩, hy, ?_⟩` and prove the remaining obligations.

Establish `hf : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) * (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) = 0`. Establish `: (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) * (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) = u ⟨none, (0 : Fin 2)⟩ ^ 2 - u ⟨none, (1 : Fin 2)⟩ ^ 2 * cRoot p ^ 2` using `by ring`. Rewrite using `[this, cRoot_sq, ← hq]`. Expand and normalize the polynomial expressions, which then agree. Break down `mul_eq_zero.mp hf with h | h` into its components or cases.

Use `left`. Introduce `j`. Use `fin_cases j`. Simplify `sub_eq_zero.mp h` using `[vPlus]`. Simplify using `[vPlus]`.

Use `right`. Introduce `j`. Use `fin_cases j`. Simplify `eq_neg_of_add_eq_zero_left h` using `[vMinus]`. Simplify using `[vMinus]`.
-/
theorem new_coords {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) :
    ∃ c : ℂ, c ≠ 0 ∧ ((∀ j : Fin 2, u ⟨none, j⟩ = c * vPlus p j) ∨
      (∀ j : Fin 2, u ⟨none, j⟩ = c * vMinus p j)) := by
  have hq : u ⟨none, (0 : Fin 2)⟩ ^ 2 + (p : ℂ) * u ⟨none, (1 : Fin 2)⟩ ^ 2 = 0 := by
    rw [← eval_quad]
    exact hu.2 _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hy : u ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
    intro h0
    rw [h0] at hq
    have hx : u ⟨none, (0 : Fin 2)⟩ = 0 := by simpa using hq
    obtain ⟨i, hi⟩ := hu.1 none
    have hall : ∀ j : Fin 2, u ⟨none, j⟩ = 0 := by
      intro j
      fin_cases j
      · exact hx
      · exact h0
    exact hi (hall i)
  refine ⟨u ⟨none, (1 : Fin 2)⟩, hy, ?_⟩
  have hf : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) *
      (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) = 0 := by
    have : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) *
      (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) =
        u ⟨none, (0 : Fin 2)⟩ ^ 2 - u ⟨none, (1 : Fin 2)⟩ ^ 2 * cRoot p ^ 2 := by ring
    rw [this, cRoot_sq, ← hq]
    ring
  rcases mul_eq_zero.mp hf with h | h
  · left
    intro j
    fin_cases j
    · simpa [vPlus] using sub_eq_zero.mp h
    · simp [vPlus]
  · right
    intro j
    fin_cases j
    · simpa [vMinus] using eq_neg_of_add_eq_zero_left h
    · simp [vMinus]

/- English proof (translation)
Introduce and unpack `_ ⟨w, ⟨z, hz, rfl, hΨ⟩, rfl⟩`. Conclude with `⟨glue z v, glue_mem_mcPts hz hv hv1, segre_glue z v, hΨ⟩`.
-/
theorem embL_image_subset {e : ℕ} {p : ℕ} {Q : Ideal (MRing ι)}
    {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 ≠ 0) :
    embL v '' fibre Q (pj v Ψ) y ⊆ fibre (twist p Q) Ψ y := by
  rintro _ ⟨w, ⟨z, hz, rfl, hΨ⟩, rfl⟩
  exact ⟨glue z v, glue_mem_mcPts hz hv hv1, segre_glue z v, hΨ⟩

/- English proof (translation)
Introduce `K _ ι _ p Q e Ψ y _ hK hQ`. Use `Set.Subset.antisymm ?_ (Set.union_subset (embL_image_subset (vPlus_root p) (by simp [vPlus])) (embL_image_subset (vMinus_root p) (by simp [vMinus])))` and prove the remaining obligations. Introduce and unpack `w ⟨u, hu, rfl, hΨ⟩`. Take `⟨c, hc, h | h⟩` from `new_coords hu`. Take `⟨z, hz, hs⟩` from `exists_segre_eq_embL hQ hu hc h`.

Use `Or.inl ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩` and prove the remaining obligations. Use `show Ψ (embL (vPlus p) (segre z)) = _`. Rewrite using `[← hs]`. Conclude with `hΨ`. Take `⟨z, hz, hs⟩` from `exists_segre_eq_embL hQ hu hc h`.

Use `Or.inr ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩` and prove the remaining obligations. Use `show Ψ (embL (vMinus p) (segre z)) = _`. Rewrite using `[← hs]`. Conclude with `hΨ`.
-/
theorem fibre_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (Q : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ),
    p ≠ 0 → Nonempty K → IsMultiHomogIdeal Q →
    fibre (twist p Q) Ψ y =
      embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y ∪
        embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y := by
  intro K _ ι _ p Q e Ψ y _ hK hQ
  refine Set.Subset.antisymm ?_ (Set.union_subset
    (embL_image_subset (vPlus_root p) (by simp [vPlus]))
    (embL_image_subset (vMinus_root p) (by simp [vMinus])))
  rintro w ⟨u, hu, rfl, hΨ⟩
  obtain ⟨c, hc, h | h⟩ := new_coords hu
  · obtain ⟨z, hz, hs⟩ := exists_segre_eq_embL hQ hu hc h
    refine Or.inl ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩
    show Ψ (embL (vPlus p) (segre z)) = _
    rw [← hs]
    exact hΨ
  · obtain ⟨z, hz, hs⟩ := exists_segre_eq_embL hQ hu hc h
    refine Or.inr ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩
    show Ψ (embL (vMinus p) (segre z)) = _
    rw [← hs]
    exact hΨ

end GlobalTheory.CompanionTheory.Ar.Tw.Fib
