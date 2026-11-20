import Mathlib

open MvPolynomial Filter Topology

/- English proof (translation)
Unfold `esymm`. Use `IsHomogeneous.sum _ _ _ (fun s hs => ?_)` and prove the remaining obligations. Establish `h` using `IsHomogeneous.prod s (fun i => (X i : MvPolynomial (Fin n) ℂ)) (fun _ => 1) (fun i _ => isHomogeneous_X ℂ i)`. Rewrite `hs` using `[Finset.mem_powersetCard]`. Simplify `h` using `[hs.2]`.
-/
private theorem gt_esymm_hom (n j : ℕ) : (esymm (Fin n) ℂ j).IsHomogeneous j := by
  unfold esymm
  refine IsHomogeneous.sum _ _ _ (fun s hs => ?_)
  have h := IsHomogeneous.prod s (fun i => (X i : MvPolynomial (Fin n) ℂ)) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℂ i)
  rw [Finset.mem_powersetCard] at hs
  simpa [hs.2] using h

/- English proof (translation)
Rewrite using `[aeval_monomial, Finsupp.prod]`. Establish `h` using `IsHomogeneous.prod α.support (fun i => f i ^ α i) (fun i => w i * α i) (fun i _ => (hf i).pow (α i))`. Establish `h0 : (algebraMap ℂ (MvPolynomial ρ ℂ) c).IsHomogeneous 0` using `isHomogeneous_C ρ c`. Simplify using `using h0.mul h`.
-/
private theorem gt_mono_hom {σ ρ : Type} (f : σ → MvPolynomial ρ ℂ) (w : σ → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (w i)) (α : σ →₀ ℕ) (c : ℂ) :
    (aeval f (monomial α c)).IsHomogeneous (∑ i ∈ α.support, w i * α i) := by
  rw [aeval_monomial, Finsupp.prod]
  have h := IsHomogeneous.prod α.support (fun i => f i ^ α i) (fun i => w i * α i)
    (fun i _ => (hf i).pow (α i))
  have h0 : (algebraMap ℂ (MvPolynomial ρ ℂ) c).IsHomogeneous 0 := isHomogeneous_C ρ c
  simpa using h0.mul h

/- English proof (translation)
Use `set W : (σ →₀ ℕ) → ℕ := fun α => ∑ i ∈ α.support, w i * α i with hW`. Use `set S := G.support.filter (fun α => W α ≤ k) with hS`. Establish `hc : ∀ β, (∑ α ∈ S, monomial α (G.coeff α)).coeff β = if β ∈ S then G.coeff β else 0`. Introduce `β`. Rewrite using `[coeff_sum]`.

Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Establish `hsupp : (∑ α ∈ S, monomial α (G.coeff α)).support ⊆ S`. Introduce `β hβ`. Rewrite `hβ` using `[mem_support_iff, hc]`.

Assume the negation of the conclusion as `h`. Conclude with `hβ (if_neg h)`. Use `⟨∑ α ∈ S, monomial α (G.coeff α), ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Distinguish the cases in `hm : m.degree ≤ k`.

Use `conv_rhs => rw [G.as_sum]`. Rewrite using `[map_sum, map_sum, coeff_sum, coeff_sum]`. Use `Finset.sum_subset (Finset.filter_subset _ _) (fun α hα hα' => ?_)` and prove the remaining obligations. Use `(gt_mono_hom f w hf α _).coeff_eq_zero ?_` and prove the remaining obligations. Introduce `h`.

Apply `hα'` to reduce the goal to its premises. Rewrite using `[hS, Finset.mem_filter]`. Conclude with `⟨hα, by simp only [hW]; omega⟩`. Establish `h1 : (aeval f G).coeff m = 0`. Apply `coeff_eq_zero_of_totalDegree_lt` to reduce the goal to its premises.

Establish `: m.degree = ∑ i ∈ m.support, m i` using `rfl`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h1, map_sum, coeff_sum]`. Use `Finset.sum_eq_zero (fun α hα => ?_)` and prove the remaining obligations. Use `(gt_mono_hom f w hf α _).coeff_eq_zero ?_` and prove the remaining obligations.

Introduce `h`. Rewrite `hα` using `[hS, Finset.mem_filter]`. Use `hα.2` as an intermediate fact. Simplify using `only [hW] at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[totalDegree, Finset.sup_le_iff]`. Introduce `α hα`. Establish `h` using `hsupp hα`. Rewrite `h` using `[hS, Finset.mem_filter]`. Use `le_trans ?_ h.2` and prove the remaining obligations.

Conclude with `Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_left _ (hw i))`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum (fun α hα => ?_)` and prove the remaining obligations. Rewrite using `[hc, if_pos (hsupp hα)]`. Use `_ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (hsupp.trans (Finset.filter_subset _ _)) (fun _ _ _ => norm_nonneg _)`.
-/
private theorem gt_gen {σ ρ : Type} [DecidableEq σ] (f : σ → MvPolynomial ρ ℂ) (w : σ → ℕ)
    (hw : ∀ i, 1 ≤ w i) (hf : ∀ i, (f i).IsHomogeneous (w i)) (k : ℕ) (G : MvPolynomial σ ℂ)
    (hG : (aeval f G).totalDegree ≤ k) :
    ∃ G' : MvPolynomial σ ℂ, aeval f G' = aeval f G ∧ G'.totalDegree ≤ k ∧
      (∑ α ∈ G'.support, ‖G'.coeff α‖) ≤ (∑ α ∈ G.support, ‖G.coeff α‖) := by
  classical
  set W : (σ →₀ ℕ) → ℕ := fun α => ∑ i ∈ α.support, w i * α i with hW
  set S := G.support.filter (fun α => W α ≤ k) with hS
  have hc : ∀ β, (∑ α ∈ S, monomial α (G.coeff α)).coeff β = if β ∈ S then G.coeff β else 0 := by
    intro β
    rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hsupp : (∑ α ∈ S, monomial α (G.coeff α)).support ⊆ S := by
    intro β hβ
    rw [mem_support_iff, hc] at hβ
    by_contra h
    exact hβ (if_neg h)
  refine ⟨∑ α ∈ S, monomial α (G.coeff α), ?_, ?_, ?_⟩
  · ext m
    by_cases hm : m.degree ≤ k
    · conv_rhs => rw [G.as_sum]
      rw [map_sum, map_sum, coeff_sum, coeff_sum]
      refine Finset.sum_subset (Finset.filter_subset _ _) (fun α hα hα' => ?_)
      refine (gt_mono_hom f w hf α _).coeff_eq_zero ?_
      intro h
      apply hα'
      rw [hS, Finset.mem_filter]
      exact ⟨hα, by simp only [hW]; omega⟩
    · have h1 : (aeval f G).coeff m = 0 := by
        apply coeff_eq_zero_of_totalDegree_lt
        have : m.degree = ∑ i ∈ m.support, m i := rfl
        omega
      rw [h1, map_sum, coeff_sum]
      refine Finset.sum_eq_zero (fun α hα => ?_)
      refine (gt_mono_hom f w hf α _).coeff_eq_zero ?_
      intro h
      rw [hS, Finset.mem_filter] at hα
      have := hα.2
      simp only [hW] at this
      omega
  · rw [totalDegree, Finset.sup_le_iff]
    intro α hα
    have h := hsupp hα
    rw [hS, Finset.mem_filter] at h
    refine le_trans ?_ h.2
    exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_left _ (hw i))
  · calc _ ≤ ∑ α ∈ (∑ α ∈ S, monomial α (G.coeff α)).support, ‖G.coeff α‖ := by
          refine Finset.sum_le_sum (fun α hα => ?_)
          rw [hc, if_pos (hsupp hα)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (hsupp.trans (Finset.filter_subset _ _)) (fun _ _ _ => norm_nonneg _)

/- English proof (translation)
Introduce `τ _ _ n k G hG`. Conclude with `gt_gen _ (fun ti : τ × Fin n => (ti.2 : ℕ) + 1) (fun _ => Nat.le_add_left _ _) (fun ti => (gt_esymm_hom n _).rename_isHomogeneous) k G hG`.
-/
theorem UpperTheory.ConvolutionTheory.FX.gen_trunc :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n k : ℕ) (G : MvPolynomial (τ × Fin n) ℂ), (aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))) G).totalDegree ≤ k → ∃ G' : MvPolynomial (τ × Fin n) ℂ, aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))) G' = aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))) G ∧ G'.totalDegree ≤ k ∧ (∑ α ∈ (G').support, ‖(G').coeff α‖) ≤ (∑ α ∈ (G).support, ‖(G).coeff α‖) := by
  intro τ _ _ n k G hG
  exact gt_gen _ (fun ti : τ × Fin n => (ti.2 : ℕ) + 1) (fun _ => Nat.le_add_left _ _)
    (fun ti => (gt_esymm_hom n _).rename_isHomogeneous) k G hG
