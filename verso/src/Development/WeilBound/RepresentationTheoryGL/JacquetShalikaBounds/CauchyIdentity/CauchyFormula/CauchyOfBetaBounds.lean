import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

noncomputable section

open Finset GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace PositivityTheory.RgJS

namespace CauchyPositivity

/- English proof (translation)
Establish `hg : Continuous (fun δ : ℝ => x * max A δ * max B δ)` using `by fun_prop`. Establish `h0 : x * max A 0 * max B 0 < 1`. Break down `le_total A 0 with hA | hA` into its components or cases. Rewrite using `[max_eq_right hA]`. Simplify using the standard rewrite rules.

Break down `le_total B 0 with hB | hB` into its components or cases. Rewrite using `[max_eq_right hB]`. Simplify using the standard rewrite rules. Rewrite using `[max_eq_left hA, max_eq_left hB]`. Conclude with `h`.

Establish `hn : ∀ᶠ δ in nhds (0:ℝ), x * max A δ * max B δ < 1` using `(hg.tendsto 0).eventually (gt_mem_nhds h0)`. Establish `hev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), x * max A δ * max B δ < 1 ∧ δ ∈ Set.Ioi (0:ℝ)` using `(Filter.Eventually.filter_mono nhdsWithin_le_nhds hn).and self_mem_nhdsWithin`. Take `⟨δ, h1, h2⟩` from `hev.exists`. Conclude with `⟨δ, h2, h1⟩`.
-/
theorem exists_pos (A B x : ℝ) (hx : 0 ≤ x) (h : x * A * B < 1) :
    ∃ δ : ℝ, 0 < δ ∧ x * max A δ * max B δ < 1 := by
  have hg : Continuous (fun δ : ℝ => x * max A δ * max B δ) := by fun_prop
  have h0 : x * max A 0 * max B 0 < 1 := by
    rcases le_total A 0 with hA | hA
    · rw [max_eq_right hA]; simp
    rcases le_total B 0 with hB | hB
    · rw [max_eq_right hB]; simp
    rw [max_eq_left hA, max_eq_left hB]; exact h
  have hn : ∀ᶠ δ in nhds (0:ℝ), x * max A δ * max B δ < 1 :=
    (hg.tendsto 0).eventually (gt_mem_nhds h0)
  have hev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), x * max A δ * max B δ < 1 ∧ δ ∈ Set.Ioi (0:ℝ) :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds hn).and self_mem_nhdsWithin
  obtain ⟨δ, h1, h2⟩ := hev.exists
  exact ⟨δ, h2, h1⟩

end CauchyPositivity

open CauchyPositivity in
/- English proof (translation)
Introduce `hBeta hSum hSchur hPad m m' hmm α β X A B hA hB hX`. Take `⟨δ, hδ, hlt⟩` from `exists_pos A B ‖X‖ (norm_nonneg X) hX`. Establish `hA'pos : 0 < max A δ` using `lt_of_lt_of_le hδ (le_max_right _ _)`. Establish `hB'pos : 0 < max B δ` using `lt_of_lt_of_le hδ (le_max_right _ _)`. Establish `hαb : ∀ i, ‖((α i : ℂ))‖ ≤ max A δ` using `fun i => (hA i).trans (le_max_left _ _)`.

Establish `hβb : ∀ j, ‖((β j : ℂ))‖ ≤ max B δ` using `fun j => (hB j).trans (le_max_left _ _)`. Establish `hH` using `hBeta m m' (fun i => (α i : ℂ)) β X (max A δ) (max B δ) hA'pos hB'pos hαb hβb hlt`. Establish `e` using `fun l : Fin m' → ℕ => (hSchur m α (padN m l)).trans (hPad m m' hmm _ l)`. Simplify using `only [e]`. Take `⟨hsum, hbdα⟩` from `hSum m m' (max A δ) (max B δ) ‖X‖ hA'pos hB'pos (norm_nonneg _) hlt`.

Establish `hbdβ` using `(hSum m' m' (max B δ) (max B δ) 0 hB'pos hB'pos le_rfl (by simp)).2`. Use `⟨hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_), hH⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, norm_pow, hSchur m' β]`. Establish `h1` using `hbdα (fun i => (α i : ℂ)) hαb l`. Establish `h2` using `hbdβ (fun j => (β j : ℂ)) hβb l`.

Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)) (pow_nonneg (norm_nonneg _) _)`.
-/
theorem cauchy_of_beta_bounds : BetaAll → SumBd → SchurJT → JTPad → Cauchy := by
  intro hBeta hSum hSchur hPad m m' hmm α β X A B hA hB hX
  obtain ⟨δ, hδ, hlt⟩ := exists_pos A B ‖X‖ (norm_nonneg X) hX
  have hA'pos : 0 < max A δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hB'pos : 0 < max B δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hαb : ∀ i, ‖((α i : ℂ))‖ ≤ max A δ := fun i => (hA i).trans (le_max_left _ _)
  have hβb : ∀ j, ‖((β j : ℂ))‖ ≤ max B δ := fun j => (hB j).trans (le_max_left _ _)
  have hH := hBeta m m' (fun i => (α i : ℂ)) β X (max A δ) (max B δ) hA'pos hB'pos hαb hβb hlt
  have e := fun l : Fin m' → ℕ => (hSchur m α (padN m l)).trans (hPad m m' hmm _ l)
  simp only [e]
  obtain ⟨hsum, hbdα⟩ := hSum m m' (max A δ) (max B δ) ‖X‖ hA'pos hB'pos (norm_nonneg _) hlt
  have hbdβ := (hSum m' m' (max B δ) (max B δ) 0 hB'pos hB'pos le_rfl (by simp)).2
  refine ⟨hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_), hH⟩
  rw [norm_mul, norm_mul, norm_pow, hSchur m' β]
  have h1 := hbdα (fun i => (α i : ℂ)) hαb l
  have h2 := hbdβ (fun j => (β j : ℂ)) hβb l
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
    (pow_nonneg (norm_nonneg _) _)

end PositivityTheory.RgJS
