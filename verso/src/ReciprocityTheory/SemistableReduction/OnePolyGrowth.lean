import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
import Lemmata.IterateZero.IterZero

namespace ReciprocityTheory.MultiplicativeHeights

open Filter Topology Function Metric Polynomial

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.IterateZero.goal1 .. | (apply Bl.IterateZero.goal1 <;> assumption) | (intros; apply Bl.IterateZero.goal1 <;> assumption)`.
-/
theorem entire_poly_of_growth (k : ℕ) : ∀ (g : ℂ → ℂ) (A : ℝ), Differentiable ℂ g →
    (∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t, g t = P.eval t := by
  first | exact Bl.IterateZero.goal1 .. | (apply Bl.IterateZero.goal1 <;> assumption) | (intros; apply Bl.IterateZero.goal1 <;> assumption)

/- English proof (translation)
Set `g : ℂ → ℂ` to `fun t => if t ∈ B then limUnder (𝓝[≠] t) f else f t`. Use `⟨g, fun c => ?_, fun t ht => if_neg ht⟩` and prove the remaining obligations. Distinguish the cases in `hc : c ∈ B`. Establish `hU : IsOpen (B \ {c})ᶜ` using `(hB.sdiff).isClosed.isOpen_compl set s : Set ℂ := (B \ {c})ᶜ ∩ ball c 1 with hs`. Establish `hsn : s ∈ 𝓝 c` using `inter_mem (hU.mem_nhds (fun h => h.2 rfl)) (ball_mem_nhds c one_pos)`.

Establish `hsub : s \ {c} ⊆ Bᶜ`. Introduce and unpack `t ⟨⟨h1, -⟩, h2⟩ htB`. Conclude with `h1 ⟨htB, h2⟩`. Establish `hbdd : BddAbove (norm ∘ f '' (s \ {c}))`. Use `⟨|A| * (2 + ‖c‖) ^ k, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨t, ht, rfl⟩`. Establish `htc : ‖t‖ ≤ ‖c‖ + 1`. Establish `h` using `ht.1.2`. Rewrite `h` using `[mem_ball, dist_eq_norm]`. Use `norm_le_norm_add_norm_sub' t c` as an intermediate fact.

Combine the linear relations using `[norm_sub_rev t c]`. Combine the equalities or inequalities in the displayed calculation. Establish `hdiff` using `Complex.differentiableOn_update_limUnder_of_bddAbove hsn (hf.mono hsub) hbdd`. Use `(hdiff.differentiableAt hsn).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hsn] with t ht`.

Distinguish the cases in `htc : t = c`. Substitute `htc` using the available equality. Simplify using `[g, hc]`. Establish `htB : t ∉ B` using `fun h => ht.1 ⟨h, htc⟩`. Simplify using `[g, htB, update_of_ne htc]`.

Establish `hO : IsOpen Bᶜ` using `hB.isClosed.isOpen_compl`. Use `(hf.differentiableAt (hO.mem_nhds hc)).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hO.mem_nhds hc] with t ht`. Conclude with `if_neg ht`.
-/
theorem exists_entire_of_finite_growth (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ) (hB : B.Finite)
    (hf : DifferentiableOn ℂ f Bᶜ) (hb : ∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ t ∉ B, g t = f t := by
  classical
  let g : ℂ → ℂ := fun t => if t ∈ B then limUnder (𝓝[≠] t) f else f t
  refine ⟨g, fun c => ?_, fun t ht => if_neg ht⟩
  by_cases hc : c ∈ B
  · have hU : IsOpen (B \ {c})ᶜ := (hB.sdiff).isClosed.isOpen_compl
    set s : Set ℂ := (B \ {c})ᶜ ∩ ball c 1 with hs
    have hsn : s ∈ 𝓝 c := inter_mem (hU.mem_nhds (fun h => h.2 rfl)) (ball_mem_nhds c one_pos)
    have hsub : s \ {c} ⊆ Bᶜ := by
      rintro t ⟨⟨h1, -⟩, h2⟩ htB
      exact h1 ⟨htB, h2⟩
    have hbdd : BddAbove (norm ∘ f '' (s \ {c})) := by
      refine ⟨|A| * (2 + ‖c‖) ^ k, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have htc : ‖t‖ ≤ ‖c‖ + 1 := by
        have h := ht.1.2
        rw [mem_ball, dist_eq_norm] at h
        have := norm_le_norm_add_norm_sub' t c
        linarith [norm_sub_rev t c]
      calc ‖f t‖ ≤ A * (1 + ‖t‖) ^ k := hb t (hsub ht)
        _ ≤ |A| * (1 + ‖t‖) ^ k := mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ |A| * (2 + ‖c‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k)
              (abs_nonneg A)
    have hdiff := Complex.differentiableOn_update_limUnder_of_bddAbove hsn
      (hf.mono hsub) hbdd
    refine (hdiff.differentiableAt hsn).congr_of_eventuallyEq ?_
    filter_upwards [hsn] with t ht
    by_cases htc : t = c
    · subst htc
      simp [g, hc]
    · have htB : t ∉ B := fun h => ht.1 ⟨h, htc⟩
      simp [g, htB, update_of_ne htc]
  · have hO : IsOpen Bᶜ := hB.isClosed.isOpen_compl
    refine (hf.differentiableAt (hO.mem_nhds hc)).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hc] with t ht
    exact if_neg ht

/- English proof (translation)
Introduce `f B A k hB hf hb`. Take `⟨g, hg, hgf⟩` from `exists_entire_of_finite_growth f B A k hB hf hb`. Establish `hclosed : IsClosed {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k}` using `isClosed_le (continuous_norm.comp hg.continuous) (continuous_const.mul ((continuous_const.add continuous_norm).pow k))`. Establish `hsub : Bᶜ ⊆ {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k}` using `fun t ht => by`. Simplify `hb t ht` using `[hgf t ht]`.

Establish `hall : ∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k`. Establish `hd : Dense Bᶜ` using `hB.countable.dense_compl ℂ`. Introduce `t`. Establish `: t ∈ closure Bᶜ` using `by rw [hd.closure_eq]; trivial`. Conclude with `closure_minimal hsub hclosed this`.

Take `⟨P, hPd, hP⟩` from `entire_poly_of_growth k g A hg hall`. Conclude with `⟨P, hPd, fun t ht => by rw [← hgf t ht, hP t]⟩`.
-/
theorem onePolyGrowth_holds : OnePolyGrowthStatement := by
  intro f B A k hB hf hb
  obtain ⟨g, hg, hgf⟩ := exists_entire_of_finite_growth f B A k hB hf hb
  have hclosed : IsClosed {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} :=
    isClosed_le (continuous_norm.comp hg.continuous)
      (continuous_const.mul ((continuous_const.add continuous_norm).pow k))
  have hsub : Bᶜ ⊆ {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} := fun t ht => by
    simpa [hgf t ht] using hb t ht
  have hall : ∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k := by
    have hd : Dense Bᶜ := hB.countable.dense_compl ℂ
    intro t
    have : t ∈ closure Bᶜ := by rw [hd.closure_eq]; trivial
    exact closure_minimal hsub hclosed this
  obtain ⟨P, hPd, hP⟩ := entire_poly_of_growth k g A hg hall
  exact ⟨P, hPd, fun t ht => by rw [← hgf t ht, hP t]⟩

end ReciprocityTheory.MultiplicativeHeights
