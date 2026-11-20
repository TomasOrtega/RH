import Formalism.TruncatedSeriesCounting.PowMemSpanOfMemSpanLinearDistinguished
import Formalism.WindowSums.PowerSeriesRelationList

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

open Finset

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i hi`. Take `⟨k, hk⟩` from `hS i hi`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_filter]`.
-/
private lemma sum_le_sum_cover {K : ℕ} (W : Fin K → Finset ℤ) (S : Finset ℤ)
    (hS : ∀ i ∈ S, ∃ k, i ∈ W k) (g : ℤ → ℕ) :
    ∑ i ∈ S, g i ≤ ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
  calc ∑ i ∈ S, g i ≤ ∑ i ∈ S, ∑ k, if i ∈ W k then g i else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨k, hk⟩ := hS i hi
        calc g i = (fun k' => if i ∈ W k' then g i else 0) k := by simp [hk]
          _ ≤ ∑ k', if i ∈ W k' then g i else 0 :=
            Finset.single_le_sum (f := fun k' => if i ∈ W k' then g i else 0) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
    _ = ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter]

/- English proof (translation)
Introduce `ℓ _ hℓ χ hχ ell K D a L JJ hJJ hD`. Take `⟨hne, hv⟩` from `Formalism.WindowSums.arc_KillerVal ℓ hℓ χ hχ ell JJ`. Use `⟨hne, ?_⟩` and prove the remaining obligations. Rewrite using `[hv]`. Use `set S := JJ.erase 0 with hSdef`.

Use `set W : Fin K → Finset ℤ := fun k => Finset.Ico (a k) (a k + (L k : ℤ)) with hWdef`. Establish `hcov : ∀ i ∈ S, ∃ k, i ∈ W k`. Introduce `i hi`. Use `hJJ (Finset.mem_of_mem_erase hi)` as an intermediate fact. Simplify `this` using `[Finset.mem_biUnion, hWdef]`.

Establish `hcard : S.card ≤ ∑ k, L k`. Establish `h` using `sum_le_sum_cover W S hcov (fun _ => 1)`. Rewrite using `[Finset.card_eq_sum_ones]`. Use `h.trans (Finset.sum_le_sum fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.card_eq_sum_ones]`.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `i hi`. Conclude with `(Finset.mem_filter.mp hi).2`. Use `_ = L k := by simp [hWdef]`.

Establish `hsumv : ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) ≤ ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `sum_le_sum_cover W S hcov (fun i => padicValInt ℓ i)` after adjusting the coercions. Use `_ = ∑ k, ((∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by push_cast; rfl`. Use `_ ≤ ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D) := by`.

Use `Finset.sum_le_sum fun k _ => ?_` and prove the remaining obligations. Use `Formalism.WindowSums.arc_WindowSum ℓ (a k) (L k) D _ ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Conclude with `(Finset.mem_filter.mp hi).2`. Introduce `h0`.

Use `(Finset.mem_filter.mp h0).1` as an intermediate fact. Simplify using `[hSdef] at this`. Introduce `i hi`. Conclude with `hD i (Finset.mem_of_mem_erase (Finset.mem_filter.mp hi).1)`. Establish `hsplit : ∑ i ∈ S, (1 + ell + padicValInt ℓ i) = S.card * (1 + ell) + ∑ i ∈ S, padicValInt ℓ i`.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]`. Rewrite using `[hsplit]`. Establish `hcardR : (S.card : ℝ) ≤ ((∑ k, L k : ℕ) : ℝ)` using `by exact_mod_cast hcard`. Establish `hmul : (S.card : ℝ) * (1 + ell) ≤ ((∑ k, L k : ℕ) : ℝ) * (1 + ell)` using `mul_le_mul_of_nonneg_right hcardR (by positivity)`. Establish `hgoal : ((S.card * (1 + ell) + ∑ i ∈ S, padicValInt ℓ i + ell : ℕ) : ℝ) = (S.card : ℝ) * (1 + ell) + ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) + ell` using `by push_cast; ring`.

Rewrite using `[hgoal]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kappa_window_bound : KapWin := by
  intro ℓ _ hℓ χ hχ ell K D a L JJ hJJ hD
  obtain ⟨hne, hv⟩ := Formalism.WindowSums.arc_KillerVal ℓ hℓ χ hχ ell JJ
  refine ⟨hne, ?_⟩
  rw [hv]
  set S := JJ.erase 0 with hSdef
  set W : Fin K → Finset ℤ := fun k => Finset.Ico (a k) (a k + (L k : ℤ)) with hWdef
  have hcov : ∀ i ∈ S, ∃ k, i ∈ W k := by
    intro i hi
    have := hJJ (Finset.mem_of_mem_erase hi)
    simpa [Finset.mem_biUnion, hWdef] using this
  have hcard : S.card ≤ ∑ k, L k := by
    have h := sum_le_sum_cover W S hcov (fun _ => 1)
    rw [Finset.card_eq_sum_ones]
    refine h.trans (Finset.sum_le_sum fun k _ => ?_)
    rw [← Finset.card_eq_sum_ones]
    calc (S.filter (fun i => i ∈ W k)).card ≤ (W k).card := by
          apply Finset.card_le_card
          intro i hi
          exact (Finset.mem_filter.mp hi).2
      _ = L k := by simp [hWdef]
  have hsumv : ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) ≤
      ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D) := by
    calc ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ)
        ≤ ((∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by
          exact_mod_cast sum_le_sum_cover W S hcov (fun i => padicValInt ℓ i)
      _ = ∑ k, ((∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D) := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine Formalism.WindowSums.arc_WindowSum ℓ (a k) (L k) D _ ?_ ?_ ?_
          · intro i hi
            exact (Finset.mem_filter.mp hi).2
          · intro h0
            have := (Finset.mem_filter.mp h0).1
            simp [hSdef] at this
          · intro i hi
            exact hD i (Finset.mem_of_mem_erase (Finset.mem_filter.mp hi).1)
  have hsplit : ∑ i ∈ S, (1 + ell + padicValInt ℓ i) =
      S.card * (1 + ell) + ∑ i ∈ S, padicValInt ℓ i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  rw [hsplit]
  have hcardR : (S.card : ℝ) ≤ ((∑ k, L k : ℕ) : ℝ) := by exact_mod_cast hcard
  have hmul : (S.card : ℝ) * (1 + ell) ≤ ((∑ k, L k : ℕ) : ℝ) * (1 + ell) :=
    mul_le_mul_of_nonneg_right hcardR (by positivity)
  have hgoal : ((S.card * (1 + ell) + ∑ i ∈ S, padicValInt ℓ i + ell : ℕ) : ℝ) =
      (S.card : ℝ) * (1 + ell) + ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) + ell := by
    push_cast; ring
  rw [hgoal]
  linarith

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
