import Formalism.PieriBlockIdeals.FactorialValuationSum
import Formalism.PieriBlockIdeals.PieriColumnMinors.LabelSumNeedsLeFalse
import Formalism.PieriBlockIdeals.PieriColumnMinors.DividedPowerZeroZeroVector
import Formalism.PieriBlockIdeals.PieriColumnMinors.LastGradedImpliesOneBlock

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Formalism.CohomologicalDescent.UnitNormBounds

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

/- English proof (translation)
Establish `h1` using `Fin.val_rev b`. Establish `h2` using `hb (Fin.rev b)`. Establish `h3` using `b.isLt`. Unfold `U dual`. Use linear arithmetic over natural numbers and integers.
-/
theorem rowStart_rev_eq (k j t w M : ℕ) (lam : Fin (k + j) → ℕ) (hb : ∀ a, w ≤ lam a ∧ lam a ≤ M)
    (b : Fin (k + j)) :
    U k j t lam (Fin.rev b) = (M : ℤ) - (dual M lam b : ℤ) + (t : ℤ) + (b.val : ℤ) := by
  have h1 := Fin.val_rev b
  have h2 := hb (Fin.rev b)
  have h3 := b.isLt
  unfold U dual
  omega

/- English proof (translation)
Unfold `cont maxB`. Use linear arithmetic over natural numbers and integers.
-/
theorem content_label_eq (t w M : ℕ) (hwM : w ≤ M) (ct : ℤ) : cont t w M ct = (M : ℤ) - ct + (t : ℤ) - 1 := by
  unfold cont maxB
  omega

/- English proof (translation)
Introduce `k j t w M i lam hb tau htau b col h1 h2`. Establish `hU` using `rowStart_rev_eq k j t w M lam hb b`. Establish `hw` using `hb (Fin.rev b)`. Establish `hd : dual M lam b = M - lam (Fin.rev b)` using `rfl`. Take `⟨_, _, _, _, hbox⟩` from `Finset.mem_filter.mp htau`.

Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hcon`. Unfold `boxesOfContent at hbox`. Rewrite `hbox` using `[Finset.card_eq_zero]`. Establish `hmem : b ∈ Finset.univ.filter fun a : Fin (k + j) => (dual M lam a : ℤ) ≤ ((M - w : ℕ) : ℤ) + (a.val : ℤ) ∧ ((M - w : ℕ) : ℤ) + (a.val : ℤ) < (tau a : ℤ)`.

Use `Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers. Unfold `label maxB at hcon`. Use linear arithmetic over natural numbers and integers. Rewrite `hmem` using `[hbox]`.

Conclude with `absurd hmem (Finset.notMem_empty _)`. Unfold `label`. Use linear arithmetic over natural numbers and integers.
-/
theorem good_labels_holds : GoodLabels := by
  intro k j t w M i lam hb tau htau b col h1 h2
  have hU := rowStart_rev_eq k j t w M lam hb b
  have hw := hb (Fin.rev b)
  have hd : dual M lam b = M - lam (Fin.rev b) := rfl
  obtain ⟨_, _, _, _, hbox⟩ := Finset.mem_filter.mp htau
  constructor
  · by_contra hcon
    unfold boxesOfContent at hbox
    rw [Finset.card_eq_zero] at hbox
    have hmem : b ∈ Finset.univ.filter fun a : Fin (k + j) =>
        (dual M lam a : ℤ) ≤ ((M - w : ℕ) : ℤ) + (a.val : ℤ) ∧
          ((M - w : ℕ) : ℤ) + (a.val : ℤ) < (tau a : ℤ) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · omega
      · unfold label maxB at hcon
        omega
    rw [hbox] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · unfold label
    omega

/- English proof (translation)
Establish `h` using `Finset.card_le_card_of_injOn (s := Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧ p b) (t := Finset.range k) (fun b => (Fin.rev b).val) (by`. Introduce `b hb`. Use `(Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.1` as an intermediate fact. Conclude with `Finset.mem_coe.mpr (Finset.mem_range.mpr this))`. Use the proof step `(by`.

Introduce `a _ b _ hab`. Conclude with `Fin.rev_injective (Fin.ext hab))`. Simplify using `using h`.
-/
theorem card_filter_rev_lt_le (k j : ℕ) (p : Fin (k + j) → Prop) [DecidablePred p] :
    (Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧ p b).card ≤ k := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧ p b)
    (t := Finset.range k) (fun b => (Fin.rev b).val)
    (by
      intro b hb
      have := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.1
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr this))
    (by
      intro a _ b _ hab
      exact Fin.rev_injective (Fin.ext hab))
  simpa using h

/- English proof (translation)
Establish `h` using `Finset.card_le_card_of_injOn (s := Finset.univ.filter fun b : Fin (k + j) => ¬ (Fin.rev b).val < k ∧ p b) (t := Finset.range j) (fun b => b.val) (by`. Introduce `b hb`. Establish `h1` using `(Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.1`. Establish `h2` using `Fin.val_rev b`. Establish `h3` using `b.isLt`.

Conclude with `Finset.mem_coe.mpr (Finset.mem_range.mpr (by show b.val < j; omega)))`. Use the proof step `(by`. Introduce `a _ b _ hab`. Conclude with `Fin.ext hab)`. Simplify using `using h`.
-/
theorem card_filter_not_rev_lt_le (k j : ℕ) (p : Fin (k + j) → Prop) [DecidablePred p] :
    (Finset.univ.filter fun b : Fin (k + j) => ¬ (Fin.rev b).val < k ∧ p b).card ≤ j := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun b : Fin (k + j) => ¬ (Fin.rev b).val < k ∧ p b)
    (t := Finset.range j) (fun b => b.val)
    (by
      intro b hb
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.1
      have h2 := Fin.val_rev b
      have h3 := b.isLt
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by show b.val < j; omega)))
    (by
      intro a _ b _ hab
      exact Fin.ext hab)
  simpa using h

/- English proof (translation)
Introduce `k j t w M i lam xm xp hR tau _ ct`. Establish `hb : ∀ a, w ≤ lam a ∧ lam a ≤ M` using `fun a => ⟨hR.low a, hR.high a⟩`. Unfold `boxesOfLabel boxesOfContent cloudBoxes`. Rewrite using `[← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun a : Fin (k + j) => (dual M lam a : ℤ) ≤ cont t w M ct + (a.val : ℤ) ∧ cont t w M ct + (a.val : ℤ) < (tau a : ℤ)) (fun b : Fin (k + j) => (Fin.rev b).val < k), add_comm]`. Rewrite using `[Finset.filter_filter, Finset.filter_filter]`.

Use `Nat.add_le_add ?_ (le_of_eq ?_)` and prove the remaining obligations. Use `split_ifs with hct`. Use `le_trans (le_of_eq ?_) (card_filter_not_rev_lt_le k j (fun a : Fin (k + j) => (dual M lam a : ℤ) ≤ cont t w M ct + (a.val : ℤ) ∧ cont t w M ct + (a.val : ℤ) < (tau a : ℤ)))` and prove the remaining obligations. Use `congr 1`. Use extensionality with `b`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. The claim follows by propositional logic. Rewrite using `[Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce and unpack `b _ ⟨⟨h1, _⟩, h3⟩`. Establish `hU` using `rowStart_rev_eq k j t w M lam hb b`.

Establish `hc` using `content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct`. Establish `hr` using `hR.rest (Fin.rev b) (by omega)`. Use linear arithmetic over natural numbers and integers. Use `congr 1`. Use extensionality with `b`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. The claim follows by propositional logic.
-/
theorem counts_rows_holds : CountsRows := by
  intro k j t w M i lam xm xp hR tau _ ct
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  unfold boxesOfLabel boxesOfContent cloudBoxes
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun a : Fin (k + j) =>
      (dual M lam a : ℤ) ≤ cont t w M ct + (a.val : ℤ) ∧ cont t w M ct + (a.val : ℤ) < (tau a : ℤ))
      (fun b : Fin (k + j) => (Fin.rev b).val < k), add_comm]
  rw [Finset.filter_filter, Finset.filter_filter]
  refine Nat.add_le_add ?_ (le_of_eq ?_)
  · split_ifs with hct
    · refine le_trans (le_of_eq ?_) (card_filter_not_rev_lt_le k j (fun a : Fin (k + j) =>
        (dual M lam a : ℤ) ≤ cont t w M ct + (a.val : ℤ) ∧ cont t w M ct + (a.val : ℤ) < (tau a : ℤ)))
      congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro b _ ⟨⟨h1, _⟩, h3⟩
      have hU := rowStart_rev_eq k j t w M lam hb b
      have hc := content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct
      have hr := hR.rest (Fin.rev b) (by omega)
      omega
  · congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto

/- English proof (translation)
Introduce `k j t w M i lam tau htau ct`. Prove the components needed by the constructor for the conclusion. Conclude with `card_filter_rev_lt_le k j _`. Use `le_trans ?_ (ld_boxes_le t (M - w) i (k + j) (dual M lam) tau htau (cont t w M ct))` and prove the remaining obligations. Unfold `cloudBoxes boxesOfContent`.

Use `Finset.card_le_card ?_` and prove the remaining obligations. Introduce `b hb`. Conclude with `Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.2⟩`.
-/
theorem counts_cloud_holds : CountsCloud := by
  intro k j t w M i lam tau htau ct
  constructor
  · exact card_filter_rev_lt_le k j _
  · refine le_trans ?_ (ld_boxes_le t (M - w) i (k + j) (dual M lam) tau htau (cont t w M ct))
    unfold cloudBoxes boxesOfContent
    refine Finset.card_le_card ?_
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.2⟩

/- English proof (translation)
Introduce `k j t w M i lam xm xp hR tau htau ct hct`. Establish `hb : ∀ a, w ≤ lam a ∧ lam a ≤ M` using `fun a => ⟨hR.low a, hR.high a⟩`. Take `⟨hpi, _, hsum, _, _⟩` from `Finset.mem_filter.mp htau`. Establish `hle : ∀ b, dual M lam b ≤ tau b` using `fun b => (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hpi) b)).1`. Establish `htot : ∑ b : Fin (k + j), ((tau b : ℤ) - (dual M lam b : ℤ)) = (i : ℤ)`.

Rewrite using `[Finset.sum_sub_distrib]`. Establish `: ((∑ a, tau a : ℕ) : ℤ) = ((∑ a, dual M lam a + i : ℕ) : ℤ)` using `by rw [hsum]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `cloudBoxes`.

Rewrite using `[← htot, ← nsmul_eq_mul, ← Finset.sum_const]`. Use `le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)` and prove the remaining obligations. Introduce `b hbm`. Take `⟨_, h1, h2, h3⟩` from `Finset.mem_filter.mp hbm`. Establish `hU` using `rowStart_rev_eq k j t w M lam hb b`.

Establish `hc` using `content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct`. Establish `hr` using `(hR.cloud (Fin.rev b) h1).1`. Use linear arithmetic over natural numbers and integers. Introduce `b _ _`. Use `hle b` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem counts_deep_holds : CountsDeep := by
  intro k j t w M i lam xm xp hR tau htau ct hct
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  obtain ⟨hpi, _, hsum, _, _⟩ := Finset.mem_filter.mp htau
  have hle : ∀ b, dual M lam b ≤ tau b := fun b => (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hpi) b)).1
  have htot : ∑ b : Fin (k + j), ((tau b : ℤ) - (dual M lam b : ℤ)) = (i : ℤ) := by
    rw [Finset.sum_sub_distrib]
    have : ((∑ a, tau a : ℕ) : ℤ) = ((∑ a, dual M lam a + i : ℕ) : ℤ) := by rw [hsum]
    push_cast at this
    linarith
  unfold cloudBoxes
  rw [← htot, ← nsmul_eq_mul, ← Finset.sum_const]
  refine le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
  · intro b hbm
    obtain ⟨_, h1, h2, h3⟩ := Finset.mem_filter.mp hbm
    have hU := rowStart_rev_eq k j t w M lam hb b
    have hc := content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct
    have hr := (hR.cloud (Fin.rev b) h1).1
    omega
  · intro b _ _
    have := hle b
    omega

/- English proof (translation)
Establish `h1` using `counts_rows_holds k j t w M i lam xm xp hR tau htau ct`. Establish `h2` using `counts_cloud_holds k j t w M i lam tau htau ct`. Establish `hk : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ k` using `by exact_mod_cast h2.1`. Establish `ht : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ t` using `by exact_mod_cast h2.2`. Distinguish the cases in `hct : ct < xm`.

Rewrite `h1` using `[if_pos hct]`. Rewrite using `[if_pos hct, if_pos hct]`. Establish `h1' : (boxesOfLabel t w M lam tau ct : ℝ) ≤ (j : ℝ) + (cloudBoxes k j t w M lam tau ct : ℝ)`. Conclude with `h1` after adjusting the coercions. Establish `h3` using `counts_deep_holds k j t w M i lam xm xp hR tau htau ct hct`.

Establish `h3' : (cloudBoxes k j t w M lam tau ct : ℝ) * ((xm - ct : ℤ) : ℝ) ≤ (i : ℝ)` using `by exact_mod_cast h3`. Establish `hpos : (0 : ℝ) < ((xm - ct : ℤ) : ℝ)` using `by exact_mod_cast (by omega : (0 : ℤ) < xm - ct)`. Establish `h4 : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ (i : ℝ) / ((xm - ct : ℤ) : ℝ)` using `(le_div_iff₀ hpos).mpr h3'`. Establish `h5` using `le_min (le_min hk ht) h4`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `h1` using `[if_neg hct]`. Rewrite using `[if_neg hct, if_neg hct]`. Establish `h1' : (boxesOfLabel t w M lam tau ct : ℝ) ≤ (0 : ℝ) + (cloudBoxes k j t w M lam tau ct : ℝ)`. Conclude with `h1` after adjusting the coercions. Establish `h5` using `le_min (le_min hk ht) hk`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem boxesOfLabel_le_bound (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) (hR : Rows k j t w M lam xm xp)
    (tau : Fin (k + j) → ℕ) (htau : tau ∈ shapes t (M - w) i (dual M lam)) (ct : ℤ) :
    (boxesOfLabel t w M lam tau ct : ℝ) ≤
      (if ct < xm then (j : ℝ) else 0) +
        min (min (k : ℝ) (t : ℝ)) (if ct < xm then (i : ℝ) / ((xm - ct : ℤ) : ℝ) else (k : ℝ)) := by
  have h1 := counts_rows_holds k j t w M i lam xm xp hR tau htau ct
  have h2 := counts_cloud_holds k j t w M i lam tau htau ct
  have hk : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ k := by exact_mod_cast h2.1
  have ht : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ t := by exact_mod_cast h2.2
  by_cases hct : ct < xm
  · rw [if_pos hct] at h1
    rw [if_pos hct, if_pos hct]
    have h1' : (boxesOfLabel t w M lam tau ct : ℝ) ≤ (j : ℝ) + (cloudBoxes k j t w M lam tau ct : ℝ) := by
      exact_mod_cast h1
    have h3 := counts_deep_holds k j t w M i lam xm xp hR tau htau ct hct
    have h3' : (cloudBoxes k j t w M lam tau ct : ℝ) * ((xm - ct : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast h3
    have hpos : (0 : ℝ) < ((xm - ct : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < xm - ct)
    have h4 : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ (i : ℝ) / ((xm - ct : ℤ) : ℝ) := (le_div_iff₀ hpos).mpr h3'
    have h5 := le_min (le_min hk ht) h4
    linarith
  · rw [if_neg hct] at h1
    rw [if_neg hct, if_neg hct]
    have h1' : (boxesOfLabel t w M lam tau ct : ℝ) ≤ (0 : ℝ) + (cloudBoxes k j t w M lam tau ct : ℝ) := by
      exact_mod_cast h1
    have h5 := le_min (le_min hk ht) hk
    linarith

/- English proof (translation)
Introduce `k j t w M i lam xm xp hR ct`. Unfold `mu`. Distinguish the cases in `hne : (shapes t (M - w) i (dual M lam)).Nonempty`. Take `⟨tau, htau, heq⟩` from `Finset.exists_mem_eq_sup _ hne (fun tau => boxesOfContent (dual M lam) tau (cont t w M ct))`. Rewrite using `[heq]`.

Conclude with `boxesOfLabel_le_bound k j t w M i lam xm xp hR tau htau ct`. Rewrite using `[Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sup_empty]`. Establish `h0 : (((⊥ : ℕ) : ℕ) : ℝ) = 0` using `by simp`. Rewrite using `[h0]`. Apply the tactic sequence `refine add_nonneg (by split_ifs <;> positivity) (le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_)`.

Use `split_ifs with hct`. Conclude with `div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast (by omega : (0 : ℤ) ≤ xm - ct))`. Conclude with `Nat.cast_nonneg _`.
-/
theorem multiplicity_bound_holds : MuBound := by
  intro k j t w M i lam xm xp hR ct
  unfold mu
  by_cases hne : (shapes t (M - w) i (dual M lam)).Nonempty
  · obtain ⟨tau, htau, heq⟩ := Finset.exists_mem_eq_sup _ hne
      (fun tau => boxesOfContent (dual M lam) tau (cont t w M ct))
    rw [heq]
    exact boxesOfLabel_le_bound k j t w M i lam xm xp hR tau htau ct
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sup_empty]
    have h0 : (((⊥ : ℕ) : ℕ) : ℝ) = 0 := by simp
    rw [h0]
    refine add_nonneg (by split_ifs <;> positivity) (le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_)
    split_ifs with hct
    · exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast (by omega : (0 : ℤ) ≤ xm - ct))
    · exact Nat.cast_nonneg _

/- English proof (translation)
Establish `hb : ∀ a, w ≤ lam a ∧ lam a ≤ M` using `fun a => ⟨hR.low a, hR.high a⟩`. Unfold `mu at hmu`. Take `⟨tau, htau, hbx⟩` from `(Finset.lt_sup_iff).mp (Nat.pos_of_ne_zero hmu)`. Unfold `boxesOfContent at hbx`. Take `⟨b, hbm⟩` from `Finset.card_pos.mp hbx`.

Take `⟨h1, h2⟩` from `(Finset.mem_filter.mp hbm).2`. Establish `hU` using `rowStart_rev_eq k j t w M lam hb b`. Establish `hc` using `content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct`. Take `⟨col, hcol⟩ : ∃ col : ℕ, (col : ℤ) = cont t w M ct + (b.val : ℤ)` from `⟨(cont t w M ct + (b.val : ℤ)).toNat, Int.toNat_of_nonneg (by omega)⟩`. Establish `hg` using `(good_labels_holds k j t w M i lam hb tau htau b col (by omega) (by omega)).1`.

Unfold `label at hg`. Prove the components needed by the constructor for the conclusion. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hk : (Fin.rev b).val < k`. Use `(hR.cloud (Fin.rev b) hk).2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `hR.rest (Fin.rev b) (by omega)` as an intermediate fact. Use `hR.le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_label_interval_of_mu_ne_zero (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) (hR : Rows k j t w M lam xm xp)
    (ct : ℤ) (hmu : mu t (M - w) i (dual M lam) (cont t w M ct) ≠ 0) : maxB t w < ct ∧ ct < xp := by
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  unfold mu at hmu
  obtain ⟨tau, htau, hbx⟩ := (Finset.lt_sup_iff).mp (Nat.pos_of_ne_zero hmu)
  unfold boxesOfContent at hbx
  obtain ⟨b, hbm⟩ := Finset.card_pos.mp hbx
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hbm).2
  have hU := rowStart_rev_eq k j t w M lam hb b
  have hc := content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct
  obtain ⟨col, hcol⟩ : ∃ col : ℕ, (col : ℤ) = cont t w M ct + (b.val : ℤ) :=
    ⟨(cont t w M ct + (b.val : ℤ)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hg := (good_labels_holds k j t w M i lam hb tau htau b col (by omega) (by omega)).1
  unfold label at hg
  constructor
  · omega
  · by_cases hk : (Fin.rev b).val < k
    · have := (hR.cloud (Fin.rev b) hk).2
      omega
    · have := hR.rest (Fin.rev b) (by omega)
      have := hR.le
      omega

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, padicValInt.mul (hg a (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr fun x hx => hg x (Finset.mem_insert_of_mem hx)), ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))]`.
-/
theorem padicValInt_prod_eq_sum (l : ℕ) [Fact l.Prime] (s : Finset ℕ) (g : ℕ → ℤ) (hg : ∀ x ∈ s, g x ≠ 0) :
    padicValInt l (∏ x ∈ s, g x) = ∑ x ∈ s, padicValInt l (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValInt.mul (hg a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun x hx => hg x (Finset.mem_insert_of_mem hx)),
      ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))]

/- English proof (translation)
Unfold `padicValInt`. Rewrite using `[Int.natAbs_pow, padicValNat.pow]`.
-/
theorem padicValInt_pow_eq_mul (l : ℕ) [Fact l.Prime] (x : ℤ) (_hx : x ≠ 0) (m : ℕ) :
    padicValInt l (x ^ m) = m * padicValInt l x := by
  unfold padicValInt
  rw [Int.natAbs_pow, padicValNat.pow]

/- English proof (translation)
Introduce `l k j t w M i lam xm xp hl hR`. Establish `: Fact l.Prime` using `⟨hl⟩`. Establish `hb : ∀ a, w ≤ lam a ∧ lam a ≤ M` using `fun a => ⟨hR.low a, hR.high a⟩`. Establish `hdw : ∀ b, dual M lam b ≤ M - w` using `fun b => by`. Use `hb (Fin.rev b)` as an intermediate fact.

Unfold `dual`. Use linear arithmetic over natural numbers and integers. Establish `hcont : ∀ c : ℤ, cont t w M (maxB t w + (((M - w : ℕ) : ℤ) - c)) = c`. Introduce `c`. Unfold `cont`.

Expand and normalize the polynomial expressions, which then agree. Unfold `Dn`. Establish `hne : ∀ x ∈ Finset.range (k + j + (M - w) + i), (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) ^ mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ)) ≠ 0`. Introduce `x _`. Distinguish the cases in `h : (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) = 0`.

Establish `hc : ((x : ℤ) - ((k + j : ℕ) : ℤ)) = ((M - w : ℕ) : ℤ)` using `by omega`. Rewrite using `[hc, ld_mu_w]`. Simplify using the standard rewrite rules. Conclude with `pow_ne_zero _ h`. Establish `hterm : ∀ x ∈ Finset.range (k + j + (M - w) + i), padicValInt l ((((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) ^ mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ))) = mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ)) * vl l (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k …`.

Introduce `x _`. Distinguish the cases in `h : (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) = 0`. Establish `hc : ((x : ℤ) - ((k + j : ℕ) : ℤ)) = ((M - w : ℕ) : ℤ)` using `by omega`. Rewrite using `[hc, ld_mu_w]`. Simplify using the standard rewrite rules.

Unfold `vl`. Conclude with `padicValInt_pow_eq_mul l _ h _`. Rewrite using `[padicValInt_prod_eq_sum l _ _ hne, Finset.sum_congr rfl hterm]`. Use `Finset.sum_bij_ne_zero (fun x _ _ => maxB t w + (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ)))) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a _ h2`.

Establish `hmu : mu t (M - w) i (dual M lam) ((a : ℤ) - ((k + j : ℕ) : ℤ)) ≠ 0` using `left_ne_zero_of_mul h2`. Rewrite `hmu` using `[← hcont ((a : ℤ) - ((k + j : ℕ) : ℤ))]`. Conclude with `Finset.mem_Ioo.mpr (mem_label_interval_of_mu_ne_zero k j t w M i lam xm xp hR _ hmu)`. Introduce `a1 _ _ a2 _ _ h`. Use linear arithmetic over natural numbers and integers.

Introduce `ct _ h2`. Establish `hmu : mu t (M - w) i (dual M lam) (cont t w M ct) ≠ 0` using `left_ne_zero_of_mul h2`. Take `⟨h3, h4⟩` from `muSupport t (M - w) i (k + j) (dual M lam) _ hdw hmu`. Establish `ha : (((cont t w M ct + ((k + j : ℕ) : ℤ)).toNat : ℕ) : ℤ) = cont t w M ct + ((k + j : ℕ) : ℤ)` using `Int.toNat_of_nonneg (by omega)`. Establish `hx : (((cont t w M ct + ((k + j : ℕ) : ℤ)).toNat : ℕ) : ℤ) - ((k + j : ℕ) : ℤ) = cont t w M ct`.

Rewrite using `[ha]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : ((M - w : ℕ) : ℤ) - cont t w M ct = ct - maxB t w`. Unfold `cont`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨(cont t w M ct + ((k + j : ℕ) : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, hv]`. Conclude with `h2`. Rewrite using `[hx, hv]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `a _ _`. Rewrite using `[hcont]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem depth_valuation_sum_holds : DnValSum := by
  intro l k j t w M i lam xm xp hl hR
  have : Fact l.Prime := ⟨hl⟩
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  have hdw : ∀ b, dual M lam b ≤ M - w := fun b => by
    have := hb (Fin.rev b)
    unfold dual
    omega
  have hcont : ∀ c : ℤ, cont t w M (maxB t w + (((M - w : ℕ) : ℤ) - c)) = c := by
    intro c
    unfold cont
    ring
  unfold Dn
  have hne : ∀ x ∈ Finset.range (k + j + (M - w) + i),
      (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) ^
        mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ)) ≠ 0 := by
    intro x _
    by_cases h : (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) = 0
    · have hc : ((x : ℤ) - ((k + j : ℕ) : ℤ)) = ((M - w : ℕ) : ℤ) := by omega
      rw [hc, ld_mu_w]
      simp
    · exact pow_ne_zero _ h
  have hterm : ∀ x ∈ Finset.range (k + j + (M - w) + i),
      padicValInt l ((((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) ^
        mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ))) =
      mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ)) *
        vl l (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) := by
    intro x _
    by_cases h : (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) = 0
    · have hc : ((x : ℤ) - ((k + j : ℕ) : ℤ)) = ((M - w : ℕ) : ℤ) := by omega
      rw [hc, ld_mu_w]
      simp
    · unfold vl
      exact padicValInt_pow_eq_mul l _ h _
  rw [padicValInt_prod_eq_sum l _ _ hne, Finset.sum_congr rfl hterm]
  refine Finset.sum_bij_ne_zero
    (fun x _ _ => maxB t w + (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ)))) ?_ ?_ ?_ ?_
  · intro a _ h2
    have hmu : mu t (M - w) i (dual M lam) ((a : ℤ) - ((k + j : ℕ) : ℤ)) ≠ 0 := left_ne_zero_of_mul h2
    rw [← hcont ((a : ℤ) - ((k + j : ℕ) : ℤ))] at hmu
    exact Finset.mem_Ioo.mpr (mem_label_interval_of_mu_ne_zero k j t w M i lam xm xp hR _ hmu)
  · intro a1 _ _ a2 _ _ h
    omega
  · intro ct _ h2
    have hmu : mu t (M - w) i (dual M lam) (cont t w M ct) ≠ 0 := left_ne_zero_of_mul h2
    obtain ⟨h3, h4⟩ := muSupport t (M - w) i (k + j) (dual M lam) _ hdw hmu
    have ha : (((cont t w M ct + ((k + j : ℕ) : ℤ)).toNat : ℕ) : ℤ) = cont t w M ct + ((k + j : ℕ) : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    have hx : (((cont t w M ct + ((k + j : ℕ) : ℤ)).toNat : ℕ) : ℤ) - ((k + j : ℕ) : ℤ) = cont t w M ct := by
      rw [ha]; ring
    have hv : ((M - w : ℕ) : ℤ) - cont t w M ct = ct - maxB t w := by
      unfold cont; ring
    refine ⟨(cont t w M ct + ((k + j : ℕ) : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · rw [hx, hv]
      exact h2
    · rw [hx, hv]
      ring
  · intro a _ _
    rw [hcont]
    congr 2
    ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `: Finset.Ioo mB (mB + 1 + ((0 : ℕ) : ℤ)) = ∅`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Establish `hins : Finset.Ioo mB (mB + 1 + ((n + 1 : ℕ) : ℤ)) = insert (mB + 1 + (n : ℤ)) (Finset.Ioo mB (mB + 1 + (n : ℤ)))`.

Use extensionality with `x`. Simplify using `only [Finset.mem_Ioo, Finset.mem_insert]`. Use linear arithmetic over natural numbers and integers. Establish `hnot : (mB + 1 + (n : ℤ)) ∉ Finset.Ioo mB (mB + 1 + (n : ℤ))`. Simplify using the standard rewrite rules.

Rewrite using `[hins, Finset.sum_insert hnot, ih, Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]`. Use `congr 1`. Unfold `vl`. Establish `: mB + 1 + (n : ℤ) - mB = ((n + 1 : ℕ) : ℤ)` using `by push_cast; ring`. Rewrite using `[this, padicValInt.of_nat]`.
-/
theorem sum_padicVal_shift_eq_factorial (l : ℕ) [Fact l.Prime] (mB : ℤ) (n : ℕ) :
    ∑ ct ∈ Finset.Ioo mB (mB + 1 + (n : ℤ)), vl l (ct - mB) = padicValNat l n.factorial := by
  induction n with
  | zero =>
    have : Finset.Ioo mB (mB + 1 + ((0 : ℕ) : ℤ)) = ∅ := by
      ext x
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [this]
    simp
  | succ n ih =>
    have hins : Finset.Ioo mB (mB + 1 + ((n + 1 : ℕ) : ℤ)) =
        insert (mB + 1 + (n : ℤ)) (Finset.Ioo mB (mB + 1 + (n : ℤ))) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    have hnot : (mB + 1 + (n : ℤ)) ∉ Finset.Ioo mB (mB + 1 + (n : ℤ)) := by
      simp
    rw [hins, Finset.sum_insert hnot, ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]
    congr 1
    unfold vl
    have : mB + 1 + (n : ℤ) - mB = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, padicValInt.of_nat]

/- English proof (translation)
Introduce `l xm mB hl hlt`. Establish `: Fact l.Prime` using `⟨hl⟩`. Establish `hn : (((xm - mB - 1).toNat : ℕ) : ℤ) = xm - mB - 1` using `Int.toNat_of_nonneg (by omega)`. Prove the components needed by the constructor for the conclusion. Establish `h` using `sum_padicVal_shift_eq_factorial l mB (xm - mB - 1).toNat`.

Rewrite `h` using `[hn]`. Establish `he : mB + 1 + (xm - mB - 1) = xm` using `by ring`. Rewrite `h` using `[he]`. Conclude with `h`. Establish `h3` using `sub_one_mul_padicValNat_factorial (p := l) (xm - mB - 1).toNat`.

Establish `h4 : (l - 1) * padicValNat l ((xm - mB - 1).toNat).factorial ≤ (xm - mB - 1).toNat`. Rewrite using `[h3]`. Conclude with `Nat.sub_le _ _`. Establish `hl2` using `hl.two_le`. Establish `hl1 : (0 : ℝ) < (l : ℝ) - 1`.

Establish `: (2 : ℝ) ≤ (l : ℝ)` using `by exact_mod_cast hl2`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[le_div_iff₀ hl1]`. Establish `h5 : (((l - 1 : ℕ) : ℝ)) * (padicValNat l ((xm - mB - 1).toNat).factorial : ℝ) ≤ (((xm - mB - 1).toNat : ℕ) : ℝ)` using `by exact_mod_cast h4`. Establish `h6 : (((l - 1 : ℕ) : ℝ)) = (l : ℝ) - 1`.

Rewrite using `[Nat.cast_sub (by omega)]; simp`. Establish `h7 : (((xm - mB - 1).toNat : ℕ) : ℝ) = ((xm - mB : ℤ) : ℝ) - 1`. Establish `: ((((xm - mB - 1).toNat : ℕ) : ℤ) : ℝ) = ((xm - mB - 1 : ℤ) : ℝ)` using `by rw [hn]`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `h5` using `[h6, h7]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem first_bound_holds : FactorialValuationSum := by
  intro l xm mB hl hlt
  have : Fact l.Prime := ⟨hl⟩
  have hn : (((xm - mB - 1).toNat : ℕ) : ℤ) = xm - mB - 1 := Int.toNat_of_nonneg (by omega)
  constructor
  · have h := sum_padicVal_shift_eq_factorial l mB (xm - mB - 1).toNat
    rw [hn] at h
    have he : mB + 1 + (xm - mB - 1) = xm := by ring
    rw [he] at h
    exact h
  · have h3 := sub_one_mul_padicValNat_factorial (p := l) (xm - mB - 1).toNat
    have h4 : (l - 1) * padicValNat l ((xm - mB - 1).toNat).factorial ≤ (xm - mB - 1).toNat := by
      rw [h3]; exact Nat.sub_le _ _
    have hl2 := hl.two_le
    have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
      linarith
    rw [le_div_iff₀ hl1]
    have h5 : (((l - 1 : ℕ) : ℝ)) * (padicValNat l ((xm - mB - 1).toNat).factorial : ℝ) ≤
        (((xm - mB - 1).toNat : ℕ) : ℝ) := by exact_mod_cast h4
    have h6 : (((l - 1 : ℕ) : ℝ)) = (l : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have h7 : (((xm - mB - 1).toNat : ℕ) : ℝ) = ((xm - mB : ℤ) : ℝ) - 1 := by
      have : ((((xm - mB - 1).toNat : ℕ) : ℤ) : ℝ) = ((xm - mB - 1 : ℤ) : ℝ) := by rw [hn]
      push_cast at this ⊢
      linarith
    rw [h6, h7] at h5
    linarith

/- English proof (translation)
Introduce `l h i hi`. Establish `hil : 0 ≤ i / (l : ℝ)` using `div_nonneg hi (Nat.cast_nonneg _)`. Prove the components needed by the constructor for the conclusion. Unfold `harm split_ifs with hlh`. Conclude with `mul_nonneg hil (add_nonneg zero_le_one Real.posLog_nonneg)`.

Use `mul_le_mul_of_nonneg_left ?_ hil` and prove the remaining obligations. Establish `: Real.log ((h : ℝ) / (l : ℝ)) ≤ Real.posLog ((h : ℝ) / (l : ℝ))` using `le_max_right _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h1 h2`. Unfold `harm`.

Rewrite using `[if_neg (by omega)]`. Establish `hl0 : (0 : ℝ) < (l : ℝ)` using `by exact_mod_cast h1`. Establish `hx : (1 : ℝ) ≤ (h : ℝ) / (l : ℝ)`. Rewrite using `[le_div_iff₀ hl0, one_mul]`. Conclude with `h2` after adjusting the coercions.

Rewrite using `[Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hx)]`.
-/
theorem harmonic_positive_log_holds : HarmPosLog := by
  intro l h i hi
  have hil : 0 ≤ i / (l : ℝ) := div_nonneg hi (Nat.cast_nonneg _)
  constructor
  · unfold harm
    split_ifs with hlh
    · exact mul_nonneg hil (add_nonneg zero_le_one Real.posLog_nonneg)
    · refine mul_le_mul_of_nonneg_left ?_ hil
      have : Real.log ((h : ℝ) / (l : ℝ)) ≤ Real.posLog ((h : ℝ) / (l : ℝ)) := le_max_right _ _
      linarith
  · intro h1 h2
    unfold harm
    rw [if_neg (by omega)]
    have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast h1
    have hx : (1 : ℝ) ≤ (h : ℝ) / (l : ℝ) := by
      rw [le_div_iff₀ hl0, one_mul]
      exact_mod_cast h2
    rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hx)]

/- English proof (translation)
Unfold `labelLHS`. Use `congr 1`. Use `Finset.sum_nbij' (fun ct => ct - mB) (fun ct => ct + mB) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `ct h`. Simplify using `only [Finset.mem_Icc] at h ⊢`.

Use linear arithmetic over natural numbers and integers. Introduce `ct h`. Simplify using `only [Finset.mem_Icc] at h ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `ct _`.

Expand and normalize the polynomial expressions, which then agree. Introduce `ct _`. Expand and normalize the polynomial expressions, which then agree. Introduce `ct _`. Rewrite using `[sub_zero]`.

Use `Finset.sum_nbij' (fun ct => ct - mB) (fun ct => ct + mB) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `ct h`. Simplify using `only [Finset.mem_Ioo] at h ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `ct h`.

Simplify using `only [Finset.mem_Ioo] at h ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `ct _`. Expand and normalize the polynomial expressions, which then agree. Introduce `ct _`.

Expand and normalize the polynomial expressions, which then agree. Introduce `ct _`. Establish `e1 : xm - mB - (ct - mB) = xm - ct` using `by ring`. Rewrite using `[e1, sub_zero]`.
-/
theorem labelLHS_shift_to_zero (l k t : ℕ) (i : ℝ) (xm xp mB : ℤ) :
    labelLHS l k t i xm xp mB = labelLHS l k t i (xm - mB) (xp - mB) 0 := by
  unfold labelLHS
  congr 1
  · refine Finset.sum_nbij' (fun ct => ct - mB) (fun ct => ct + mB) ?_ ?_ ?_ ?_ ?_
    · intro ct h
      simp only [Finset.mem_Icc] at h ⊢
      omega
    · intro ct h
      simp only [Finset.mem_Icc] at h ⊢
      omega
    · intro ct _
      ring
    · intro ct _
      ring
    · intro ct _
      rw [sub_zero]
  · refine Finset.sum_nbij' (fun ct => ct - mB) (fun ct => ct + mB) ?_ ?_ ?_ ?_ ?_
    · intro ct h
      simp only [Finset.mem_Ioo] at h ⊢
      omega
    · intro ct h
      simp only [Finset.mem_Ioo] at h ⊢
      omega
    · intro ct _
      ring
    · intro ct _
      ring
    · intro ct _
      have e1 : xm - mB - (ct - mB) = xm - ct := by ring
      rw [e1, sub_zero]

/- English proof (translation)
Unfold `IlInd`. Establish `h : (∃ y : ℤ, xm - mB ≤ y ∧ y ≤ xp - mB ∧ (l : ℤ) ∣ y - 0) ↔ (∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, h1, h2, h3⟩`. Conclude with `⟨y + mB, by omega, by omega, by simpa using h3⟩`.

Introduce and unpack `⟨y, h1, h2, h3⟩`. Conclude with `⟨y - mB, by omega, by omega, by simpa using h3⟩`. Distinguish the cases in `hc : ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB`. Rewrite using `[if_pos hc, if_pos (h.mpr hc)]`. Rewrite using `[if_neg hc, if_neg (fun h' => hc (h.mp h'))]`.
-/
theorem indexIntegral_shift (l : ℕ) (xm xp mB : ℤ) : IlInd l (xm - mB) (xp - mB) 0 = IlInd l xm xp mB := by
  unfold IlInd
  have h : (∃ y : ℤ, xm - mB ≤ y ∧ y ≤ xp - mB ∧ (l : ℤ) ∣ y - 0) ↔
      (∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB) := by
    constructor
    · rintro ⟨y, h1, h2, h3⟩
      exact ⟨y + mB, by omega, by omega, by simpa using h3⟩
    · rintro ⟨y, h1, h2, h3⟩
      exact ⟨y - mB, by omega, by omega, by simpa using h3⟩
  by_cases hc : ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB
  · rw [if_pos hc, if_pos (h.mpr hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (h.mp h'))]

/- English proof (translation)
Unfold `IlInd`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem indexIntegral_nonneg (l : ℕ) (xm xp mB : ℤ) : 0 ≤ IlInd l xm xp mB := by
  unfold IlInd
  split_ifs <;> norm_num

/- English proof (translation)
Use `split_ifs`. Conclude with `le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg hi (Nat.cast_nonneg _))`. Conclude with `le_rfl`.
-/
theorem gated_min_nonneg (l k t : ℕ) (i : ℝ) (hi : 0 ≤ i) (D : ℤ) :
    0 ≤ (if ((d0 l D : ℕ) : ℤ) < D then min (min (k : ℝ) (t : ℝ)) (i / (d0 l D : ℝ)) else 0) := by
  split_ifs
  · exact le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg hi (Nat.cast_nonneg _))
  · exact le_rfl

/- English proof (translation)
Introduce `l k t h i xm xp mB hl hi hmx hxx hxp hh`. Distinguish the cases in `hlh : h < l`. Establish `hlhZ : (h : ℤ) < (l : ℤ)` using `by exact_mod_cast hlh`. Establish `hz : ∀ ct : ℤ, mB < ct → ct ≤ xp → (vl l (ct - mB) : ℝ) = 0`. Introduce `ct h1 h2`.

Rewrite using `[label_vl_zero_small (by omega) (by omega)]`. Simplify using the standard rewrite rules. Establish `hL : labelLHS l k t i xm xp mB = 0`. Unfold `labelLHS`. Rewrite using `[Finset.sum_eq_zero (fun ct hct => by`.

Rewrite using `[hz ct (by have := Finset.mem_Icc.mp hct; omega) (Finset.mem_Icc.mp hct).2, mul_zero]),`. Use the proof step `Finset.sum_eq_zero (fun ct hct => by`. Rewrite using `[hz ct (Finset.mem_Ioo.mp hct).1 (by have := Finset.mem_Ioo.mp hct; omega), mul_zero]),`. Use the proof step `add_zero]`. Rewrite using `[hL]`.

Unfold `labelSumBoundPos harm`. Rewrite using `[if_pos hlh, add_zero]`. Use `add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (div_nonneg ?_ (Nat.cast_nonneg _)) (indexIntegral_nonneg _ _ _ _))) (gated_min_nonneg l k t i hi _)` and prove the remaining obligations. Conclude with `(by omega : (0 : ℤ) ≤ xp - xm)` after adjusting the coercions. Establish `h1` using `labelSumLe_holds l k t h i (xm - mB) (xp - mB) 0 hl hi le_rfl (by omega) (by omega) (by omega) hh (by omega)`.

Rewrite `h1` using `[← labelLHS_shift_to_zero]`. Unfold `labelSumBound at h1`. Unfold `labelSumBoundPos harm`. Rewrite using `[if_neg hlh]`. Establish `e : xp - mB - (xm - mB) = xp - xm` using `by ring`.

Rewrite `h1` using `[indexIntegral_shift, e]`. Simplify using `only [sub_zero] at h1`. Conclude with `h1`.
-/
theorem label_sum_plus_holds : LabelSumPlus := by
  intro l k t h i xm xp mB hl hi hmx hxx hxp hh
  by_cases hlh : h < l
  · have hlhZ : (h : ℤ) < (l : ℤ) := by exact_mod_cast hlh
    have hz : ∀ ct : ℤ, mB < ct → ct ≤ xp → (vl l (ct - mB) : ℝ) = 0 := by
      intro ct h1 h2
      rw [label_vl_zero_small (by omega) (by omega)]
      simp
    have hL : labelLHS l k t i xm xp mB = 0 := by
      unfold labelLHS
      rw [Finset.sum_eq_zero (fun ct hct => by
            rw [hz ct (by have := Finset.mem_Icc.mp hct; omega) (Finset.mem_Icc.mp hct).2, mul_zero]),
          Finset.sum_eq_zero (fun ct hct => by
            rw [hz ct (Finset.mem_Ioo.mp hct).1 (by have := Finset.mem_Ioo.mp hct; omega), mul_zero]),
          add_zero]
    rw [hL]
    unfold labelSumBoundPos harm
    rw [if_pos hlh, add_zero]
    refine add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (div_nonneg ?_ (Nat.cast_nonneg _))
      (indexIntegral_nonneg _ _ _ _))) (gated_min_nonneg l k t i hi _)
    exact_mod_cast (by omega : (0 : ℤ) ≤ xp - xm)
  · have h1 := labelSumLe_holds l k t h i (xm - mB) (xp - mB) 0 hl hi le_rfl (by omega) (by omega) (by omega) hh
      (by omega)
    rw [← labelLHS_shift_to_zero] at h1
    unfold labelSumBound at h1
    unfold labelSumBoundPos harm
    rw [if_neg hlh]
    have e : xp - mB - (xm - mB) = xp - xm := by ring
    rw [indexIntegral_shift, e] at h1
    simp only [sub_zero] at h1
    exact h1

/- English proof (translation)
Introduce `a b hab`. Unfold `harm`. Use `split_ifs with hlh`. Conclude with `le_rfl`. Establish `hlog : 0 ≤ Real.log ((h : ℝ) / (l : ℝ))`.

Break down `Nat.eq_zero_or_pos l with h0 | h0` into its components or cases. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Establish `hl0 : (0 : ℝ) < (l : ℝ)` using `by exact_mod_cast h0`. Use `Real.log_nonneg ?_` and prove the remaining obligations.

Rewrite using `[le_div_iff₀ hl0, one_mul]`. Conclude with `(by omega : l ≤ h)` after adjusting the coercions. Conclude with `mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _)) (by linarith)`.
-/
theorem harmonic_monotone (l h : ℕ) : Monotone (harm l h) := by
  intro a b hab
  unfold harm
  split_ifs with hlh
  · exact le_rfl
  · have hlog : 0 ≤ Real.log ((h : ℝ) / (l : ℝ)) := by
      rcases Nat.eq_zero_or_pos l with h0 | h0
      · rw [h0]; simp
      · have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast h0
        refine Real.log_nonneg ?_
        rw [le_div_iff₀ hl0, one_mul]
        exact_mod_cast (by omega : l ≤ h)
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _)) (by linarith)

/- English proof (translation)
Use `split_ifs`. Conclude with `min_le_min_left _ (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _))`. Conclude with `le_rfl`.
-/
theorem gated_min_monotone (l k t : ℕ) (D : ℤ) {a b : ℝ} (hab : a ≤ b) :
    (if ((d0 l D : ℕ) : ℤ) < D then min (min (k : ℝ) (t : ℝ)) (a / (d0 l D : ℝ)) else 0) ≤
      (if ((d0 l D : ℕ) : ℤ) < D then min (min (k : ℝ) (t : ℝ)) (b / (d0 l D : ℝ)) else 0) := by
  split_ifs
  · exact min_le_min_left _ (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _))
  · exact le_rfl

/- English proof (translation)
Unfold `labelSumBoundPos`. Establish `h1` using `gated_min_monotone l k t (xm - mB) hab`. Establish `h2` using `harmonic_monotone l h hab`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem labelRHSPlus_monotone (l k t h : ℕ) (xm xp mB : ℤ) {a b : ℝ} (hab : a ≤ b) :
    labelSumBoundPos l k t h a xm xp mB ≤ labelSumBoundPos l k t h b xm xp mB := by
  unfold labelSumBoundPos
  have h1 := gated_min_monotone l k t (xm - mB) hab
  have h2 := harmonic_monotone l h hab
  linarith

/- English proof (translation)
Introduce `l k j t w M h i lam xm xp hl hR hxp hh`. Establish `hsum` using `depth_valuation_sum_holds l k j t w M i lam xm xp hl hR`. Establish `hA1` using `first_bound_holds l xm (maxB t w) hl hR.above`. Establish `hLS` using `label_sum_plus_holds l k t h (i : ℝ) xm xp (maxB t w) hl (Nat.cast_nonneg _) hR.above hR.le hxp hh`. Rewrite using `[hsum, Nat.cast_sum]`.

Simplify using `only [Nat.cast_mul]`. Establish `hdisj : Disjoint (Finset.Ioo (maxB t w) xm) (Finset.Ico xm xp)`. Rewrite using `[Finset.disjoint_left]`. Introduce `x h1 h2`. Use `(Finset.mem_Ioo.mp h1).2` as an intermediate fact.

Use `(Finset.mem_Ico.mp h2).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hun : Finset.Ioo (maxB t w) xp = Finset.Ioo (maxB t w) xm ∪ Finset.Ico xm xp`. Use extensionality with `x`. Simplify using `only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_Ico]`.

Use `hR.above` as an intermediate fact. Use `hR.le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hun, Finset.sum_union hdisj]`. Establish `h1 : ∑ ct ∈ Finset.Ioo (maxB t w) xm, (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ) ≤ (j : ℝ) * ∑ ct ∈ Finset.Ioo (maxB t w) xm, (vl l (ct - maxB t w) : ℝ) + ∑ ct ∈ Finset.Ioo (maxB t w) xm, min (min (k : ℝ) (t : ℝ)) ((i : ℝ) / ((xm - ct : ℤ) : ℝ) …`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum ?_` and prove the remaining obligations. Introduce `ct hct`. Establish `hlt` using `(Finset.mem_Ioo.mp hct).2`. Establish `hm` using `multiplicity_bound_holds k j t w M i lam xm xp hR ct`.

Rewrite `hm` using `[if_pos hlt, if_pos hlt]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ∑ ct ∈ Finset.Ico xm xp, (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ) ≤ ∑ ct ∈ Finset.Icc xm xp, (k : ℝ) * (vl l (ct - maxB t w) : ℝ)`. Use `le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self ?_)` and prove the remaining obligations. Introduce `ct hct`.

Establish `hge` using `(Finset.mem_Ico.mp hct).1`. Establish `hm` using `multiplicity_bound_holds k j t w M i lam xm xp hR ct`. Rewrite `hm` using `[if_neg (by omega), if_neg (by omega), zero_add]`. Conclude with `mul_le_mul_of_nonneg_right (le_trans hm (min_le_right _ _)) (Nat.cast_nonneg _)`. Introduce `ct _ _`.

Conclude with `mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)`. Establish `hA : ∑ ct ∈ Finset.Ioo (maxB t w) xm, (vl l (ct - maxB t w) : ℝ) ≤ (((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1)`. Establish `h3` using `hA1.2`. Rewrite `h3` using `[← hA1.1, Nat.cast_sum]`. Conclude with `h3`.

Establish `hA'` using `mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))`. Unfold `labelLHS at hLS`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem second_valuation_holds : Step2Val := by
  intro l k j t w M h i lam xm xp hl hR hxp hh
  have hsum := depth_valuation_sum_holds l k j t w M i lam xm xp hl hR
  have hA1 := first_bound_holds l xm (maxB t w) hl hR.above
  have hLS := label_sum_plus_holds l k t h (i : ℝ) xm xp (maxB t w) hl (Nat.cast_nonneg _) hR.above hR.le hxp hh
  rw [hsum, Nat.cast_sum]
  simp only [Nat.cast_mul]
  have hdisj : Disjoint (Finset.Ioo (maxB t w) xm) (Finset.Ico xm xp) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have := (Finset.mem_Ioo.mp h1).2
    have := (Finset.mem_Ico.mp h2).1
    omega
  have hun : Finset.Ioo (maxB t w) xp = Finset.Ioo (maxB t w) xm ∪ Finset.Ico xm xp := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_Ico]
    have := hR.above
    have := hR.le
    omega
  rw [hun, Finset.sum_union hdisj]
  have h1 : ∑ ct ∈ Finset.Ioo (maxB t w) xm,
        (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ) ≤
      (j : ℝ) * ∑ ct ∈ Finset.Ioo (maxB t w) xm, (vl l (ct - maxB t w) : ℝ) +
        ∑ ct ∈ Finset.Ioo (maxB t w) xm,
          min (min (k : ℝ) (t : ℝ)) ((i : ℝ) / ((xm - ct : ℤ) : ℝ)) * (vl l (ct - maxB t w) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro ct hct
    have hlt := (Finset.mem_Ioo.mp hct).2
    have hm := multiplicity_bound_holds k j t w M i lam xm xp hR ct
    rw [if_pos hlt, if_pos hlt] at hm
    calc (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ)
        ≤ ((j : ℝ) + min (min (k : ℝ) (t : ℝ)) ((i : ℝ) / ((xm - ct : ℤ) : ℝ))) * (vl l (ct - maxB t w) : ℝ) :=
          mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _)
      _ = _ := by ring
  have h2 : ∑ ct ∈ Finset.Ico xm xp,
        (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ) ≤
      ∑ ct ∈ Finset.Icc xm xp, (k : ℝ) * (vl l (ct - maxB t w) : ℝ) := by
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self ?_)
    · intro ct hct
      have hge := (Finset.mem_Ico.mp hct).1
      have hm := multiplicity_bound_holds k j t w M i lam xm xp hR ct
      rw [if_neg (by omega), if_neg (by omega), zero_add] at hm
      exact mul_le_mul_of_nonneg_right (le_trans hm (min_le_right _ _)) (Nat.cast_nonneg _)
    · intro ct _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hA : ∑ ct ∈ Finset.Ioo (maxB t w) xm, (vl l (ct - maxB t w) : ℝ) ≤
      (((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1) := by
    have h3 := hA1.2
    rw [← hA1.1, Nat.cast_sum] at h3
    exact h3
  have hA' := mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  unfold labelLHS at hLS
  linarith

/- English proof (translation)
Introduce `l k j t w M h i I lam xm xp hl hR hxp hh hiI`. Establish `h1` using `second_valuation_holds l k j t w M h i lam xm xp hl hR hxp hh`. Establish `h2` using `labelRHSPlus_monotone l k t h xm xp (maxB t w) hiI`. Establish `hl1 : (0 : ℝ) ≤ (l : ℝ) - 1`. Establish `: (2 : ℝ) ≤ (l : ℝ)` using `by exact_mod_cast hl.two_le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD : ((xm - maxB t w : ℤ) : ℝ) ≤ (h : ℝ)`. Use `hR.le` as an intermediate fact. Conclude with `(by omega : xm - maxB t w ≤ (h : ℤ))` after adjusting the coercions. Establish `h3 : (((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) - 1) / ((l : ℝ) - 1)` using `div_le_div_of_nonneg_right (by linarith) hl1`.

Establish `h4` using `mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem second_valuation_up_to_holds : Step2ValUpTo := by
  intro l k j t w M h i I lam xm xp hl hR hxp hh hiI
  have h1 := second_valuation_holds l k j t w M h i lam xm xp hl hR hxp hh
  have h2 := labelRHSPlus_monotone l k t h xm xp (maxB t w) hiI
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl.two_le
    linarith
  have hD : ((xm - maxB t w : ℤ) : ℝ) ≤ (h : ℝ) := by
    have := hR.le
    exact_mod_cast (by omega : xm - maxB t w ≤ (h : ℤ))
  have h3 : (((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) - 1) / ((l : ℝ) - 1) :=
    div_le_div_of_nonneg_right (by linarith) hl1
  have h4 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  linarith

/- English proof (translation)
Introduce `l k j t q h N' ecl xm xp mB I hl hI`. Unfold `cPrime cCoarse labelSumBoundPos`. Establish `h1` using `(harmonic_positive_log_holds l h I hI).1`. Establish `hl1 : (0 : ℝ) ≤ (l : ℝ) - 1`. Establish `: (2 : ℝ) ≤ (l : ℝ)` using `by exact_mod_cast hl`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ((h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6`. Establish `h3 : ((h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1)` using `div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ (N' : ℝ) := Nat.cast_nonneg _; linarith) hl1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4` using `mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (q : ℝ) + 2 * (j : ℝ))`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem c_prime_le_coarse_holds : CPrimeLeCoarse := by
  intro l k j t q h N' ecl xm xp mB I hl hI
  unfold cPrime cCoarse labelSumBoundPos
  have h1 := (harmonic_positive_log_holds l h I hI).1
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have h2 : ((h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6 := by
    have h3 : ((h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) :=
      div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ (N' : ℝ) := Nat.cast_nonneg _; linarith) hl1
    linarith
  have h4 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0 : ℝ) ≤ (q : ℝ) + 2 * (j : ℝ))
  linarith

/- English proof (translation)
Unfold `labelSumBoundPos`. Establish `e1 : xp + c - (xm + c) = xp - xm` using `by ring`. Establish `e2 : xm + c - (mB + c) = xm - mB` using `by ring`. Establish `e3 : xp + c - (mB + c) = xp - mB` using `by ring`. Establish `e4 : IlInd l (xm + c) (xp + c) (mB + c) = IlInd l xm xp mB`.

Rewrite using `[← indexIntegral_shift l (xm + c) (xp + c) (mB + c), e2, e3, indexIntegral_shift]`. Rewrite using `[e1, e2, e4]`.
-/
theorem labelRHSPlus_shift_invariant (l k t h : ℕ) (I : ℝ) (xm xp mB c : ℤ) :
    labelSumBoundPos l k t h I (xm + c) (xp + c) (mB + c) = labelSumBoundPos l k t h I xm xp mB := by
  unfold labelSumBoundPos
  have e1 : xp + c - (xm + c) = xp - xm := by ring
  have e2 : xm + c - (mB + c) = xm - mB := by ring
  have e3 : xp + c - (mB + c) = xp - mB := by ring
  have e4 : IlInd l (xm + c) (xp + c) (mB + c) = IlInd l xm xp mB := by
    rw [← indexIntegral_shift l (xm + c) (xp + c) (mB + c), e2, e3, indexIntegral_shift]
  rw [e1, e2, e4]

end Formalism.CohomologicalDescent.UnitNormBounds
