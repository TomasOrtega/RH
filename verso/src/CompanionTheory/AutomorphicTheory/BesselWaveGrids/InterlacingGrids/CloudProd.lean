import Mathlib

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[prod_range_succ, ih, if_neg (Nat.succ_ne_zero n)]`. Establish `hn : ((n : ℝ) + 1) ≠ 0` using `by positivity`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem cloud_weight_prod (c : ℝ) (n : ℕ) :
    ∏ j ∈ range (n + 1), (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) = (2 + c) * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, if_neg (Nat.succ_ne_zero n)]
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp

/- English proof (translation)
Use `split_ifs with hj`. Establish `: (1 + c) / max d 1 ≤ 1 + c` using `div_le_self (by linarith) (le_max_right _ _)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hj1 : (1 : ℝ) ≤ j` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj`. Establish `hpos : 0 < (j : ℝ) * (1 + c)` using `by positivity`.

Establish `h1 : (j : ℝ) * (1 + c) ≤ (j : ℝ) * g` using `mul_le_mul_of_nonneg_left hg (by positivity)`. Establish `h2 : (j : ℝ) * (1 + c) ≤ max d 1` using `le_trans (h1.trans hd) (le_max_left _ _)`. Establish `h3 : (1 + c) / max d 1 ≤ (1 + c) / ((j : ℝ) * (1 + c))` using `div_le_div_of_nonneg_left (by linarith) hpos h2`. Establish `h4 : (1 + c) / ((j : ℝ) * (1 + c)) = 1 / j`. Establish `: (1 + c) ≠ 0` using `by linarith`.

Establish `: (j : ℝ) ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cloud_factor_le (c g d : ℝ) (j : ℕ) (hc : 0 ≤ c) (hg : 1 + c ≤ g) (hd : (j : ℝ) * g ≤ d) :
    1 + (1 + c) / max d 1 ≤ (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) := by
  split_ifs with hj
  · have : (1 + c) / max d 1 ≤ 1 + c := div_le_self (by linarith) (le_max_right _ _)
    linarith
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have hpos : 0 < (j : ℝ) * (1 + c) := by positivity
    have h1 : (j : ℝ) * (1 + c) ≤ (j : ℝ) * g := mul_le_mul_of_nonneg_left hg (by positivity)
    have h2 : (j : ℝ) * (1 + c) ≤ max d 1 := le_trans (h1.trans hd) (le_max_left _ _)
    have h3 : (1 + c) / max d 1 ≤ (1 + c) / ((j : ℝ) * (1 + c)) :=
      div_le_div_of_nonneg_left (by linarith) hpos h2
    have h4 : (1 + c) / ((j : ℝ) * (1 + c)) = 1 / j := by
      have : (1 + c) ≠ 0 := by linarith
      have : (j : ℝ) ≠ 0 := by linarith
      field_simp
    linarith

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Apply `prod_le_prod_of_subset_of_one_le` to reduce the goal to its premises. Introduce `j hj`. Take `⟨s, hs, rfl⟩` from `mem_image.mp hj`. Conclude with `mem_range.mpr (hmap s hs)`.

Introduce `j _`. Conclude with `le_trans zero_le_one (hw j)`. Introduce `j _ _`. Conclude with `hw j`.
-/
theorem prod_le_prod_range_of_rank (A : Finset ℕ) (F : ℕ → ℝ) (φ : ℕ → ℕ) (w : ℕ → ℝ) (k : ℕ)
    (hF0 : ∀ s ∈ A, 0 ≤ F s) (hF : ∀ s ∈ A, F s ≤ w (φ s)) (hinj : Set.InjOn φ A)
    (hmap : ∀ s ∈ A, φ s < k) (hw : ∀ j, 1 ≤ w j) :
    ∏ s ∈ A, F s ≤ ∏ j ∈ range k, w j := by
  classical
  calc ∏ s ∈ A, F s ≤ ∏ s ∈ A, w (φ s) := prod_le_prod hF0 hF
    _ = ∏ j ∈ A.image φ, w j := (prod_image hinj).symm
    _ ≤ ∏ j ∈ range k, w j := by
      apply prod_le_prod_of_subset_of_one_le
      · intro j hj
        obtain ⟨s, hs, rfl⟩ := mem_image.mp hj
        exact mem_range.mpr (hmap s hs)
      · intro j _
        exact le_trans zero_le_one (hw j)
      · intro j _ _
        exact hw j

/- English proof (translation)
Introduce `s' hss'`. Proceed by induction on `s', hss' using Nat.le_induction with`. Consider the case `base => intro _`. Simplify using the standard rewrite rules. Consider the case `succ n hn ih`.

Introduce `hn1`. Establish `h1` using `hgap n (by omega) hn1`. Establish `h2` using `ih (by omega)`. Establish `h3 : (((n + 1 : ℕ) : ℝ) - s) * g = ((n : ℝ) - s) * g + g` using `by push_cast; ring`. Rewrite using `[h3]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cloud_gap_sum (k : ℕ) (lam : ℕ → ℝ) (g : ℝ)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s) (s : ℕ) (hs : 1 ≤ s) :
    ∀ s', s ≤ s' → s' ≤ k - 1 → lam s' + ((s' : ℝ) - s) * g ≤ lam s := by
  intro s' hss'
  induction s', hss' using Nat.le_induction with
  | base => intro _; simp
  | succ n hn ih =>
    intro hn1
    have h1 := hgap n (by omega) hn1
    have h2 := ih (by omega)
    have h3 : (((n + 1 : ℕ) : ℝ) - s) * g = ((n : ℝ) - s) * g + g := by push_cast; ring
    rw [h3]
    linarith

/- English proof (translation)
Establish `hF0 : ∀ s, 0 ≤ 1 + (1 + c) / max |Y + lam s| 1` using `fun s => by`. Establish `: 0 ≤ (1 + c) / max |Y + lam s| 1` using `div_nonneg (by linarith) (le_trans zero_le_one (le_max_right _ _))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hw : ∀ j : ℕ, 1 ≤ (if j = 0 then 2 + c else 1 + 1 / (j : ℝ))` using `fun j => by split_ifs`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: (0 : ℝ) ≤ 1 / (j : ℝ)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkR : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hW : ∏ j ∈ range k, (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) = (2 + c) * k`. Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`.

Rewrite using `[cloud_weight_prod]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hone : (1 : ℝ) ≤ (2 + c) * k` using `by nlinarith`. Rewrite using `[← prod_filter_mul_prod_filter_not (Icc 1 (k - 1)) (fun s => 0 < Y + lam s)]`.

Establish `hL : ∏ s ∈ (Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s), (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) * k`. Distinguish the cases in `hne : ((Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s)).Nonempty`. Establish `ht` using `max'_mem _ hne set t := ((Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s)).max' hne with ht_def`. Rewrite `ht` using `[mem_filter, mem_Icc]`. Rewrite using `[← hW]`.

Apply `prod_le_prod_range_of_rank _ _ (fun s => t - s) _ k (fun s _ => hF0 s) _ _ _ hw` to reduce the goal to its premises. Introduce `s hs`. Establish `hst : s ≤ t` using `le_max' _ _ hs`. Rewrite `hs` using `[mem_filter, mem_Icc]`. Apply `cloud_factor_le c g _ _ hc hg` to reduce the goal to its premises.

Establish `h1` using `cloud_gap_sum k lam g hgap s hs.1.1 t hst ht.1.2`. Establish `h2` using `le_abs_self (Y + lam s)`. Use `show (((t - s : ℕ) : ℝ)) * g ≤ |Y + lam s|`. Rewrite using `[Nat.cast_sub hst]`. Combine the linear relations using `[ht.2]`.

Introduce `a ha b hb hab`. Establish `ha' : a ≤ t` using `le_max' _ _ (mem_coe.mp ha)`. Establish `hb' : b ≤ t` using `le_max' _ _ (mem_coe.mp hb)`. Simplify using `only at hab`. Use linear arithmetic over natural numbers and integers.

Introduce `s hs`. Establish `hst : s ≤ t` using `le_max' _ _ hs`. Use `show t - s < k`. Use linear arithmetic over natural numbers and integers. Rewrite using `[not_nonempty_iff_eq_empty.mp hne, prod_empty]`.

Conclude with `hone`. Establish `hR : ∏ s ∈ (Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s), (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) * k`. Distinguish the cases in `hne : ((Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s)).Nonempty`. Establish `hu` using `min'_mem _ hne set u := ((Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s)).min' hne with hu_def`. Rewrite `hu` using `[mem_filter, mem_Icc]`.

Rewrite using `[← hW]`. Apply `prod_le_prod_range_of_rank _ _ (fun s => s - u) _ k (fun s _ => hF0 s) _ _ _ hw` to reduce the goal to its premises. Introduce `s hs`. Establish `hus : u ≤ s` using `min'_le _ _ hs`. Rewrite `hs` using `[mem_filter, mem_Icc]`.

Apply `cloud_factor_le c g _ _ hc hg` to reduce the goal to its premises. Establish `h1` using `cloud_gap_sum k lam g hgap u hu.1.1 s hus hs.1.2`. Establish `h2` using `neg_le_abs (Y + lam s)`. Use `show (((s - u : ℕ) : ℝ)) * g ≤ |Y + lam s|`. Rewrite using `[Nat.cast_sub hus]`.

Use `not_lt.mp hu.2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `a ha b hb hab`. Establish `ha' : u ≤ a` using `min'_le _ _ (mem_coe.mp ha)`. Establish `hb' : u ≤ b` using `min'_le _ _ (mem_coe.mp hb)`.

Simplify using `only at hab`. Use linear arithmetic over natural numbers and integers. Introduce `s hs`. Establish `hus : u ≤ s` using `min'_le _ _ hs`. Rewrite `hs` using `[mem_filter, mem_Icc]`.

Use `show s - u < k`. Use linear arithmetic over natural numbers and integers. Rewrite using `[not_nonempty_iff_eq_empty.mp hne, prod_empty]`. Conclude with `hone`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cloud_prod_le (k : ℕ) (lam : ℕ → ℝ) (c g Y : ℝ) (hk : 1 ≤ k) (hc : 0 ≤ c) (hg : 1 + c ≤ g)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s) :
    ∏ s ∈ Icc 1 (k - 1), (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) ^ 2 * (k : ℝ) ^ 2 := by
  classical
  have hF0 : ∀ s, 0 ≤ 1 + (1 + c) / max |Y + lam s| 1 := fun s => by
    have : 0 ≤ (1 + c) / max |Y + lam s| 1 :=
      div_nonneg (by linarith) (le_trans zero_le_one (le_max_right _ _))
    linarith
  have hw : ∀ j : ℕ, 1 ≤ (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) := fun j => by
    split_ifs
    · linarith
    · have : (0 : ℝ) ≤ 1 / (j : ℝ) := by positivity
      linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hW : ∏ j ∈ range k, (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) = (2 + c) * k := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [cloud_weight_prod]
    push_cast
    ring
  have hone : (1 : ℝ) ≤ (2 + c) * k := by nlinarith
  rw [← prod_filter_mul_prod_filter_not (Icc 1 (k - 1)) (fun s => 0 < Y + lam s)]
  have hL : ∏ s ∈ (Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s),
      (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) * k := by
    by_cases hne : ((Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s)).Nonempty
    · have ht := max'_mem _ hne
      set t := ((Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s)).max' hne with ht_def
      rw [mem_filter, mem_Icc] at ht
      rw [← hW]
      apply prod_le_prod_range_of_rank _ _ (fun s => t - s) _ k (fun s _ => hF0 s) _ _ _ hw
      · intro s hs
        have hst : s ≤ t := le_max' _ _ hs
        rw [mem_filter, mem_Icc] at hs
        apply cloud_factor_le c g _ _ hc hg
        have h1 := cloud_gap_sum k lam g hgap s hs.1.1 t hst ht.1.2
        have h2 := le_abs_self (Y + lam s)
        show (((t - s : ℕ) : ℝ)) * g ≤ |Y + lam s|
        rw [Nat.cast_sub hst]
        linarith [ht.2]
      · intro a ha b hb hab
        have ha' : a ≤ t := le_max' _ _ (mem_coe.mp ha)
        have hb' : b ≤ t := le_max' _ _ (mem_coe.mp hb)
        simp only at hab
        omega
      · intro s hs
        have hst : s ≤ t := le_max' _ _ hs
        show t - s < k
        omega
    · rw [not_nonempty_iff_eq_empty.mp hne, prod_empty]
      exact hone
  have hR : ∏ s ∈ (Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s),
      (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) * k := by
    by_cases hne : ((Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s)).Nonempty
    · have hu := min'_mem _ hne
      set u := ((Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s)).min' hne with hu_def
      rw [mem_filter, mem_Icc] at hu
      rw [← hW]
      apply prod_le_prod_range_of_rank _ _ (fun s => s - u) _ k (fun s _ => hF0 s) _ _ _ hw
      · intro s hs
        have hus : u ≤ s := min'_le _ _ hs
        rw [mem_filter, mem_Icc] at hs
        apply cloud_factor_le c g _ _ hc hg
        have h1 := cloud_gap_sum k lam g hgap u hu.1.1 s hus hs.1.2
        have h2 := neg_le_abs (Y + lam s)
        show (((s - u : ℕ) : ℝ)) * g ≤ |Y + lam s|
        rw [Nat.cast_sub hus]
        have := not_lt.mp hu.2
        linarith
      · intro a ha b hb hab
        have ha' : u ≤ a := min'_le _ _ (mem_coe.mp ha)
        have hb' : u ≤ b := min'_le _ _ (mem_coe.mp hb)
        simp only at hab
        omega
      · intro s hs
        have hus : u ≤ s := min'_le _ _ hs
        rw [mem_filter, mem_Icc] at hs
        show s - u < k
        omega
    · rw [not_nonempty_iff_eq_empty.mp hne, prod_empty]
      exact hone
  calc _ ≤ ((2 + c) * k) * ((2 + c) * k) :=
        mul_le_mul hL hR (prod_nonneg fun s _ => hF0 s) (by linarith)
    _ = (2 + c) ^ 2 * (k : ℝ) ^ 2 := by ring

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
