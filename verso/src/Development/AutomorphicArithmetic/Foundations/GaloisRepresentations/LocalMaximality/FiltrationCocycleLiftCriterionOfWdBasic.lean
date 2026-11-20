import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section SlopeTestRemainingChoices
variable {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]

/- English proof (translation)
Simplify using `[wd, LinearMap.pi_apply, LinearMap.sum_apply]`.
-/
private lemma wd_apply' (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]

/- English proof (translation)
Simplify using `[acx, Submodule.mem_pi]`.
-/
private lemma mem_acxC {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E} {n : ℤ}
    {c : Finset σ → E} :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) := by
  simp [acx, Submodule.mem_pi]

/- English proof (translation)
Rewrite `hc`, the goal using `[mem_acxC]`. Introduce `s`. Rewrite using `[wd_apply']`. Distinguish the cases in `hs : (s.card : ℤ) = n + 1`. Rewrite using `[if_pos hs]`.

Use `Submodule.sum_mem _ fun i hi => Submodule.smul_of_tower_mem _ _ ?_` and prove the remaining obligations. Establish `hcard : ((s.erase i).card : ℤ) = n`. Use `Finset.card_erase_add_one hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hmem` using `hc (s.erase i)`.

Rewrite `hmem` using `[if_pos hcard]`. Unfold `wOn`. Use `split_ifs`. Use `h.2 (s.erase i) i (by simp) _ hmem` as an intermediate fact. Rewrite `this` using `[Finset.insert_erase hi]`. Then use the resulting hypothesis.

Rewrite using `[LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[if_neg hs, Submodule.mem_bot]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `hcard : ¬ ((s.erase i).card : ℤ) = n`.

Use `Finset.card_erase_add_one hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hmem` using `hc (s.erase i)`. Rewrite `hmem` using `[if_neg hcard, Submodule.mem_bot]`. Rewrite using `[hmem, map_zero, smul_zero]`.
-/
private lemma wd_wOn_mem {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    (h : WOk A w) (P : Finset σ) {n : ℤ} {c : Finset σ → E} (hc : c ∈ (acx A w).C n) :
    wd (wOn P w) c ∈ (acx A w).C (n + 1) := by
  rw [mem_acxC] at hc ⊢
  intro s
  rw [wd_apply']
  by_cases hs : (s.card : ℤ) = n + 1
  · rw [if_pos hs]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_of_tower_mem _ _ ?_
    have hcard : ((s.erase i).card : ℤ) = n := by
      have := Finset.card_erase_add_one hi
      omega
    have hmem := hc (s.erase i)
    rw [if_pos hcard] at hmem
    unfold wOn
    split_ifs
    · have := h.2 (s.erase i) i (by simp) _ hmem
      rwa [Finset.insert_erase hi] at this
    · rw [LinearMap.zero_apply]
      exact Submodule.zero_mem _
  · rw [if_neg hs, Submodule.mem_bot]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : ¬ ((s.erase i).card : ℤ) = n := by
      have := Finset.card_erase_add_one hi
      omega
    have hmem := hc (s.erase i)
    rw [if_neg hcard, Submodule.mem_bot] at hmem
    rw [hmem, map_zero, smul_zero]

/- English proof (translation)
Introduce `s hs`. Rewrite using `[wd_apply']`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Unfold `wOn`. Use `split_ifs with hiQ`.

Rewrite `hiQ` using `[Finset.mem_compl]`. Establish `hQ : (s.erase i) ∩ Q = s ∩ Q`. Use extensionality with `x`. Simplify using `only [Finset.mem_inter, Finset.mem_erase]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨_, hx⟩, hxQ⟩`. Conclude with `⟨hx, hxQ⟩`. Introduce and unpack `⟨hx, hxQ⟩`. Conclude with `⟨⟨fun hxi => hiQ (by rw [← hxi]; exact hxQ), hx⟩, hxQ⟩`. Rewrite using `[h (s.erase i) (by rw [hQ]; exact hs), map_zero, smul_zero]`.

Rewrite using `[LinearMap.zero_apply, smul_zero]`.
-/
private lemma wd_compl_lev [Fintype σ] {Q : Finset σ} {w : σ → Module.End ℂ E} {m : ℤ}
    {c : Finset σ → E} (h : Lev Q (· = m) c) : Lev Q (· = m) (wd (wOn Qᶜ w) c) := by
  intro s hs
  rw [wd_apply']
  refine Finset.sum_eq_zero fun i hi => ?_
  unfold wOn
  split_ifs with hiQ
  · rw [Finset.mem_compl] at hiQ
    have hQ : (s.erase i) ∩ Q = s ∩ Q := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hx⟩, hxQ⟩
        exact ⟨hx, hxQ⟩
      · rintro ⟨hx, hxQ⟩
        exact ⟨⟨fun hxi => hiQ (by rw [← hxi]; exact hxQ), hx⟩, hxQ⟩
    rw [h (s.erase i) (by rw [hQ]; exact hs), map_zero, smul_zero]
  · rw [LinearMap.zero_apply, smul_zero]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce and unpack `hB σ E _ _ _ _ A w Q d n hW hQE c0 hc0 hl0 hq0 ⟨y, hy, hly, hdy⟩`. Establish `hcw : ∀ P P' : Finset σ, ∀ i j, Commute (wOn P w i) (wOn P' w j)`. Introduce `P P' i j`. Unfold `wOn`. Use `split_ifs`.

Apply the tactic sequence `all_goals first`. Consider the case `exact hW.1 i j`. Consider the case `exact Commute.zero_right _`. Consider the case `exact Commute.zero_left _`. Establish `hsplit : ∀ x, wd w x = wd (wOn Q w) x + wd (wOn Qᶜ w) x`.

Introduce `x`. Establish `hw : w = wOn Q w + wOn Qᶜ w`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases hi : i ∈ Q <;> simp [wOn, hi]`. Use `conv_lhs => rw [hw]`.

Rewrite using `[(hB σ E A (wOn Q w)).2.2.1 (wOn Qᶜ w), LinearMap.add_apply]`. Establish `hRR : ∀ x, wd (wOn Qᶜ w) (wd (wOn Qᶜ w) x) = 0` using `(hB σ E A (wOn Qᶜ w)).1 (hcw Qᶜ Qᶜ)`. Apply the tactic sequence `have hQR : ∀ x, wd (wOn Q w) (wd (wOn Qᶜ w) x) + wd (wOn Qᶜ w) (wd (wOn Q w) x) = 0 := (hB σ E A (wOn Q w)).2.2.2.1 (wOn Qᶜ w) (hcw Q Qᶜ) (fun i => by by_cases hi : i ∈ Q <;> simp [wOn, hi])`. Establish `levZero : ∀ (m : ℤ) (x : Finset σ → E), m < 0 → Lev Q (· = m) x → x = 0`. Introduce `m x hm hx`.

Use function extensionality and compare the values at `s`. Conclude with `hx s (fun h => by`. Establish `h' : (((s ∩ Q).card : ℕ) : ℤ) = m` using `h`. Use the proof step `omega)`. Establish `key : ∀ j : ℕ, ∀ m : ℤ, m < j → m < d → ∀ ck yk : Finset σ → E, ck ∈ (acx A w).C n → Lev Q (· < d) (ck - c0) → yk ∈ (acx A w).C n → Lev Q (· = m) yk → wd w ck = -wd (wOn Qᶜ w) yk → wd (wOn Q w) (wd (wOn Qᶜ w) yk) = 0 → ∃ c ∈ (acx A w).Z n, Lev Q (· < d) (c - c0)`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `m hm _ ck yk hck hlk _ hly hd _`. Establish `hy0` using `levZero m yk (by exact_mod_cast hm) hly`.

Use `⟨ck, ?_, hlk⟩` and prove the remaining obligations. Use `show ck ∈ (acx A w).C n ⊓ LinearMap.ker (acx A w).D`. Use `Submodule.mem_inf.2 ⟨hck, LinearMap.mem_ker.2 ?_⟩` and prove the remaining obligations. Use `show wd w ck = 0`. Rewrite using `[hd, hy0, map_zero, neg_zero]`.

Consider the case `succ j ih`. Introduce `m hm hmd ck yk hck hlk hyk hly hd hqr`. Establish `hmem : -wd (wOn Qᶜ w) yk ∈ (acx A w).C (n + 1)` using `Submodule.neg_mem _ (wd_wOn_mem hW Qᶜ hyk)`. Establish `hlev : Lev Q (· = m) (-wd (wOn Qᶜ w) yk)`. Introduce `s hs`.

Rewrite using `[Pi.neg_apply, wd_compl_lev hly s hs, neg_zero]`. Establish `hdq : wd (wOn Q w) (-wd (wOn Qᶜ w) yk) = 0` using `by rw [map_neg, hqr, neg_zero]`. Take `⟨y', hy', hly', hdy'⟩` from `hQE (n + 1) m hmd _ hmem hlev hdq`. Rewrite `hy'` using `[add_sub_cancel_right]`. Use `ih (m - 1) (by push_cast at hm; omega) (by omega) (ck - y') y' (Submodule.sub_mem _ hck hy') ?_ hy' hly' ?_ ?_` and prove the remaining obligations.

Introduce `s hs`. Establish `h1` using `hlk s hs`. Establish `h2` using `hly' s (fun h => hs (by`. Establish `h' : (((s ∩ Q).card : ℕ) : ℤ) = m - 1` using `h`. Use `show (((s ∩ Q).card : ℕ) : ℤ) < d`.

Use the proof step `omega))`. Simplify using `only [Pi.sub_apply] at h1 ⊢`. Rewrite using `[h2, sub_zero]`. Conclude with `h1`. Rewrite using `[map_sub, hd, hsplit y', hdy']`.

Normalize the expressions using the abelian group laws. Use `hQR y'` as an intermediate fact. Rewrite `this` using `[hdy', map_neg, hRR, neg_zero, add_zero]`. Conclude with `this`. Use `key d.toNat (d - 1) (by have := Int.self_le_toNat d; omega) (by omega) (c0 - y) y (Submodule.sub_mem _ hc0 hy) ?_ hy hly ?_ ?_` and prove the remaining obligations.

Introduce `s hs`. Establish `h2` using `hly s (fun h => hs (by`. Establish `h' : (((s ∩ Q).card : ℕ) : ℤ) = d - 1` using `h`. Use `show (((s ∩ Q).card : ℕ) : ℤ) < d`. Use the proof step `omega))`.

Simplify using `only [Pi.sub_apply]`. Rewrite using `[h2]`. Normalize the expressions using the abelian group laws. Rewrite using `[map_sub, hsplit c0, hsplit y, hq0, hdy]`. Normalize the expressions using the abelian group laws.

Use `hQR y` as an intermediate fact. Rewrite `this` using `[hdy, hRR, add_zero]`. Conclude with `this`.
-/
theorem UpperTheory.Gal.productCup_of_system.filtrationCocycleLiftCriterion_of_wdBasic :
    WdBasic → FiltrationCocycleLiftCriterion := by
  rintro hB σ E _ _ _ _ A w Q d n hW hQE c0 hc0 hl0 hq0 ⟨y, hy, hly, hdy⟩
  have hcw : ∀ P P' : Finset σ, ∀ i j, Commute (wOn P w i) (wOn P' w j) := by
    intro P P' i j
    unfold wOn
    split_ifs
    all_goals first
      | exact hW.1 i j
      | exact Commute.zero_right _
      | exact Commute.zero_left _
  have hsplit : ∀ x, wd w x = wd (wOn Q w) x + wd (wOn Qᶜ w) x := by
    intro x
    have hw : w = wOn Q w + wOn Qᶜ w := by
      funext i
      by_cases hi : i ∈ Q <;> simp [wOn, hi]
    conv_lhs => rw [hw]
    rw [(hB σ E A (wOn Q w)).2.2.1 (wOn Qᶜ w), LinearMap.add_apply]
  have hRR : ∀ x, wd (wOn Qᶜ w) (wd (wOn Qᶜ w) x) = 0 := (hB σ E A (wOn Qᶜ w)).1 (hcw Qᶜ Qᶜ)
  have hQR : ∀ x, wd (wOn Q w) (wd (wOn Qᶜ w) x) + wd (wOn Qᶜ w) (wd (wOn Q w) x) = 0 :=
    (hB σ E A (wOn Q w)).2.2.2.1 (wOn Qᶜ w) (hcw Q Qᶜ) (fun i => by by_cases hi : i ∈ Q <;> simp [wOn, hi])
  have levZero : ∀ (m : ℤ) (x : Finset σ → E), m < 0 → Lev Q (· = m) x → x = 0 := by
    intro m x hm hx
    funext s
    exact hx s (fun h => by
      have h' : (((s ∩ Q).card : ℕ) : ℤ) = m := h
      omega)
  have key : ∀ j : ℕ, ∀ m : ℤ, m < j → m < d → ∀ ck yk : Finset σ → E,
      ck ∈ (acx A w).C n → Lev Q (· < d) (ck - c0) → yk ∈ (acx A w).C n → Lev Q (· = m) yk →
      wd w ck = -wd (wOn Qᶜ w) yk → wd (wOn Q w) (wd (wOn Qᶜ w) yk) = 0 →
      ∃ c ∈ (acx A w).Z n, Lev Q (· < d) (c - c0) := by
    intro j
    induction j with
    | zero =>
      intro m hm _ ck yk hck hlk _ hly hd _
      have hy0 := levZero m yk (by exact_mod_cast hm) hly
      refine ⟨ck, ?_, hlk⟩
      show ck ∈ (acx A w).C n ⊓ LinearMap.ker (acx A w).D
      refine Submodule.mem_inf.2 ⟨hck, LinearMap.mem_ker.2 ?_⟩
      show wd w ck = 0
      rw [hd, hy0, map_zero, neg_zero]
    | succ j ih =>
      intro m hm hmd ck yk hck hlk hyk hly hd hqr
      have hmem : -wd (wOn Qᶜ w) yk ∈ (acx A w).C (n + 1) :=
        Submodule.neg_mem _ (wd_wOn_mem hW Qᶜ hyk)
      have hlev : Lev Q (· = m) (-wd (wOn Qᶜ w) yk) := by
        intro s hs
        rw [Pi.neg_apply, wd_compl_lev hly s hs, neg_zero]
      have hdq : wd (wOn Q w) (-wd (wOn Qᶜ w) yk) = 0 := by rw [map_neg, hqr, neg_zero]
      obtain ⟨y', hy', hly', hdy'⟩ := hQE (n + 1) m hmd _ hmem hlev hdq
      rw [add_sub_cancel_right] at hy'
      refine ih (m - 1) (by push_cast at hm; omega) (by omega) (ck - y') y'
        (Submodule.sub_mem _ hck hy') ?_ hy' hly' ?_ ?_
      · intro s hs
        have h1 := hlk s hs
        have h2 := hly' s (fun h => hs (by
          have h' : (((s ∩ Q).card : ℕ) : ℤ) = m - 1 := h
          show (((s ∩ Q).card : ℕ) : ℤ) < d
          omega))
        simp only [Pi.sub_apply] at h1 ⊢
        rw [h2, sub_zero]
        exact h1
      · rw [map_sub, hd, hsplit y', hdy']
        abel
      · have := hQR y'
        rw [hdy', map_neg, hRR, neg_zero, add_zero] at this
        exact this
  refine key d.toNat (d - 1) (by have := Int.self_le_toNat d; omega) (by omega) (c0 - y) y
    (Submodule.sub_mem _ hc0 hy) ?_ hy hly ?_ ?_
  · intro s hs
    have h2 := hly s (fun h => hs (by
      have h' : (((s ∩ Q).card : ℕ) : ℤ) = d - 1 := h
      show (((s ∩ Q).card : ℕ) : ℤ) < d
      omega))
    simp only [Pi.sub_apply]
    rw [h2]
    abel
  · rw [map_sub, hsplit c0, hsplit y, hq0, hdy]
    abel
  · have := hQR y
    rw [hdy, hRR, add_zero] at this
    exact this
