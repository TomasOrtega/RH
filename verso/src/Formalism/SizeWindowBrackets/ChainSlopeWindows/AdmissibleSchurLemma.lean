import Formalism.SizeWindowBrackets.SecondKindBucket
import Formalism.LogFactorialBounds.LogFactorialProofs.PrimeSum
import Formalism.RankGapBounds.RankGapProofs.RankGapDecayHypothesis
import Formalism.RankGapBounds.RankGapProofs.PmModulusFacts
import Formalism.RankGapBounds.RankGapProofs.FourNotDvdOddSqAddOne

namespace Formalism.LFunctionChainParameters.DeficitSplitLemmas

open Finset Classical

noncomputable section

/- English proof (translation)
Unfold `GaW`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not W (fun w => below w ∈ Ps)]`. Establish `hoff : ∑ w ∈ W.filter (fun w => ¬ below w ∈ Ps), l w * ((∑ j ∈ J, gainW j w) - tauW w) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `w hw`.

Rewrite `hw` using `[Finset.mem_filter]`. Take `⟨hg, ht⟩` from `h.offPs w hw.1 hw.2`. Rewrite using `[Finset.sum_eq_zero hg, ht]`. Expand and normalize the polynomial expressions, which then agree. Establish `hon : ∑ w ∈ W.filter (fun w => below w ∈ Ps), l w * ((∑ j ∈ J, gainW j w) - tauW w) = ∑ w ∈ W.filter (fun w => below w ∈ Ps), l w * ((∑ j ∈ J, gain j (below w)) - tau (below w))`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w hw`. Rewrite `hw` using `[Finset.mem_filter]`. Take `⟨hg, ht⟩` from `h.onPs w hw.1 hw.2`. Rewrite using `[Finset.sum_congr rfl hg, ht]`.

Establish `hfib` using `Finset.sum_fiberwise_of_maps_to (s := W.filter (fun w => below w ∈ Ps)) (t := Ps) (g := below) (fun w hw => (Finset.mem_filter.1 hw).2) (fun w => l w * ((∑ j ∈ J, gain j (below w)) - tau (below w)))`. Rewrite using `[hoff, add_zero, hon, ← hfib, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p hp`. Establish `hset : (W.filter (fun w => below w ∈ Ps)).filter (fun w => below w = p) = W.filter (fun w => below w = p)`.

Use extensionality with `w`. Simplify using `only [Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hw, _⟩, he⟩`. Conclude with `⟨hw, he⟩`.

Introduce and unpack `⟨hw, he⟩`. Conclude with `⟨⟨hw, he ▸ hp⟩, he⟩`. Rewrite using `[hset]`. Establish `hc : ∑ w ∈ W.filter (fun w => below w = p), l w * ((∑ j ∈ J, gain j (below w)) - tau (below w)) = ∑ w ∈ W.filter (fun w => below w = p), l w * ((∑ j ∈ J, gain j p) - tau p)`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `w hw`. Rewrite using `[(Finset.mem_filter.1 hw).2]`. Rewrite using `[hc, ← Finset.sum_mul, h.unit p hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ga_eq {ι κ : Type*} (W : Finset ι) (below : ι → ℕ) (l : ι → ℝ) (Ps : Finset ℕ)
    (J : Finset κ) (gainW : κ → ι → ℝ) (tauW : ι → ℝ) (gain : κ → ℕ → ℝ) (tau : ℕ → ℝ)
    (h : UnitRule W below l Ps J gainW tauW gain tau) :
    GaW W J l gainW tauW = ∑ p ∈ Ps, 2 * Real.log p * ((∑ j ∈ J, gain j p) - tau p) := by
  unfold GaW
  rw [← Finset.sum_filter_add_sum_filter_not W (fun w => below w ∈ Ps)]
  have hoff : ∑ w ∈ W.filter (fun w => ¬ below w ∈ Ps), l w * ((∑ j ∈ J, gainW j w) - tauW w) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hg, ht⟩ := h.offPs w hw.1 hw.2
    rw [Finset.sum_eq_zero hg, ht]; ring
  have hon : ∑ w ∈ W.filter (fun w => below w ∈ Ps), l w * ((∑ j ∈ J, gainW j w) - tauW w)
      = ∑ w ∈ W.filter (fun w => below w ∈ Ps),
          l w * ((∑ j ∈ J, gain j (below w)) - tau (below w)) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hg, ht⟩ := h.onPs w hw.1 hw.2
    rw [Finset.sum_congr rfl hg, ht]
  have hfib := Finset.sum_fiberwise_of_maps_to (s := W.filter (fun w => below w ∈ Ps)) (t := Ps)
      (g := below) (fun w hw => (Finset.mem_filter.1 hw).2)
      (fun w => l w * ((∑ j ∈ J, gain j (below w)) - tau (below w)))
  rw [hoff, add_zero, hon, ← hfib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hset : (W.filter (fun w => below w ∈ Ps)).filter (fun w => below w = p) =
      W.filter (fun w => below w = p) := by
    ext w; simp only [Finset.mem_filter]; constructor
    · rintro ⟨⟨hw, _⟩, he⟩; exact ⟨hw, he⟩
    · rintro ⟨hw, he⟩; exact ⟨⟨hw, he ▸ hp⟩, he⟩
  rw [hset]
  have hc : ∑ w ∈ W.filter (fun w => below w = p),
      l w * ((∑ j ∈ J, gain j (below w)) - tau (below w)) =
      ∑ w ∈ W.filter (fun w => below w = p), l w * ((∑ j ∈ J, gain j p) - tau p) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [(Finset.mem_filter.1 hw).2]
  rw [hc, ← Finset.sum_mul, h.unit p hp]; ring

/- English proof (translation)
Unfold `ASK`. Simplify using `only [Finset.sum_add_distrib, Finset.mul_sum]`. Use `congr 1`. Rewrite using `[Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]`. Conclude with `Finset.sum_comm`.
-/
theorem ask_eq {κ τ : Type*} (Ps : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (vonMangoldtClassSum : κ → τ → ℕ → ℝ) (dT : κ → τ → ℝ) :
    ASK Ps J TT vonMangoldtClassSum dT = (∑ p ∈ Ps, 2 * Real.log p * ∑ j ∈ J, ∑ t ∈ TT, vonMangoldtClassSum j t p) +
      ∑ j ∈ J, ∑ t ∈ TT, dT j t := by
  unfold ASK
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  exact Finset.sum_comm

/- English proof (translation)
Introduce `ι κ τ W below l Ps J TT vonMangoldtClassSum dT gainW tauW gain tau h`. Rewrite using `[ask_eq, ga_eq W below l Ps J gainW tauW gain tau h]`. Unfold `deficit`. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem splitEq_valid : SplitEq := by
  intro ι κ τ W below l Ps J TT vonMangoldtClassSum dT gainW tauW gain tau h
  rw [ask_eq, ga_eq W below l Ps J gainW tauW gain tau h]
  unfold deficit
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/- English proof (translation)
Take `⟨hsub, hled⟩` from `h`. Unfold `deficit servedLoss`. Establish `h1 : ∑ j ∈ J, ∑ t ∈ TT, vonMangoldtClassSum j t p = ∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p + ∑ j ∈ J, ∑ t ∈ TTp p, vonMangoldtClassSum j t p`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl (fun j _ => (Finset.sum_sdiff hsub).symm)`.

Establish `h2 : ∑ j ∈ J, ∑ t ∈ TTp p, (vonMangoldtClassSum j t p - lo p) = ∑ j ∈ J, ∑ t ∈ TTp p, vonMangoldtClassSum j t p - (J.card : ℝ) * (TTp p).card * lo p`. Simplify using `only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Rewrite `hled` using `[h2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deficit_le {κ τ : Type*} (J : Finset κ) (TT : Finset τ) (TTp : ℕ → Finset τ)
    (vonMangoldtClassSum : κ → τ → ℕ → ℝ) (gain : κ → ℕ → ℝ) (tau lo fl : ℕ → ℝ) (p : ℕ)
    (h : SizeData₂ J TT TTp vonMangoldtClassSum gain tau lo fl p) :
    deficit J TT vonMangoldtClassSum gain tau p ≤ servedLoss J TT TTp vonMangoldtClassSum lo fl p := by
  obtain ⟨hsub, hled⟩ := h
  unfold deficit servedLoss
  have h1 : ∑ j ∈ J, ∑ t ∈ TT, vonMangoldtClassSum j t p =
      ∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p + ∑ j ∈ J, ∑ t ∈ TTp p, vonMangoldtClassSum j t p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => (Finset.sum_sdiff hsub).symm)
  have h2 : ∑ j ∈ J, ∑ t ∈ TTp p, (vonMangoldtClassSum j t p - lo p) =
      ∑ j ∈ J, ∑ t ∈ TTp p, vonMangoldtClassSum j t p - (J.card : ℝ) * (TTp p).card * lo p := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  rw [h1]
  rw [h2] at hled
  linarith

/- English proof (translation)
Unfold `deficit wholeAsk`. Rewrite using `[Finset.sum_eq_zero hg, ht]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deficit_dropped {κ τ : Type*} (J : Finset κ) (TT : Finset τ) (vonMangoldtClassSum : κ → τ → ℕ → ℝ)
    (gain : κ → ℕ → ℝ) (tau : ℕ → ℝ) (p : ℕ) (hg : ∀ j ∈ J, gain j p = 0) (ht : tau p = 0) :
    deficit J TT vonMangoldtClassSum gain tau p = wholeAsk J TT vonMangoldtClassSum p := by
  unfold deficit wholeAsk
  rw [Finset.sum_eq_zero hg, ht]; ring

/- English proof (translation)
Introduce `ι κ τ W below l Ps S J TT TTp vonMangoldtClassSum dT gainW tauW gain tau lo fl h hS hled hdrop`. Rewrite using `[splitEq_valid ι κ τ W below l Ps J TT vonMangoldtClassSum dT gainW tauW gain tau h, ← Finset.sum_sdiff hS]`. Establish `hA : ∑ p ∈ S, 2 * Real.log p * deficit J TT vonMangoldtClassSum gain tau p ≤ ∑ p ∈ S, 2 * Real.log p * servedLoss J TT TTp vonMangoldtClassSum lo fl p`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`.

Conclude with `mul_le_mul_of_nonneg_left (deficit_le J TT TTp vonMangoldtClassSum gain tau lo fl p (hled p hp)) (by have := Real.log_natCast_nonneg p; linarith)`. Establish `hB : ∑ p ∈ Ps \ S, 2 * Real.log p * deficit J TT vonMangoldtClassSum gain tau p = ∑ p ∈ Ps \ S, 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p hp`. Rewrite using `[deficit_dropped J TT vonMangoldtClassSum gain tau p (hdrop p hp).1 (hdrop p hp).2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem splitLe_valid : SplitLe := by
  intro ι κ τ W below l Ps S J TT TTp vonMangoldtClassSum dT gainW tauW gain tau lo fl h hS hled hdrop
  rw [splitEq_valid ι κ τ W below l Ps J TT vonMangoldtClassSum dT gainW tauW gain tau h,
    ← Finset.sum_sdiff hS]
  have hA : ∑ p ∈ S, 2 * Real.log p * deficit J TT vonMangoldtClassSum gain tau p ≤
      ∑ p ∈ S, 2 * Real.log p * servedLoss J TT TTp vonMangoldtClassSum lo fl p := by
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (deficit_le J TT TTp vonMangoldtClassSum gain tau lo fl p (hled p hp))
      (by have := Real.log_natCast_nonneg p; linarith)
  have hB : ∑ p ∈ Ps \ S, 2 * Real.log p * deficit J TT vonMangoldtClassSum gain tau p =
      ∑ p ∈ Ps \ S, 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [deficit_dropped J TT vonMangoldtClassSum gain tau p (hdrop p hp).1 (hdrop p hp).2]
  linarith

/- English proof (translation)
Introduce `ι κ τ W below l Ps cl J TT TTp vonMangoldtClassSum dT gainW tauW gain tau lo fl h hled hdrop`. Rewrite using `[splitEq_valid ι κ τ W below l Ps J TT vonMangoldtClassSum dT gainW tauW gain tau h]`. Simplify using `only [Finset.sum_filter]`. Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Establish `key : ∀ p ∈ Ps, 2 * Real.log p * deficit J TT vonMangoldtClassSum gain tau p ≤ ((if cl p = PClass.served then 2 * Real.log p * servedLoss J TT TTp vonMangoldtClassSum lo fl p else 0) + (if cl p = PClass.first then 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p else 0) + (if …`.

Introduce `p hp`. Establish `hl : 0 ≤ 2 * Real.log p` using `by have := Real.log_natCast_nonneg p; linarith`. Consider the cases of `hc : cl p with`. Consider the case `served`. Simplify using `only [if_true, if_false, reduceCtorEq, add_zero]`.

Conclude with `mul_le_mul_of_nonneg_left (deficit_le J TT TTp vonMangoldtClassSum gain tau lo fl p (hled p hp hc)) hl`. Consider the case `first`. Take `⟨hg, ht⟩` from `hdrop p hp (by simp [hc])`. Rewrite using `[deficit_dropped J TT vonMangoldtClassSum gain tau p hg ht]`. Simplify using the standard rewrite rules.

Consider the case `second`. Take `⟨hg, ht⟩` from `hdrop p hp (by simp [hc])`. Rewrite using `[deficit_dropped J TT vonMangoldtClassSum gain tau p hg ht]`. Simplify using the standard rewrite rules. Consider the case `high`.

Take `⟨hg, ht⟩` from `hdrop p hp (by simp [hc])`. Rewrite using `[deficit_dropped J TT vonMangoldtClassSum gain tau p hg ht]`. Simplify using the standard rewrite rules. Use `Finset.sum_le_sum key` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem split_classes_count : SplitClasses := by
  intro ι κ τ W below l Ps cl J TT TTp vonMangoldtClassSum dT gainW tauW gain tau lo fl h hled hdrop
  rw [splitEq_valid ι κ τ W below l Ps J TT vonMangoldtClassSum dT gainW tauW gain tau h]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key : ∀ p ∈ Ps, 2 * Real.log p * deficit J TT vonMangoldtClassSum gain tau p ≤
      ((if cl p = PClass.served then 2 * Real.log p * servedLoss J TT TTp vonMangoldtClassSum lo fl p else 0) +
      (if cl p = PClass.first then 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p else 0) +
      (if cl p = PClass.second then 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p else 0) +
      (if cl p = PClass.high then 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p else 0)) := by
    intro p hp
    have hl : 0 ≤ 2 * Real.log p := by have := Real.log_natCast_nonneg p; linarith
    cases hc : cl p with
    | served =>
      simp only [if_true, if_false, reduceCtorEq, add_zero]
      exact mul_le_mul_of_nonneg_left (deficit_le J TT TTp vonMangoldtClassSum gain tau lo fl p (hled p hp hc)) hl
    | first =>
      obtain ⟨hg, ht⟩ := hdrop p hp (by simp [hc])
      rw [deficit_dropped J TT vonMangoldtClassSum gain tau p hg ht]
      simp
    | second =>
      obtain ⟨hg, ht⟩ := hdrop p hp (by simp [hc])
      rw [deficit_dropped J TT vonMangoldtClassSum gain tau p hg ht]
      simp
    | high =>
      obtain ⟨hg, ht⟩ := hdrop p hp (by simp [hc])
      rw [deficit_dropped J TT vonMangoldtClassSum gain tau p hg ht]
      simp
  have := Finset.sum_le_sum key
  linarith

/- English proof (translation)
Introduce `Y s hY hs`. Establish `hN : 1 ≤ ⌊Y⌋₊` using `(Nat.one_le_floor_iff Y).mpr hY`. Establish `hsub : s ⊆ Nat.primesLE ⌊Y⌋₊`. Introduce `p hp`. Rewrite using `[Nat.mem_primesLE]`.

Conclude with `⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩`. Combine the equalities or inequalities in the displayed calculation. Establish `: Real.log (⌊Y⌋₊ : ℝ) ≤ Real.log Y` using `Real.log_le_log (by exact_mod_cast hN) (Nat.floor_le (by linarith))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem prime_log_sum_bound : PrimeLogSum := by
  intro Y s hY hs
  have hN : 1 ≤ ⌊Y⌋₊ := (Nat.one_le_floor_iff Y).mpr hY
  have hsub : s ⊆ Nat.primesLE ⌊Y⌋₊ := by
    intro p hp; rw [Nat.mem_primesLE]; exact ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
  calc ∑ p ∈ s, Real.log p / p ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    _ ≤ Real.log ⌊Y⌋₊ + Real.log 4 := Formalism.LogFactorialBounds.sum_primesLE_log_div_le _ hN
    _ ≤ Real.log Y + Real.log 4 := by
        have : Real.log (⌊Y⌋₊ : ℝ) ≤ Real.log Y :=
          Real.log_le_log (by exact_mod_cast hN) (Nat.floor_le (by linarith))
        linarith

/- English proof (translation)
Introduce `Y s hY hs`. Establish `hsub : s ⊆ Nat.primesLE ⌊Y⌋₊`. Introduce `p hp`. Rewrite using `[Nat.mem_primesLE]`. Conclude with `⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem theta_finite : ThetaFin := by
  intro Y s hY hs
  have hsub : s ⊆ Nat.primesLE ⌊Y⌋₊ := by
    intro p hp; rw [Nat.mem_primesLE]; exact ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
  calc ∑ p ∈ s, Real.log p ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
    _ = Chebyshev.theta (⌊Y⌋₊ : ℝ) := (Chebyshev.theta_eq_sum_primesLE_log _).symm
    _ ≤ Real.log 4 * (⌊Y⌋₊ : ℝ) := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
    _ ≤ Real.log 4 * Y :=
        mul_le_mul_of_nonneg_left (Nat.floor_le hY) (Real.log_nonneg (by norm_num))

def gT (y : ℝ) : ℝ := (Real.log y + 1) / y

/- English proof (translation)
Unfold `gT`. Establish `hy1 : 0 < y - 1` using `by linarith`. Establish `hy0 : 0 < y` using `by linarith`. Establish `hL1 : 1 ≤ Real.log y`. Rewrite using `[Real.le_log_iff_exp_le hy0]`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdiff : Real.log y - Real.log (y - 1) ≤ 1 / (y - 1)`. Rewrite using `[← Real.log_div hy0.ne' hy1.ne']`. Establish `h` using `Real.log_le_sub_one_of_pos (show 0 < y / (y - 1) by positivity)`.

Establish `e : y / (y - 1) - 1 = 1 / (y - 1)` using `by field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set L := Real.log y`. Use `set L1 := Real.log (y - 1)`. Establish `hD1 : (L - L1) * (y - 1) ≤ 1`.

Use `mul_le_mul_of_nonneg_right hdiff hy1.le` as an intermediate fact. Rewrite `this` using `[one_div, inv_mul_cancel₀ hy1.ne']`. Then use the resulting hypothesis. Establish `hD2 : L - L1 ≤ 1 / 2`. Establish `: 1 / (y - 1) ≤ 1 / 2`. Rewrite using `[div_le_div_iff₀ hy1 (by norm_num)]; linarith`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDy : y * (L - L1) ≤ 3 / 2` using `by nlinarith`. Establish `hG : L * (y - 1) ≤ 2 * y * (y * (L1 + 1) - (y - 1) * (L + 1))`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hDy hy0.le]`. Establish `e2 : 2 * ((L1 + 1) / (y - 1) - (L + 1) / y) = 2 * (y * (L1 + 1) - (y - 1) * (L + 1)) / (y * (y - 1))`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e2, div_le_div_iff₀ (by positivity) (by positivity)]`. Use `mul_le_mul_of_nonneg_left hG hy0.le` as an intermediate fact. Use polynomial arithmetic with `[this]`.
-/
lemma tail_step (y : ℝ) (hy : 3 ≤ y) : Real.log y / y ^ 2 ≤ 2 * (gT (y - 1) - gT y) := by
  unfold gT
  have hy1 : 0 < y - 1 := by linarith
  have hy0 : 0 < y := by linarith
  have hL1 : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]
    have := Real.exp_one_lt_d9; linarith
  have hdiff : Real.log y - Real.log (y - 1) ≤ 1 / (y - 1) := by
    rw [← Real.log_div hy0.ne' hy1.ne']
    have h := Real.log_le_sub_one_of_pos (show 0 < y / (y - 1) by positivity)
    have e : y / (y - 1) - 1 = 1 / (y - 1) := by field_simp; ring
    linarith
  set L := Real.log y
  set L1 := Real.log (y - 1)
  have hD1 : (L - L1) * (y - 1) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hdiff hy1.le
    rwa [one_div, inv_mul_cancel₀ hy1.ne'] at this
  have hD2 : L - L1 ≤ 1 / 2 := by
    have : 1 / (y - 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hy1 (by norm_num)]; linarith
    linarith
  have hDy : y * (L - L1) ≤ 3 / 2 := by nlinarith
  have hG : L * (y - 1) ≤ 2 * y * (y * (L1 + 1) - (y - 1) * (L + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_left hDy hy0.le]
  have e2 : 2 * ((L1 + 1) / (y - 1) - (L + 1) / y) =
      2 * (y * (L1 + 1) - (y - 1) * (L + 1)) / (y * (y - 1)) := by
    field_simp
  rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hG hy0.le
  nlinarith [this]

/- English proof (translation)
Unfold `gT`. Use `Real.log_nonneg hy` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma gT_nonneg (y : ℝ) (hy : 1 ≤ y) : 0 ≤ gT y := by
  unfold gT
  have := Real.log_nonneg hy
  positivity

/- English proof (translation)
Proceed by induction on `K with`. Consider the case `zero => simp`. Consider the case `succ K ih`. Rewrite using `[← add_assoc, Finset.sum_Ico_succ_top (by omega)]`. Establish `h3 : (3 : ℝ) ≤ ((p₀ + K : ℕ) : ℝ)`.

Establish `: 3 ≤ p₀ + K` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hs` using `tail_step ((p₀ + K : ℕ) : ℝ) h3`. Move the coercions through the operations in `at hs ⊢`. Establish `e : (p₀ : ℝ) + (K + 1) - 1 = p₀ + K` using `by ring`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma tail_Ico (p₀ : ℕ) (hp : 3 ≤ p₀) (K : ℕ) :
    ∑ n ∈ Finset.Ico p₀ (p₀ + K), Real.log n / (n : ℝ) ^ 2 ≤
      2 * (gT ((p₀ : ℝ) - 1) - gT ((p₀ : ℝ) + K - 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have h3 : (3 : ℝ) ≤ ((p₀ + K : ℕ) : ℝ) := by
      have : 3 ≤ p₀ + K := by omega
      exact_mod_cast this
    have hs := tail_step ((p₀ + K : ℕ) : ℝ) h3
    push_cast at hs ⊢
    have e : (p₀ : ℝ) + (K + 1) - 1 = p₀ + K := by ring
    rw [e]
    linarith

/- English proof (translation)
Introduce `p₀ s hp hs`. Establish `hsub : s ⊆ Finset.Ico p₀ (p₀ + (s.sup id + 1))`. Introduce `n hn`. Rewrite using `[Finset.mem_Ico]`. Establish `: n ≤ s.sup id` using `Finset.le_sup (f := id) hn`.

Conclude with `⟨hs n hn, by omega⟩`. Establish `h1 : ∑ n ∈ s, Real.log n / (n : ℝ) ^ 2 ≤ ∑ n ∈ Finset.Ico p₀ (p₀ + (s.sup id + 1)), Real.log n / (n : ℝ) ^ 2` using `Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => div_nonneg (Real.log_natCast_nonneg n) (by positivity))`. Establish `h2` using `tail_Ico p₀ hp (s.sup id + 1)`. Establish `hp' : (3 : ℝ) ≤ p₀` using `by exact_mod_cast hp`. Establish `h3 : 0 ≤ gT ((p₀ : ℝ) + ((s.sup id + 1 : ℕ) : ℝ) - 1)`.

Apply `gT_nonneg` to reduce the goal to its premises. Establish `: (0 : ℝ) ≤ ((s.sup id + 1 : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : 2 * (Real.log ((p₀ : ℝ) - 1) + 1) / ((p₀ : ℝ) - 1) = 2 * gT ((p₀ : ℝ) - 1)`. Unfold `gT`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tail_square_bound : TailSq := by
  intro p₀ s hp hs
  have hsub : s ⊆ Finset.Ico p₀ (p₀ + (s.sup id + 1)) := by
    intro n hn
    rw [Finset.mem_Ico]
    have : n ≤ s.sup id := Finset.le_sup (f := id) hn
    exact ⟨hs n hn, by omega⟩
  have h1 : ∑ n ∈ s, Real.log n / (n : ℝ) ^ 2 ≤
      ∑ n ∈ Finset.Ico p₀ (p₀ + (s.sup id + 1)), Real.log n / (n : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => div_nonneg (Real.log_natCast_nonneg n) (by positivity))
  have h2 := tail_Ico p₀ hp (s.sup id + 1)
  have hp' : (3 : ℝ) ≤ p₀ := by exact_mod_cast hp
  have h3 : 0 ≤ gT ((p₀ : ℝ) + ((s.sup id + 1 : ℕ) : ℝ) - 1) := by
    apply gT_nonneg
    have : (0 : ℝ) ≤ ((s.sup id + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have e : 2 * (Real.log ((p₀ : ℝ) - 1) + 1) / ((p₀ : ℝ) - 1) = 2 * gT ((p₀ : ℝ) - 1) := by
    unfold gT; ring
  rw [e]
  linarith

/- English proof (translation)
Unfold `askAt`. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i hi`. Establish `e : at_ * (1 / p) ^ i = at_ / p ^ i` using `by rw [one_div, inv_pow]; rfl`.

Rewrite using `[e]`. Apply `max_le` to reduce the goal to its premises. Combine the linear relations using `[hw i hi]`. Check the signs of the components of the expression.
-/
lemma askAt_le_geom (I : Finset ℕ) (at_ p : ℝ) (w : ℕ → ℝ) (hp : 0 < p) (ha : 0 ≤ at_)
    (hw : ∀ i ∈ I, 0 ≤ w i) : askAt I at_ p w ≤ at_ * ∑ i ∈ I, (1 / p) ^ i := by
  unfold askAt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have e : at_ * (1 / p) ^ i = at_ / p ^ i := by rw [one_div, inv_pow]; rfl
  rw [e]
  apply max_le
  · linarith [hw i hi]
  · positivity

/- English proof (translation)
Use `set K := I.sup id + 1`. Establish `hsub : I ⊆ (Finset.range K).image (fun k => 2 * k + 1)`. Introduce `i hi`. Take `⟨k, hk⟩` from `hI i hi`. Rewrite using `[Finset.mem_image]`.

Establish `: i ≤ I.sup id` using `Finset.le_sup (f := id) hi`. Conclude with `⟨k, Finset.mem_range.2 (by omega), hk.symm⟩`. Establish `h1 : ∑ i ∈ I, q ^ i ≤ ∑ i ∈ (Finset.range K).image (fun k => 2 * k + 1), q ^ i` using `Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg hq0 i)`. Rewrite `h1` using `[Finset.sum_image (by intro a _ b _ h; simpa using h)]`. Establish `h2 : ∑ k ∈ Finset.range K, q ^ (2 * k + 1) = q * ∑ k ∈ Finset.range K, (q ^ 2) ^ k`.

Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[pow_succ, pow_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hq2 : q ^ 2 ≤ 1 / 4` using `by nlinarith`. Establish `h3 : ∑ k ∈ Finset.range K, (q ^ 2) ^ k ≤ 4 / 3`. Use `geom_sum_Ico_le_of_lt_one (x := q ^ 2) (m := 0) (n := K) (sq_nonneg q) (by linarith)` as an intermediate fact. Rewrite using `[Finset.range_eq_Ico]`. Use `this.trans ?_` and prove the remaining obligations.

Rewrite using `[pow_zero, div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h1` using `[h2]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h3 hq0]`.
-/
lemma geom_odd (I : Finset ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (hI : ∀ i ∈ I, Odd i) :
    ∑ i ∈ I, q ^ i ≤ 4 / 3 * q := by
  set K := I.sup id + 1
  have hsub : I ⊆ (Finset.range K).image (fun k => 2 * k + 1) := by
    intro i hi
    obtain ⟨k, hk⟩ := hI i hi
    rw [Finset.mem_image]
    have : i ≤ I.sup id := Finset.le_sup (f := id) hi
    exact ⟨k, Finset.mem_range.2 (by omega), hk.symm⟩
  have h1 : ∑ i ∈ I, q ^ i ≤ ∑ i ∈ (Finset.range K).image (fun k => 2 * k + 1), q ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg hq0 i)
  rw [Finset.sum_image (by intro a _ b _ h; simpa using h)] at h1
  have h2 : ∑ k ∈ Finset.range K, q ^ (2 * k + 1) = q * ∑ k ∈ Finset.range K, (q ^ 2) ^ k := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [pow_succ, pow_mul]; ring
  have hq2 : q ^ 2 ≤ 1 / 4 := by nlinarith
  have h3 : ∑ k ∈ Finset.range K, (q ^ 2) ^ k ≤ 4 / 3 := by
    have := geom_sum_Ico_le_of_lt_one (x := q ^ 2) (m := 0) (n := K) (sq_nonneg q) (by linarith)
    rw [Finset.range_eq_Ico]
    refine this.trans ?_
    rw [pow_zero, div_le_iff₀ (by linarith)]
    linarith
  rw [h2] at h1
  nlinarith [mul_le_mul_of_nonneg_left h3 hq0]

/- English proof (translation)
Establish `hsub : I ⊆ Finset.Ico 1 (I.sup id + 1)`. Introduce `i hi`. Establish `: i ≤ I.sup id` using `Finset.le_sup (f := id) hi`. Conclude with `Finset.mem_Ico.2 ⟨hI i hi, by omega⟩`. Establish `h1 : ∑ i ∈ I, q ^ i ≤ ∑ i ∈ Finset.Ico 1 (I.sup id + 1), q ^ i` using `Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg hq0 i)`.

Use `geom_sum_Ico_le_of_lt_one (x := q) (m := 1) (n := I.sup id + 1) hq0 hq` as an intermediate fact. Rewrite `this` using `[pow_one]`. Conclude with `h1.trans this`.
-/
lemma geom_pos (I : Finset ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1) (hI : ∀ i ∈ I, 1 ≤ i) :
    ∑ i ∈ I, q ^ i ≤ q / (1 - q) := by
  have hsub : I ⊆ Finset.Ico 1 (I.sup id + 1) := by
    intro i hi
    have : i ≤ I.sup id := Finset.le_sup (f := id) hi
    exact Finset.mem_Ico.2 ⟨hI i hi, by omega⟩
  have h1 : ∑ i ∈ I, q ^ i ≤ ∑ i ∈ Finset.Ico 1 (I.sup id + 1), q ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg hq0 i)
  have := geom_sum_Ico_le_of_lt_one (x := q) (m := 1) (n := I.sup id + 1) hq0 hq
  rw [pow_one] at this
  exact h1.trans this

/- English proof (translation)
Introduce `I at_ p w hp ha hw hI`. Establish `hp0 : 0 < p` using `by linarith`. Establish `h1` using `askAt_le_geom I at_ p w hp0 ha hw`. Establish `hq : 1 / p ≤ 1 / 2`. Rewrite using `[div_le_div_iff₀ hp0 (by norm_num)]; linarith`.

Establish `h2` using `geom_odd I (1 / p) (by positivity) hq hI`. Establish `h3` using `mul_le_mul_of_nonneg_left h2 ha`. Establish `e : at_ * (4 / 3 * (1 / p)) = 4 / 3 * at_ / p` using `by ring`. Rewrite `h3` using `[e]`. Conclude with `h1.trans h3`.
-/
theorem top_term_bound : AskUpperBound := by
  intro I at_ p w hp ha hw hI
  have hp0 : 0 < p := by linarith
  have h1 := askAt_le_geom I at_ p w hp0 ha hw
  have hq : 1 / p ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
  have h2 := geom_odd I (1 / p) (by positivity) hq hI
  have h3 := mul_le_mul_of_nonneg_left h2 ha
  have e : at_ * (4 / 3 * (1 / p)) = 4 / 3 * at_ / p := by ring
  rw [e] at h3
  exact h1.trans h3

/- English proof (translation)
Introduce `I a at_ p w hp ha hat hw hI`. Establish `hpR : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `h1` using `top_term_bound I at_ p w hpR ha hw hI`. Establish `hl : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`.

Establish `h2 : 4 / 3 * at_ / p ≤ 2 * a / p`. Apply `div_le_div_of_nonneg_right _ hp0.le` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `mul_le_mul_of_nonneg_left (h1.trans h2) (show 0 ≤ 2 * Real.log p by linarith)`. Establish `e : 2 * Real.log p * (2 * a / p) = 4 * a * Real.log p / p` using `by ring`.

Rewrite `h3` using `[e]`. Conclude with `h3`.
-/
theorem top_loss_bound : TopLoss := by
  intro I a at_ p w hp ha hat hw hI
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 := top_term_bound I at_ p w hpR ha hw hI
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h2 : 4 / 3 * at_ / p ≤ 2 * a / p := by
    apply div_le_div_of_nonneg_right _ hp0.le
    linarith
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (show 0 ≤ 2 * Real.log p by linarith)
  have e : 2 * Real.log p * (2 * a / p) = 4 * a * Real.log p / p := by ring
  rw [e] at h3
  exact h3

/- English proof (translation)
Introduce `I a at_ d w hd ha hat hw hI`. Establish `hdR : (4 : ℝ) ≤ d` using `by exact_mod_cast hd`. Establish `hd0 : (0 : ℝ) < d` using `by linarith`. Establish `h1` using `askAt_le_geom I at_ d w hd0 ha hw`. Establish `hq : 1 / (d : ℝ) < 1`.

Rewrite using `[div_lt_one hd0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `geom_pos I (1 / (d : ℝ)) (by positivity) hq hI`. Establish `e1 : 1 / (d : ℝ) / (1 - 1 / (d : ℝ)) = 1 / ((d : ℝ) - 1)`. Establish `: (d : ℝ) - 1 ≠ 0` using `by linarith`.

Clear the denominators using the available nonvanishing facts. Rewrite `h2` using `[e1]`. Establish `h3 : at_ * (1 / ((d : ℝ) - 1)) ≤ 2 * a / d`. Establish `hd1 : (0 : ℝ) < (d : ℝ) - 1` using `by linarith`. Rewrite using `[mul_one_div, div_le_div_iff₀ hd1 hd0]`.

Establish `ha' : 0 ≤ a` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4` using `(h1.trans (mul_le_mul_of_nonneg_left h2 ha)).trans h3`. Establish `hl : 0 ≤ Real.log d` using `Real.log_natCast_nonneg d`. Establish `h5` using `mul_le_mul_of_nonneg_left h4 hl`.

Establish `e : Real.log d * (2 * a / d) = 2 * a * Real.log d / d` using `by ring`. Rewrite `h5` using `[e]`. Conclude with `h5`.
-/
theorem d_term_bound : DTerm := by
  intro I a at_ d w hd ha hat hw hI
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have h1 := askAt_le_geom I at_ d w hd0 ha hw
  have hq : 1 / (d : ℝ) < 1 := by
    rw [div_lt_one hd0]; linarith
  have h2 := geom_pos I (1 / (d : ℝ)) (by positivity) hq hI
  have e1 : 1 / (d : ℝ) / (1 - 1 / (d : ℝ)) = 1 / ((d : ℝ) - 1) := by
    have : (d : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [e1] at h2
  have h3 : at_ * (1 / ((d : ℝ) - 1)) ≤ 2 * a / d := by
    have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    rw [mul_one_div, div_le_div_iff₀ hd1 hd0]
    have ha' : 0 ≤ a := by linarith
    nlinarith
  have h4 := (h1.trans (mul_le_mul_of_nonneg_left h2 ha)).trans h3
  have hl : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have h5 := mul_le_mul_of_nonneg_left h4 hl
  have e : Real.log d * (2 * a / d) = 2 * a * Real.log d / d := by ring
  rw [e] at h5
  exact h5

/- English proof (translation)
Introduce `A B s hAB hs`. Break down `s.eq_empty_or_nonempty with rfl | hne` into its components or cases. Simplify using `only [Finset.card_empty, Nat.cast_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsub : s ⊆ Finset.Icc (s.min' hne) (s.max' hne)` using `fun n hn => Finset.mem_Icc.2 ⟨s.min'_le n hn, s.le_max' n hn⟩`.

Establish `hmM : s.min' hne ≤ s.max' hne` using `s.min'_le_max' hne`. Establish `hc : (s.card : ℝ) ≤ ((Finset.Icc (s.min' hne) (s.max' hne)).card : ℝ)`. Conclude with `Finset.card_le_card hsub` after adjusting the coercions. Rewrite `hc` using `[Nat.card_Icc, Nat.cast_sub (by omega)]`. Move the coercions through the operations in `at hc`.

Establish `hm` using `(hs _ (s.min'_mem hne)).1`. Establish `hM` using `(hs _ (s.max'_mem hne)).2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem interval_count : IntervalCount := by
  intro A B s hAB hs
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]; linarith
  · have hsub : s ⊆ Finset.Icc (s.min' hne) (s.max' hne) :=
      fun n hn => Finset.mem_Icc.2 ⟨s.min'_le n hn, s.le_max' n hn⟩
    have hmM : s.min' hne ≤ s.max' hne := s.min'_le_max' hne
    have hc : (s.card : ℝ) ≤ ((Finset.Icc (s.min' hne) (s.max' hne)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.cast_sub (by omega)] at hc
    push_cast at hc
    have hm := (hs _ (s.min'_mem hne)).1
    have hM := (hs _ (s.max'_mem hne)).2
    linarith

/- English proof (translation)
Introduce `P c s hP hc hs`. Establish `h` using `interval_count (P * (1 - c)) (P * (1 + c)) s (by nlinarith) hs`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem band_count : BandCount := by
  intro P c s hP hc hs
  have h := interval_count (P * (1 - c)) (P * (1 + c)) s (by nlinarith) hs
  linarith

/- English proof (translation)
Introduce `P c p₀ s hP hc0 hc hp₀ hs`. Establish `hP0 : 0 < P` using `by linarith`. Establish `hp0 : 0 < p₀` using `by linarith`. Establish `hcard` using `band_count P c s hP0.le hc0 (fun n hn => (hs n hn).2)`. Use `set μ := min (2 / P) (1 / p₀) with hμ`.

Establish `hμ0 : 0 ≤ μ` using `le_min (by positivity) (by positivity)`. Establish `hl2P : 0 ≤ Real.log (2 * P)` using `Real.log_nonneg (by linarith)`. Establish `hterm : ∀ n ∈ s, Real.log n / n ≤ Real.log (2 * P) * μ`. Introduce `n hn`. Take `⟨h1, h2, h3⟩` from `hs n hn`.

Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hlog : Real.log n ≤ Real.log (2 * P)` using `Real.log_le_log hn0 (by nlinarith)`. Establish `hinv : 1 / (n : ℝ) ≤ μ`. Apply `le_min` to reduce the goal to its premises. Rewrite using `[div_le_div_iff₀ hn0 hP0]`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `one_div_le_one_div_of_le hp0 h1`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum : ∑ n ∈ s, Real.log n / n ≤ s.card * (Real.log (2 * P) * μ)`. Use `Finset.sum_le_card_nsmul s _ _ hterm` as an intermediate fact.

Rewrite `this` using `[nsmul_eq_mul]`. Then use the resulting hypothesis. Establish `hcμ : (s.card : ℝ) * μ ≤ 4 * c + 1 / p₀`. Establish `h1 : (s.card : ℝ) * μ ≤ (2 * c * P + 1) * μ` using `mul_le_mul_of_nonneg_right hcard hμ0`. Establish `h2 : 2 * c * P * μ ≤ 2 * c * P * (2 / P)` using `mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)`. Establish `h3 : μ ≤ 1 / p₀` using `min_le_right _ _`.

Establish `e : 2 * c * P * (2 / P) = 4 * c` using `by field_simp; ring`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem band_sum : BandSum := by
  intro P c p₀ s hP hc0 hc hp₀ hs
  have hP0 : 0 < P := by linarith
  have hp0 : 0 < p₀ := by linarith
  have hcard := band_count P c s hP0.le hc0 (fun n hn => (hs n hn).2)
  set μ := min (2 / P) (1 / p₀) with hμ
  have hμ0 : 0 ≤ μ := le_min (by positivity) (by positivity)
  have hl2P : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith)
  have hterm : ∀ n ∈ s, Real.log n / n ≤ Real.log (2 * P) * μ := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hs n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : Real.log n ≤ Real.log (2 * P) := Real.log_le_log hn0 (by nlinarith)
    have hinv : 1 / (n : ℝ) ≤ μ := by
      apply le_min
      · rw [div_le_div_iff₀ hn0 hP0]; nlinarith
      · exact one_div_le_one_div_of_le hp0 h1
    calc Real.log n / n = Real.log n * (1 / (n : ℝ)) := by ring
      _ ≤ Real.log (2 * P) * μ :=
        mul_le_mul hlog hinv (by positivity) hl2P
  have hsum : ∑ n ∈ s, Real.log n / n ≤ s.card * (Real.log (2 * P) * μ) := by
    have := Finset.sum_le_card_nsmul s _ _ hterm
    rwa [nsmul_eq_mul] at this
  have hcμ : (s.card : ℝ) * μ ≤ 4 * c + 1 / p₀ := by
    have h1 : (s.card : ℝ) * μ ≤ (2 * c * P + 1) * μ := mul_le_mul_of_nonneg_right hcard hμ0
    have h2 : 2 * c * P * μ ≤ 2 * c * P * (2 / P) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    have h3 : μ ≤ 1 / p₀ := min_le_right _ _
    have e : 2 * c * P * (2 / P) = 4 * c := by field_simp; ring
    nlinarith
  calc ∑ n ∈ s, Real.log n / n ≤ s.card * (Real.log (2 * P) * μ) := hsum
    _ = (s.card * μ) * Real.log (2 * P) := by ring
    _ ≤ (4 * c + 1 / p₀) * Real.log (2 * P) := mul_le_mul_of_nonneg_right hcμ hl2P

/- English proof (translation)
Introduce `I P X' c p₀ s hc0 hc hp₀ hP hs`. Establish `hp0 : 0 < p₀` using `by linarith`. Establish `hterm : ∀ i ∈ Finset.range I, ∑ n ∈ s i, Real.log n / n ≤ (4 * c + 1 / p₀) * Real.log (2 * X')`. Introduce `i hi`. Establish `hi'` using `Finset.mem_range.1 hi`.

Establish `h1` using `band_sum (P i) c p₀ (s i) (hP i hi').1 hc0 hc hp₀ (hs i hi')`. Establish `h2 : Real.log (2 * P i) ≤ Real.log (2 * X')` using `Real.log_le_log (by linarith [(hP i hi').1]) (by linarith [(hP i hi').2])`. Conclude with `h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))`. Use `Finset.sum_le_card_nsmul (Finset.range I) _ _ hterm` as an intermediate fact. Rewrite `this` using `[Finset.card_range, nsmul_eq_mul]`. Then use the resulting hypothesis.
-/
theorem band_total : BandTotal := by
  intro I P X' c p₀ s hc0 hc hp₀ hP hs
  have hp0 : 0 < p₀ := by linarith
  have hterm : ∀ i ∈ Finset.range I, ∑ n ∈ s i, Real.log n / n ≤
      (4 * c + 1 / p₀) * Real.log (2 * X') := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have h1 := band_sum (P i) c p₀ (s i) (hP i hi').1 hc0 hc hp₀ (hs i hi')
    have h2 : Real.log (2 * P i) ≤ Real.log (2 * X') :=
      Real.log_le_log (by linarith [(hP i hi').1]) (by linarith [(hP i hi').2])
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have := Finset.sum_le_card_nsmul (Finset.range I) _ _ hterm
  rwa [Finset.card_range, nsmul_eq_mul] at this

/- English proof (translation)
Introduce `a at_ w'' X'' th s I w hw'' hth0 hth1 hX ha hat0 hat hs hI hw`. Simplify using `only [askAt]`. Establish `hX0 : 0 < X''` using `by linarith`. Establish `hl2X : 0 ≤ Real.log (2 * X'')` using `Real.log_nonneg (by linarith)`. Establish `hper : ∀ p ∈ s, 2 * Real.log p * ∑ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤ (if (p : ℝ) < X'' * (1 + th) then 2 * Real.log (2 * X'') * (w'' * th) else 0)`.

Introduce `p hp`. Establish `hpX : X'' < p` using `hs p hp`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hlp : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`. Use `set bp : ℝ := if (p : ℝ) < X'' * (1 + th) then w'' * th else 0 with hbp`.

Establish `hbp0 : 0 ≤ bp`. Rewrite using `[hbp]`. Use `split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`.

Establish `hi : ∀ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤ if i = 1 then bp else 0`. Introduce `i hiI`. Establish `hi1` using `hI p hp i hiI`. Distinguish the cases in `h1 : i = 1`. Substitute `h1` using the available equality.

Rewrite using `[if_pos rfl, pow_one]`. Apply `max_le _ hbp0` to reduce the goal to its premises. Rewrite using `[hbp]`. Use `split_ifs with hlt`. Establish `h2 : at_ / (p : ℝ) ≤ at_ / X''` using `div_le_div_of_nonneg_left hat0 hX0 hpX.le`.

Establish `h3 : at_ / X'' ≤ w'' * (1 + th)`. Rewrite using `[div_le_iff₀ hX0]`. Rewrite `hat` using `[← ha]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear relations using `[hw p hp 1 hiI]`.

Establish `hge : X'' * (1 + th) ≤ p` using `not_lt.1 hlt`. Establish `h2 : at_ / (p : ℝ) ≤ w''`. Rewrite using `[div_le_iff₀ hp0]`. Rewrite `hat` using `[← ha]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear relations using `[hw p hp 1 hiI]`. Rewrite using `[if_neg h1]`. Apply `max_le _ le_rfl` to reduce the goal to its premises. Establish `hi2 : 2 ≤ i` using `by omega`. Establish `hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ i` using `pow_le_pow_right₀ (by linarith) hi2`.

Establish `hp2 : 2 * X'' ≤ (p : ℝ) ^ 2` using `by nlinarith`. Establish `hpi0 : (0 : ℝ) < (p : ℝ) ^ i` using `by positivity`. Establish `h2 : at_ / (p : ℝ) ^ i ≤ w''`. Rewrite using `[div_le_iff₀ hpi0]`. Rewrite `hat` using `[← ha]`.

Establish `: at_ ≤ w'' * (2 * X'')` using `by nlinarith`. Establish `h5 : w'' * (2 * X'') ≤ w'' * (p : ℝ) ^ i` using `mul_le_mul_of_nonneg_left (hp2.trans hpow) hw''.le`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `[hw p hp i hiI]`. Establish `hinner : ∑ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤ bp`.

Use `(Finset.sum_le_sum hi).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `hbp0`.

Establish `h6 : 2 * Real.log p * ∑ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤ 2 * Real.log p * bp` using `mul_le_mul_of_nonneg_left hinner (by linarith)`. Use `h6.trans ?_` and prove the remaining obligations. Rewrite using `[hbp]`. Use `split_ifs with hlt`. Establish `hlog : Real.log p ≤ Real.log (2 * X'')` using `Real.log_le_log hp0 (by nlinarith)`.

Establish `: 0 ≤ w'' * th` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Simplify using the standard rewrite rules. Use `(Finset.sum_le_sum hper).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`.

Establish `hcard` using `interval_count X'' (X'' * (1 + th)) (s.filter (fun p : ℕ => (p : ℝ) < X'' * (1 + th))) (by nlinarith) (by`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_filter]`. Conclude with `⟨(hs n hn.1).le, hn.2.le⟩)`. Establish `hnn : 0 ≤ 2 * Real.log (2 * X'') * (w'' * th)` using `by positivity`.

Establish `h7` using `mul_le_mul_of_nonneg_right hcard hnn`. Use `h7.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← ha]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem high_bucket_bound : HighBucket := by
  intro a at_ w'' X'' th s I w hw'' hth0 hth1 hX ha hat0 hat hs hI hw
  simp only [askAt]
  have hX0 : 0 < X'' := by linarith
  have hl2X : 0 ≤ Real.log (2 * X'') := Real.log_nonneg (by linarith)

  have hper : ∀ p ∈ s, 2 * Real.log p * ∑ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤
      (if (p : ℝ) < X'' * (1 + th) then 2 * Real.log (2 * X'') * (w'' * th) else 0) := by
    intro p hp
    have hpX : X'' < p := hs p hp
    have hp0 : (0 : ℝ) < p := by linarith
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    set bp : ℝ := if (p : ℝ) < X'' * (1 + th) then w'' * th else 0 with hbp
    have hbp0 : 0 ≤ bp := by
      rw [hbp]; split_ifs
      · positivity
      · exact le_rfl
    have hi : ∀ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤ if i = 1 then bp else 0 := by
      intro i hiI
      have hi1 := hI p hp i hiI
      by_cases h1 : i = 1
      · subst h1
        rw [if_pos rfl, pow_one]
        apply max_le _ hbp0
        rw [hbp]
        split_ifs with hlt
        · have h2 : at_ / (p : ℝ) ≤ at_ / X'' := div_le_div_of_nonneg_left hat0 hX0 hpX.le
          have h3 : at_ / X'' ≤ w'' * (1 + th) := by
            rw [div_le_iff₀ hX0]; rw [← ha] at hat; nlinarith
          linarith [hw p hp 1 hiI]
        · have hge : X'' * (1 + th) ≤ p := not_lt.1 hlt
          have h2 : at_ / (p : ℝ) ≤ w'' := by
            rw [div_le_iff₀ hp0]; rw [← ha] at hat
            nlinarith
          linarith [hw p hp 1 hiI]
      · rw [if_neg h1]
        apply max_le _ le_rfl
        have hi2 : 2 ≤ i := by omega
        have hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ i := pow_le_pow_right₀ (by linarith) hi2
        have hp2 : 2 * X'' ≤ (p : ℝ) ^ 2 := by nlinarith
        have hpi0 : (0 : ℝ) < (p : ℝ) ^ i := by positivity
        have h2 : at_ / (p : ℝ) ^ i ≤ w'' := by
          rw [div_le_iff₀ hpi0]; rw [← ha] at hat
          have : at_ ≤ w'' * (2 * X'') := by nlinarith
          have h5 : w'' * (2 * X'') ≤ w'' * (p : ℝ) ^ i :=
            mul_le_mul_of_nonneg_left (hp2.trans hpow) hw''.le
          linarith
        linarith [hw p hp i hiI]
    have hinner : ∑ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤ bp := by
      refine (Finset.sum_le_sum hi).trans ?_
      rw [Finset.sum_ite_eq']
      split_ifs
      · exact le_rfl
      · exact hbp0
    have h6 : 2 * Real.log p * ∑ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤ 2 * Real.log p * bp :=
      mul_le_mul_of_nonneg_left hinner (by linarith)
    refine h6.trans ?_
    rw [hbp]
    split_ifs with hlt
    · have hlog : Real.log p ≤ Real.log (2 * X'') := Real.log_le_log hp0 (by nlinarith)
      have : 0 ≤ w'' * th := by positivity
      nlinarith
    · simp
  refine (Finset.sum_le_sum hper).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard := interval_count X'' (X'' * (1 + th))
    (s.filter (fun p : ℕ => (p : ℝ) < X'' * (1 + th))) (by nlinarith) (by
      intro n hn
      rw [Finset.mem_filter] at hn
      exact ⟨(hs n hn.1).le, hn.2.le⟩)
  have hnn : 0 ≤ 2 * Real.log (2 * X'') * (w'' * th) := by positivity
  have h7 := mul_le_mul_of_nonneg_right hcard hnn
  refine h7.trans (le_of_eq ?_)
  rw [← ha]; ring

/- English proof (translation)
Introduce `C f N a X'' s hC hf ha hs hcard`. Establish `hla : 0 ≤ Real.log a` using `Real.log_nonneg ha`. Establish `hB0 : 0 ≤ 2 * C * f * (N ^ 2 * Real.log a + 2 * Real.log a ^ 2)` using `by positivity`. Simplify using `only [flF]`. Establish `hterm : ∀ p ∈ s, 2 * Real.log p * (C * f * N ^ 2 * Real.logb p a + C * f * Real.logb p a ^ 2) ≤ 2 * C * f * (N ^ 2 * Real.log a + 2 * Real.log a ^ 2)`.

Introduce `p hp`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hs p hp`. Establish `hl2 : Real.log 2 ≤ Real.log p` using `Real.log_le_log (by norm_num) hp2`. Establish `hl2'` using `Real.log_two_gt_d9`. Establish `hlp : 0 < Real.log p` using `by linarith`.

Establish `e : 2 * Real.log p * (C * f * N ^ 2 * Real.logb p a + C * f * Real.logb p a ^ 2) = 2 * C * f * (N ^ 2 * Real.log a + Real.log a ^ 2 / Real.log p)`. Unfold `Real.logb`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Establish `h1 : Real.log a ^ 2 / Real.log p ≤ 2 * Real.log a ^ 2`.

Rewrite using `[div_le_iff₀ hlp]`. Establish `: 0 ≤ Real.log a ^ 2` using `sq_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `Finset.sum_le_card_nsmul s _ _ hterm`. Rewrite `h1` using `[nsmul_eq_mul]`. Establish `h2` using `mul_le_mul_of_nonneg_right hcard hB0`. Use `h1.trans (h2.trans (le_of_eq ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem floor_bucket_bound : FloorBucket := by
  intro C f N a X'' s hC hf ha hs hcard
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have hB0 : 0 ≤ 2 * C * f * (N ^ 2 * Real.log a + 2 * Real.log a ^ 2) := by positivity
  simp only [flF]
  have hterm : ∀ p ∈ s,
      2 * Real.log p * (C * f * N ^ 2 * Real.logb p a + C * f * Real.logb p a ^ 2) ≤
      2 * C * f * (N ^ 2 * Real.log a + 2 * Real.log a ^ 2) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hs p hp
    have hl2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have hl2' := Real.log_two_gt_d9
    have hlp : 0 < Real.log p := by linarith
    have e : 2 * Real.log p * (C * f * N ^ 2 * Real.logb p a + C * f * Real.logb p a ^ 2) =
        2 * C * f * (N ^ 2 * Real.log a + Real.log a ^ 2 / Real.log p) := by
      unfold Real.logb; field_simp
    rw [e]
    have h1 : Real.log a ^ 2 / Real.log p ≤ 2 * Real.log a ^ 2 := by
      rw [div_le_iff₀ hlp]
      have : 0 ≤ Real.log a ^ 2 := sq_nonneg _
      nlinarith
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have h1 := Finset.sum_le_card_nsmul s _ _ hterm
  rw [nsmul_eq_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right hcard hB0
  refine h1.trans (h2.trans (le_of_eq ?_))
  ring

/- English proof (translation)
Introduce `C Sk a mT X'' s hC hSk ha hmT hs hcard`. Establish `hla : 0 ≤ Real.log (2 * a)` using `Real.log_nonneg (by linarith)`. Establish `hB0 : 0 ≤ 2 * C * Sk * Real.log (2 * a) * mT` using `by positivity`. Simplify using `only [cpF]`. Establish `hterm : ∀ p ∈ s, 2 * Real.log p * (mT * (C * Sk * Real.logb p (2 * a))) ≤ 2 * C * Sk * Real.log (2 * a) * mT`.

Introduce `p hp`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hs p hp`. Establish `hlp : 0 < Real.log p` using `Real.log_pos (by linarith)`. Apply `le_of_eq` to reduce the goal to its premises. Unfold `Real.logb`.

Clear the denominators using the available nonvanishing facts. Establish `h1` using `Finset.sum_le_card_nsmul s _ _ hterm`. Rewrite `h1` using `[nsmul_eq_mul]`. Establish `h2` using `mul_le_mul_of_nonneg_right hcard hB0`. Use `h1.trans (h2.trans (le_of_eq ?_))` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cp_bucket_bound : CpBucket := by
  intro C Sk a mT X'' s hC hSk ha hmT hs hcard
  have hla : 0 ≤ Real.log (2 * a) := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ 2 * C * Sk * Real.log (2 * a) * mT := by positivity
  simp only [cpF]
  have hterm : ∀ p ∈ s, 2 * Real.log p * (mT * (C * Sk * Real.logb p (2 * a))) ≤
      2 * C * Sk * Real.log (2 * a) * mT := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hs p hp
    have hlp : 0 < Real.log p := Real.log_pos (by linarith)
    apply le_of_eq
    unfold Real.logb; field_simp
  have h1 := Finset.sum_le_card_nsmul s _ _ hterm
  rw [nsmul_eq_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right hcard hB0
  refine h1.trans (h2.trans (le_of_eq ?_))
  ring

/- English proof (translation)
Introduce `p₀ X' Q₁ Q₂ s hX' hQ₁ hQ₂ hs`. Simplify using `only [prF]`. Establish `hterm : ∀ p ∈ s, 2 * Real.log p * (if p < p₀ then Q₁ else Q₂) ≤ (if p < p₀ then 2 * Q₁ * Real.log p else 0) + 2 * Q₂ * Real.log p`. Introduce `p _`. Establish `hl : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`.

Use `split_ifs`. Use polynomial arithmetic with `[mul_nonneg hQ₂ hl]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(Finset.sum_le_sum hterm).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum, ← Finset.mul_sum]`.

Establish `h1` using `theta_finite p₀ (s.filter (fun p : ℕ => p < p₀)) (Nat.cast_nonneg _) (by`. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter]`. Conclude with `⟨(hs p hp.1).1, by exact_mod_cast hp.2.le⟩)`. Establish `h2` using `theta_finite X' s hX' (fun p hp => ⟨(hs p hp).1, (hs p hp).2.le⟩)`.

Establish `h3` using `mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * Q₁ by linarith)`. Establish `h4` using `mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * Q₂ by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pr_bucket_bound : PrBucket := by
  intro p₀ X' Q₁ Q₂ s hX' hQ₁ hQ₂ hs
  simp only [prF]
  have hterm : ∀ p ∈ s, 2 * Real.log p * (if p < p₀ then Q₁ else Q₂) ≤
      (if p < p₀ then 2 * Q₁ * Real.log p else 0) + 2 * Q₂ * Real.log p := by
    intro p _
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    split_ifs
    · nlinarith [mul_nonneg hQ₂ hl]
    · linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := theta_finite p₀ (s.filter (fun p : ℕ => p < p₀)) (Nat.cast_nonneg _) (by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨(hs p hp.1).1, by exact_mod_cast hp.2.le⟩)
  have h2 := theta_finite X' s hX' (fun p hp => ⟨(hs p hp).1, (hs p hp).2.le⟩)
  have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * Q₁ by linarith)
  have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * Q₂ by linarith)
  linarith

/- English proof (translation)
Introduce `C lx La a k K₀ X' L₁ p₀ s hC hlx hLa ha hk hK₀ hX' hp₀ hs hL`. Simplify using `only [orF]`. Establish `hterm : ∀ p ∈ s, 2 * Real.log p * (C * lx * (La * a / (p * k) + (if p < p₀ then a * (p : ℝ) ^ (-(L₁ p)) else a / (p : ℝ) ^ 2))) ≤ 2 * C * lx * a * (La / k) * (Real.log p / p) + (if p < p₀ then 2 * C * lx * a * (1 / K₀) * (Real.log p / p) else 0) + (if p₀ ≤ p then 2 * C * lx * a * …`. Introduce `p hp`. Establish `hpp` using `(hs p hp).1`.

Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hpp.pos`. Establish `hl : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`. Distinguish the cases in `hlt : p < p₀`. Rewrite using `[if_pos hlt, if_pos hlt, if_neg (by omega)]`. Establish `hK` using `hL p hp hlt`.

Rewrite `hK` using `[Real.rpow_sub_one hp0.ne']`. Establish `hpL : 0 < (p : ℝ) ^ (L₁ p)` using `Real.rpow_pos_of_pos hp0 _`. Establish `hK' : K₀ * p ≤ (p : ℝ) ^ (L₁ p)` using `(le_div_iff₀ hp0).1 hK`. Establish `hinv : (p : ℝ) ^ (-(L₁ p)) ≤ 1 / K₀ * (1 / p)`. Rewrite using `[Real.rpow_neg hp0.le, ← one_div, one_div_mul_one_div]`.

Conclude with `one_div_le_one_div_of_le (by positivity) hK'`. Establish `h1 : a * (p : ℝ) ^ (-(L₁ p)) ≤ a * (1 / K₀ * (1 / p))` using `mul_le_mul_of_nonneg_left hinv ha`. Establish `h2 : 2 * Real.log p * (C * lx * (La * a / (p * k) + a * (p : ℝ) ^ (-(L₁ p)))) ≤ 2 * Real.log p * (C * lx * (La * a / (p * k) + a * (1 / K₀ * (1 / p))))`. Apply `mul_le_mul_of_nonneg_left _ (by linarith)` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Use `h2.trans (le_of_eq ?_)` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hlt, if_neg hlt, if_pos (by omega)]`.

Apply `le_of_eq` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `(Finset.sum_le_sum hterm).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]`.

Establish `h1` using `prime_log_sum_bound X' s hX' (fun p hp => ⟨(hs p hp).1, (hs p hp).2.le⟩)`. Establish `h2` using `prime_log_sum_bound X' (s.filter (fun p => p < p₀)) hX' (by`. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter]`. Conclude with `⟨(hs p hp.1).1, (hs p hp.1).2.le⟩)`.

Establish `h3` using `tail_square_bound p₀ (s.filter (fun p => p₀ ≤ p)) hp₀ (by`. Introduce `p hp`. Conclude with `(Finset.mem_filter.1 hp).2)`. Establish `h4` using `mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C * lx * a * (La / k) by positivity)`. Establish `h5` using `mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * C * lx * a * (1 / K₀) by positivity)`.

Establish `h6` using `mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * C * lx * a by positivity)`. Use `(add_le_add (add_le_add h4 h5) h6).trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem or_bucket_bound : OrBucket := by
  intro C lx La a k K₀ X' L₁ p₀ s hC hlx hLa ha hk hK₀ hX' hp₀ hs hL
  simp only [orF]
  have hterm : ∀ p ∈ s, 2 * Real.log p * (C * lx * (La * a / (p * k) +
        (if p < p₀ then a * (p : ℝ) ^ (-(L₁ p)) else a / (p : ℝ) ^ 2))) ≤
      2 * C * lx * a * (La / k) * (Real.log p / p) +
      (if p < p₀ then 2 * C * lx * a * (1 / K₀) * (Real.log p / p) else 0) +
      (if p₀ ≤ p then 2 * C * lx * a * (Real.log p / (p : ℝ) ^ 2) else 0) := by
    intro p hp
    have hpp := (hs p hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    by_cases hlt : p < p₀
    · rw [if_pos hlt, if_pos hlt, if_neg (by omega)]
      have hK := hL p hp hlt
      rw [Real.rpow_sub_one hp0.ne'] at hK
      have hpL : 0 < (p : ℝ) ^ (L₁ p) := Real.rpow_pos_of_pos hp0 _
      have hK' : K₀ * p ≤ (p : ℝ) ^ (L₁ p) := (le_div_iff₀ hp0).1 hK
      have hinv : (p : ℝ) ^ (-(L₁ p)) ≤ 1 / K₀ * (1 / p) := by
        rw [Real.rpow_neg hp0.le, ← one_div, one_div_mul_one_div]
        exact one_div_le_one_div_of_le (by positivity) hK'
      have h1 : a * (p : ℝ) ^ (-(L₁ p)) ≤ a * (1 / K₀ * (1 / p)) := mul_le_mul_of_nonneg_left hinv ha
      have h2 : 2 * Real.log p * (C * lx * (La * a / (p * k) + a * (p : ℝ) ^ (-(L₁ p)))) ≤
          2 * Real.log p * (C * lx * (La * a / (p * k) + a * (1 / K₀ * (1 / p)))) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      refine h2.trans (le_of_eq ?_)
      field_simp
      ring
    · rw [if_neg hlt, if_neg hlt, if_pos (by omega)]
      apply le_of_eq
      field_simp
      ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := prime_log_sum_bound X' s hX' (fun p hp => ⟨(hs p hp).1, (hs p hp).2.le⟩)
  have h2 := prime_log_sum_bound X' (s.filter (fun p => p < p₀)) hX' (by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨(hs p hp.1).1, (hs p hp.1).2.le⟩)
  have h3 := tail_square_bound p₀ (s.filter (fun p => p₀ ≤ p)) hp₀ (by
    intro p hp
    exact (Finset.mem_filter.1 hp).2)
  have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C * lx * a * (La / k) by positivity)
  have h5 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * C * lx * a * (1 / K₀) by positivity)
  have h6 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * C * lx * a by positivity)
  refine (add_le_add (add_le_add h4 h5) h6).trans (le_of_eq ?_)
  ring

/- English proof (translation)
Introduce `α ι _ _ _ δ β m a ω BAD _ hδ0 hδ1 h16 hβ hω hm ha hcond`. Take `⟨T, hT1, hT2, hT3⟩` from `Formalism.RankGapBounds.V4.tops_lemma_sixteen_holds α ι δ β ω BAD hδ0 hδ1 h16 hβ hω hcond`. Use `⟨T, hT1, hT2, ?_⟩` and prove the remaining obligations. Establish `hSum : 0 ≤ ∑ p, ω p` using `Finset.sum_nonneg (fun p _ => hω p)`. Establish `e : ∑ p, 4 * m * a * ω p * ((T.filter fun t => BAD p t T).card : ℝ) = 4 * m * a * ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ)`.

Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Establish `h1` using `mul_le_mul_of_nonneg_left hT3 (show 0 ≤ 4 * m * a by positivity)`. Establish `h2 : 4 * β * δ * Fintype.card α * ∑ p, ω p ≤ 8 * β * T.card * ∑ p, ω p`. Apply `mul_le_mul_of_nonneg_right _ hSum` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `h3` using `mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * m * a by positivity)`.

Use `h1.trans (h3.trans (le_of_eq ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bad_orbits_bucket_bound : BadOrbitsBucket := by
  intro α ι _ _ _ δ β m a ω BAD _ hδ0 hδ1 h16 hβ hω hm ha hcond
  obtain ⟨T, hT1, hT2, hT3⟩ :=
    Formalism.RankGapBounds.V4.tops_lemma_sixteen_holds α ι δ β ω BAD hδ0 hδ1 h16 hβ hω hcond
  refine ⟨T, hT1, hT2, ?_⟩
  have hSum : 0 ≤ ∑ p, ω p := Finset.sum_nonneg (fun p _ => hω p)
  have e : ∑ p, 4 * m * a * ω p * ((T.filter fun t => BAD p t T).card : ℝ) =
      4 * m * a * ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left hT3 (show 0 ≤ 4 * m * a by positivity)
  have h2 : 4 * β * δ * Fintype.card α * ∑ p, ω p ≤ 8 * β * T.card * ∑ p, ω p := by
    apply mul_le_mul_of_nonneg_right _ hSum
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * m * a by positivity)
  refine h1.trans (h3.trans (le_of_eq ?_))
  ring

/- English proof (translation)
Take `⟨C, hC⟩` from `Formalism.RankGapBounds.LocalQuadraticParts.ordersSumY_of Formalism.RankGapBounds.LocalQuadraticParts.powTwoPowEqOneIff_holds`. Use `⟨C, ?_⟩` and prove the remaining obligations. Introduce `e J Y mTa s he hJ hY hm hs`. Rewrite using `[← Finset.mul_sum]`. Conclude with `mul_le_mul_of_nonneg_left (hC e J Y s he hJ hY hs) (by linarith)`.
-/
theorem orders_bucket_bound : OrdersBucket := by
  obtain ⟨C, hC⟩ := Formalism.RankGapBounds.LocalQuadraticParts.ordersSumY_of Formalism.RankGapBounds.LocalQuadraticParts.powTwoPowEqOneIff_holds
  refine ⟨C, ?_⟩
  intro e J Y mTa s he hJ hY hm hs
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hC e J Y s he hJ hY hs) (by linarith)

/- English proof (translation)
Introduce `Ω _ π s Sig L θ s₀ hπ hθ hSig hL hmean`. Establish `h1 : ∑ o, π o * ∑ p ∈ s, (if θ < Sig p o then L p else 0) ≤ ∑ o, π o * ∑ p ∈ s, (Sig p o / θ * L p)`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `o _`. Apply `mul_le_mul_of_nonneg_left _ (hπ o)` to reduce the goal to its premises.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Use `split_ifs with h`. Establish `: 1 ≤ Sig p o / θ` using `by rw [le_div_iff₀ hθ]; linarith`. Use polynomial arithmetic with `[hL p hp]`.

Conclude with `mul_nonneg (div_nonneg (hSig p hp o) hθ.le) (hL p hp)`. Establish `h2 : ∑ o, π o * ∑ p ∈ s, (Sig p o / θ * L p) = ∑ p ∈ s, L p / θ * ∑ o, π o * Sig p o`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `p _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `o _`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ∑ p ∈ s, L p / θ * ∑ o, π o * Sig p o ≤ ∑ p ∈ s, L p / θ * s₀`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Conclude with `mul_le_mul_of_nonneg_left (hmean p hp) (div_nonneg (hL p hp) hθ.le)`. Establish `h4 : ∑ p ∈ s, L p / θ * s₀ = s₀ / θ * ∑ p ∈ s, L p`. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p _`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem markov_drop : MarkovDrop := by
  intro Ω _ π s Sig L θ s₀ hπ hθ hSig hL hmean
  have h1 : ∑ o, π o * ∑ p ∈ s, (if θ < Sig p o then L p else 0) ≤
      ∑ o, π o * ∑ p ∈ s, (Sig p o / θ * L p) := by
    apply Finset.sum_le_sum
    intro o _
    apply mul_le_mul_of_nonneg_left _ (hπ o)
    apply Finset.sum_le_sum
    intro p hp
    split_ifs with h
    · have : 1 ≤ Sig p o / θ := by rw [le_div_iff₀ hθ]; linarith
      nlinarith [hL p hp]
    · exact mul_nonneg (div_nonneg (hSig p hp o) hθ.le) (hL p hp)
  have h2 : ∑ o, π o * ∑ p ∈ s, (Sig p o / θ * L p) = ∑ p ∈ s, L p / θ * ∑ o, π o * Sig p o := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro o _
    ring
  have h3 : ∑ p ∈ s, L p / θ * ∑ o, π o * Sig p o ≤ ∑ p ∈ s, L p / θ * s₀ := by
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hmean p hp) (div_nonneg (hL p hp) hθ.le)
  have h4 : ∑ p ∈ s, L p / θ * s₀ = s₀ / θ * ∑ p ∈ s, L p := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  linarith

/- English proof (translation)
Introduce `Ω ν _ π V kap N m T c hm hc hmean hN`. Establish `h1 : ∑ o, π o * (m * ∑ v ∈ V, kap v o) = m * ∑ v ∈ V, ∑ o, π o * kap v o`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `v _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `o _`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∑ v ∈ V, ∑ o, π o * kap v o ≤ ∑ v ∈ V, N v * c` using `Finset.sum_le_sum hmean`.

Rewrite `h2` using `[← Finset.sum_mul]`. Establish `h3 : (∑ v ∈ V, N v) * c ≤ T * c` using `mul_le_mul_of_nonneg_right hN hc`. Rewrite using `[h1]`. Use `mul_le_mul_of_nonneg_left (h2.trans h3) hm` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sigma_mean : SigMean := by
  intro Ω ν _ π V kap N m T c hm hc hmean hN
  have h1 : ∑ o, π o * (m * ∑ v ∈ V, kap v o) = m * ∑ v ∈ V, ∑ o, π o * kap v o := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    apply Finset.sum_congr rfl; intro o _
    ring
  have h2 : ∑ v ∈ V, ∑ o, π o * kap v o ≤ ∑ v ∈ V, N v * c := Finset.sum_le_sum hmean
  rw [← Finset.sum_mul] at h2
  have h3 : (∑ v ∈ V, N v) * c ≤ T * c := mul_le_mul_of_nonneg_right hN hc
  rw [h1]
  have := mul_le_mul_of_nonneg_left (h2.trans h3) hm
  linarith

/- English proof (translation)
Introduce `Ω _ π s Sig Y θ s₀ mTa hπ hθ hs₀ hm hY hSig hs hmean`. Establish `h1` using `markov_drop Ω π s Sig (fun p => 4 * mTa * Real.log p / p) θ s₀ hπ hθ hSig (fun p _ => div_nonneg (mul_nonneg (by linarith) (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p)) hmean`. Use `h1.trans ?_` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_left _ (div_nonneg hs₀ hθ.le)` to reduce the goal to its premises. Establish `e : ∑ p ∈ s, 4 * mTa * Real.log p / p = 4 * mTa * ∑ p ∈ s, Real.log p / p`.

Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `mul_le_mul_of_nonneg_left (prime_log_sum_bound Y s hY hs) (by linarith)`.
-/
theorem second_kind_bucket_bound : SecondKindBucket := by
  intro Ω _ π s Sig Y θ s₀ mTa hπ hθ hs₀ hm hY hSig hs hmean
  have h1 := markov_drop Ω π s Sig (fun p => 4 * mTa * Real.log p / p) θ s₀ hπ hθ hSig
    (fun p _ => div_nonneg (mul_nonneg (by linarith) (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p))
    hmean
  refine h1.trans ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hs₀ hθ.le)
  have e : ∑ p ∈ s, 4 * mTa * Real.log p / p = 4 * mTa * ∑ p ∈ s, Real.log p / p := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (prime_log_sum_bound Y s hY hs) (by linarith)

/- English proof (translation)
Introduce `Ω _ π s Sig io Y s₀ mTa hπ hs₀ hm hY hs hmean hio`. Establish `h1 : ∑ o, π o * ∑ p ∈ s, Real.log p * io p o ≤ ∑ o, π o * ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p))`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `o _`. Apply `mul_le_mul_of_nonneg_left _ (hπ o)` to reduce the goal to its premises.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Conclude with `mul_le_mul_of_nonneg_left (hio p hp o) (Real.log_natCast_nonneg p)`. Establish `h2 : ∑ o, π o * ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)) = ∑ p ∈ s, 4 * mTa * (Real.log p / p) * ∑ o, π o * Sig p o`. Simplify using `only [Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `o _`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ∑ p ∈ s, 4 * mTa * (Real.log p / p) * ∑ o, π o * Sig p o ≤ ∑ p ∈ s, 4 * mTa * (Real.log p / p) * s₀`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Apply `mul_le_mul_of_nonneg_left (hmean p hp)` to reduce the goal to its premises.

Conclude with `mul_nonneg (by linarith) (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))`. Establish `h4 : ∑ p ∈ s, 4 * mTa * (Real.log p / p) * s₀ = 4 * mTa * s₀ * ∑ p ∈ s, Real.log p / p`. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p _`.

Expand and normalize the polynomial expressions, which then agree. Establish `h5` using `mul_le_mul_of_nonneg_left (prime_log_sum_bound Y s hY hs) (show 0 ≤ 4 * mTa * s₀ by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem io_mean_bound : IoMean := by
  intro Ω _ π s Sig io Y s₀ mTa hπ hs₀ hm hY hs hmean hio
  have h1 : ∑ o, π o * ∑ p ∈ s, Real.log p * io p o ≤
      ∑ o, π o * ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)) := by
    apply Finset.sum_le_sum
    intro o _
    apply mul_le_mul_of_nonneg_left _ (hπ o)
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hio p hp o) (Real.log_natCast_nonneg p)
  have h2 : ∑ o, π o * ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)) =
      ∑ p ∈ s, 4 * mTa * (Real.log p / p) * ∑ o, π o * Sig p o := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro o _
    ring
  have h3 : ∑ p ∈ s, 4 * mTa * (Real.log p / p) * ∑ o, π o * Sig p o ≤
      ∑ p ∈ s, 4 * mTa * (Real.log p / p) * s₀ := by
    apply Finset.sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_left (hmean p hp)
    exact mul_nonneg (by linarith) (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have h4 : ∑ p ∈ s, 4 * mTa * (Real.log p / p) * s₀ = 4 * mTa * s₀ * ∑ p ∈ s, Real.log p / p := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  have h5 := mul_le_mul_of_nonneg_left (prime_log_sum_bound Y s hY hs)
    (show 0 ≤ 4 * mTa * s₀ by positivity)
  linarith

/- English proof (translation)
Introduce `Ω ν _ π V Vo kap N m T c hm hc hπ hsub hkap hmean hN`. Use `le_trans ?_ (sigma_mean Ω ν π V kap N m T c hm hc hmean hN)` and prove the remaining obligations. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `o _`. Apply `mul_le_mul_of_nonneg_left _ (hπ o)` to reduce the goal to its premises.

Apply `mul_le_mul_of_nonneg_left _ hm` to reduce the goal to its premises. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (hsub o) (fun v hv _ => hkap v hv o)`.
-/
theorem sigma_mean_variance : SigMeanVar := by
  intro Ω ν _ π V Vo kap N m T c hm hc hπ hsub hkap hmean hN
  refine le_trans ?_ (sigma_mean Ω ν π V kap N m T c hm hc hmean hN)
  apply Finset.sum_le_sum
  intro o _
  apply mul_le_mul_of_nonneg_left _ (hπ o)
  apply mul_le_mul_of_nonneg_left _ hm
  exact Finset.sum_le_sum_of_subset_of_nonneg (hsub o) (fun v hv _ => hkap v hv o)

/- English proof (translation)
Introduce `Ω _ π X M hπ h1 hM`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hterm : ∀ o ∈ (Finset.univ : Finset Ω), 0 ≤ π o * (X o - M)`. Introduce `o _`.

Break down `(hπ o).eq_or_lt with h | h` into its components or cases. Rewrite using `[← h]`. Simplify using the standard rewrite rules. Conclude with `mul_nonneg h.le (by linarith [hcon o h])`. Establish `hsum : ∑ o, π o * (X o - M) ≤ 0`.

Establish `e : ∑ o, π o * (X o - M) = ∑ o, π o * X o - (∑ o, π o) * M`. Rewrite using `[Finset.sum_mul, ← Finset.sum_sub_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `o _`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz` using `(Finset.sum_eq_zero_iff_of_nonneg hterm).1 (le_antisymm hsum (Finset.sum_nonneg hterm))`. Establish `hπ0 : ∀ o, π o = 0`. Introduce `o`.

Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < π o` using `lt_of_le_of_ne (hπ o) (Ne.symm hne)`. Establish `h2` using `hz o (Finset.mem_univ o)`. Establish `h3 : 0 < π o * (X o - M)` using `mul_pos hpos (by linarith [hcon o hpos])`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `[hπ0] at h1`.
-/
theorem choose_window : ChooseWindow := by
  intro Ω _ π X M hπ h1 hM
  by_contra hcon
  push Not at hcon
  have hterm : ∀ o ∈ (Finset.univ : Finset Ω), 0 ≤ π o * (X o - M) := by
    intro o _
    rcases (hπ o).eq_or_lt with h | h
    · rw [← h]; simp
    · exact mul_nonneg h.le (by linarith [hcon o h])
  have hsum : ∑ o, π o * (X o - M) ≤ 0 := by
    have e : ∑ o, π o * (X o - M) = ∑ o, π o * X o - (∑ o, π o) * M := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro o _; ring
    rw [e, h1]; linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).1
    (le_antisymm hsum (Finset.sum_nonneg hterm))
  have hπ0 : ∀ o, π o = 0 := by
    intro o
    by_contra hne
    have hpos : 0 < π o := lt_of_le_of_ne (hπ o) (Ne.symm hne)
    have h2 := hz o (Finset.mem_univ o)
    have h3 : 0 < π o * (X o - M) := mul_pos hpos (by linarith [hcon o hpos])
    linarith
  simp [hπ0] at h1

/- English proof (translation)
Introduce `Ω _ π F G A B hπ h1 hF hG hA hB`. Take `⟨o, ho, hX⟩` from `choose_window Ω π (fun o => F o + G o) (A + B) hπ h1 (by`. Simplify using `only [mul_add, Finset.sum_add_distrib]`. Use the proof step `linarith)`. Conclude with `⟨o, ho, hX, by linarith [hG o], by linarith [hF o]⟩`.
-/
theorem choose_window_second : ChooseWindow2 := by
  intro Ω _ π F G A B hπ h1 hF hG hA hB
  obtain ⟨o, ho, hX⟩ := choose_window Ω π (fun o => F o + G o) (A + B) hπ h1 (by
    simp only [mul_add, Finset.sum_add_distrib]; linarith)
  exact ⟨o, ho, hX, by linarith [hG o], by linarith [hF o]⟩

/- English proof (translation)
Establish `h1 : ∀ j ∈ J, ∑ t ∈ S, g j t ≤ S.card * c`. Introduce `j hj`. Use `Finset.sum_le_card_nsmul S _ c (h j hj)` as an intermediate fact. Rewrite `this` using `[nsmul_eq_mul]`. Then use the resulting hypothesis. Establish `h2` using `Finset.sum_le_card_nsmul J _ _ h1`.

Rewrite `h2` using `[nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma dsum_le {κ τ : Type*} (J : Finset κ) (S : Finset τ) (g : κ → τ → ℝ) (c : ℝ)
    (h : ∀ j ∈ J, ∀ t ∈ S, g j t ≤ c) :
    ∑ j ∈ J, ∑ t ∈ S, g j t ≤ (J.card : ℝ) * S.card * c := by
  have h1 : ∀ j ∈ J, ∑ t ∈ S, g j t ≤ S.card * c := by
    intro j hj
    have := Finset.sum_le_card_nsmul S _ c (h j hj)
    rwa [nsmul_eq_mul] at this
  have h2 := Finset.sum_le_card_nsmul J _ _ h1
  rw [nsmul_eq_mul] at h2
  calc _ ≤ (J.card : ℝ) * (S.card * c) := h2
    _ = _ := by ring

/- English proof (translation)
Introduce `ι κ τ W below l Ps cl J TT TTp Iex at_ wz Id wd d gainW tauW gain tau lo fl a th w'' X'' X' C f N Sk Q₁ Q₂ lx La k K₀ L₁ p₀ hU hPr hw'' hth0 hth hX'' haX ha1 hX' hp₀ hd hC hf hSk hQ₁ hQ₂ hlx hLa hk hK₀ hat hIex hId hserved hhigh hled hdrop hfl hlo hL`. Establish `h0` using `split_classes_count ι κ τ W below l Ps cl J TT TTp (fun j t p => askAt (Iex j t p) (at_ t) p (wz j t p)) (fun j t => Real.log d * askAt (Id j t) (at_ t) d (wd j t)) gainW tauW gain tau lo fl hU hled hdrop`. Generalize the expression as in `hask : (fun j t p => askAt (Iex j t p) (at_ t) (p : ℝ) (wz j t p) : κ → τ → ℕ → ℝ) = vonMangoldtClassSum at h0 hled ⊢`. Generalize the expression as in `hdT : (fun j t => Real.log d * askAt (Id j t) (at_ t) d (wd j t) : κ → τ → ℝ) = dT at h0 ⊢`. Generalize the expression as in `hm : (J.card : ℝ) = m at h0 ⊢`.

Generalize the expression as in `hT : (TT.card : ℝ) = T at h0 ⊢`. Establish `hm0 : 0 ≤ m` using `by rw [← hm]; exact Nat.cast_nonneg _`. Establish `hT0 : 0 ≤ T` using `by rw [← hT]; exact Nat.cast_nonneg _`. Establish `ha0 : 0 ≤ a` using `by linarith`. Establish `hat32 : ∀ t ∈ TT, at_ t ≤ 3 / 2 * a`.

Introduce `t ht`. Use `(hat t ht).2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hTop : ∀ j ∈ J, ∀ t ∈ TT, ∀ p ∈ Ps, 2 * Real.log p * vonMangoldtClassSum j t p ≤ 4 * a * Real.log p / p`. Introduce `j hj t ht p hp`.

Rewrite using `[← hask]`. Conclude with `top_loss_bound (Iex j t p) a (at_ t) p (wz j t p) (hPr p hp).two_le (hat t ht).1 (hat32 t ht) (fun i hi => by linarith [(hIex j hj t ht p hp i hi).2]) (fun i hi => (hIex j hj t ht p hp i hi).1)`. Establish `hWhole : ∀ p ∈ Ps, 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p ≤ 4 * m * T * a * (Real.log p / p)`. Introduce `p hp`. Unfold `wholeAsk`.

Simplify using `only [Finset.mul_sum]`. Use `(dsum_le J TT _ _ (fun j hj t ht => hTop j hj t ht p hp)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hm, hT]`. Expand and normalize the polynomial expressions, which then agree. Establish `hS : ∀ c : PClass, ∑ p ∈ Ps.filter (fun p => cl p = c), 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p ≤ 4 * m * T * a * ∑ p ∈ Ps.filter (fun p => cl p = c), Real.log p / p`.

Introduce `c`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_le_sum (fun p hp => hWhole p (Finset.mem_filter.1 hp).1)`. Establish `hHigh : ∑ p ∈ Ps.filter (fun p => cl p = PClass.high), 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p ≤ m * T * (2 * Real.log (2 * X'') * (a * th ^ 2 + w'' * th))`. Unfold `wholeAsk`.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm, Finset.sum_congr rfl (fun j _ => Finset.sum_comm), ← hm, ← hT]`. Apply `dsum_le` to reduce the goal to its premises. Introduce `j hj t ht`. Rewrite using `[← hask]`.

Conclude with `high_bucket_bound a (at_ t) w'' X'' th _ (fun p => Iex j t p) (fun p => wz j t p) hw'' hth0 (by linarith) hX'' haX (hat t ht).1 (hat t ht).2 (fun p hp => hhigh p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2) (fun p hp i hi => (hIex j hj t ht p (Finset.mem_filter.1 hp).1 …`. Establish `hD : ∑ j ∈ J, ∑ t ∈ TT, dT j t ≤ m * T * (2 * a * Real.log d / d)`. Rewrite using `[← hm, ← hT]`. Apply `dsum_le` to reduce the goal to its premises. Introduce `j hj t ht`.

Rewrite using `[← hdT]`. Conclude with `d_term_bound (Id j t) a (at_ t) d (wd j t) hd (hat t ht).1 (hat32 t ht) (fun i hi => (hId j hj t ht i hi).2) (fun i hi => (hId j hj t ht i hi).1)`. Establish `hServ : ∀ p ∈ Ps.filter (fun p => cl p = PClass.served), 2 * Real.log p * servedLoss J TT TTp vonMangoldtClassSum lo fl p ≤ 4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) + 2 * Real.log p * (m * T * cpF C Sk a p) + (if (p : ℝ) < X' then m * T * (2 * Real.log p * prF p₀ Q₁ …`. Introduce `p hp`. Take `⟨hpP, hc⟩` from `Finset.mem_filter.1 hp`.

Establish `hl : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast (hPr p hpP).two_le`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hsub` using `(hled p hpP hc).1`. Establish `h1 : 2 * Real.log p * ∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p ≤ 4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ)`.

Simplify using `only [Finset.mul_sum]`. Use `(dsum_le J (TT \ TTp p) _ _ (fun j hj t ht => hTop j hj t (Finset.mem_sdiff.1 ht).1 p hpP)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcp0 : 0 ≤ cpF C Sk a p`.

Unfold `cpF`. Establish `: 0 ≤ Real.logb p (2 * a)` using `Real.logb_nonneg (by linarith) (by linarith)`. Check the signs of the components of the expression. Apply the tactic sequence `have hpr0 : 0 ≤ prF p₀ Q₁ Q₂ p := by unfold prF; split_ifs <;> assumption`. Establish `hor0 : 0 ≤ orF C lx La a k L₁ p₀ p`.

Unfold `orF`. Establish `: 0 ≤ (if p < p₀ then a * (p : ℝ) ^ (-(L₁ p)) else a / (p : ℝ) ^ 2)` using `by split_ifs`. Conclude with `mul_nonneg ha0 (Real.rpow_nonneg hp0.le _)`. Check the signs of the components of the expression. Check the signs of the components of the expression.

Establish `hloF0 : 0 ≤ loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p`. Apply the tactic sequence `unfold loF; split_ifs <;> linarith`. Establish `hcard : ((TTp p).card : ℝ) ≤ T`. Rewrite using `[← hT]`. Conclude with `Finset.card_le_card hsub` after adjusting the coercions.

Establish `hcard0 : (0 : ℝ) ≤ ((TTp p).card : ℝ)` using `Nat.cast_nonneg _`. Establish `h2 : m * (TTp p).card * lo p ≤ m * T * loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : m * fl p ≤ m * flF C f N a p` using `mul_le_mul_of_nonneg_left (hfl p hpP hc) hm0`. Unfold `servedLoss`.

Rewrite using `[hm]`. Establish `h4` using `mul_le_mul_of_nonneg_left (add_le_add h2 h3) (show 0 ≤ 2 * Real.log p by linarith)`. Establish `e1 : 2 * Real.log p * (∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p + m * (TTp p).card * lo p + m * fl p) = 2 * Real.log p * ∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p + 2 * Real.log p * (m * (TTp p).card * lo p + m * fl p)` using `by ring`. Rewrite using `[e1]`. Establish `e2 : 2 * Real.log p * (m * T * loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p + m * flF C f N a p) = 2 * Real.log p * (m * T * cpF C Sk a p) + (if (p : ℝ) < X' then m * T * (2 * Real.log p * prF p₀ Q₁ Q₂ p) else 0) + (if (p : ℝ) < X' then m * T * (2 * Real.log p * orF C lx La a k L₁ p₀ p) e …`.

Unfold `loF`. Apply the tactic sequence `split_ifs <;> ring`. Rewrite `h4` using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS1` using `Finset.sum_le_sum hServ`.

Simplify using `only [Finset.sum_add_distrib] at hS1`. Rewrite `hS1` using `[← Finset.sum_filter, ← Finset.sum_filter, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]`. Establish `hs2 : ∀ p ∈ Ps.filter (fun p => cl p = PClass.served), 2 ≤ p` using `fun p hp => (hPr p (Finset.mem_filter.1 hp).1).two_le`. Establish `hcardS : ((Ps.filter (fun p => cl p = PClass.served)).card : ℝ) ≤ X''`. Use `interval_count 2 X'' (Ps.filter (fun p => cl p = PClass.served)) hX'' (by` as an intermediate fact.

Introduce `p hp`. Conclude with `⟨by exact_mod_cast hs2 p hp, hserved p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2⟩)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCp` using `cp_bucket_bound C Sk a (m * T) X'' _ hC hSk (by linarith) (by positivity) hs2 hcardS`. Establish `hFl` using `floor_bucket_bound C f N a X'' _ hC hf ha1 hs2 hcardS`.

Establish `hPrB` using `pr_bucket_bound p₀ X' Q₁ Q₂ ((Ps.filter (fun p => cl p = PClass.served)).filter (fun p : ℕ => (p : ℝ) < X')) (by linarith) hQ₁ hQ₂ (by`. Introduce `p hp`. Take `⟨hp1, hp2⟩` from `Finset.mem_filter.1 hp`. Conclude with `⟨hPr p (Finset.mem_filter.1 hp1).1, hp2⟩)`. Establish `hOrB` using `or_bucket_bound C lx La a k K₀ X' L₁ p₀ ((Ps.filter (fun p => cl p = PClass.served)).filter (fun p : ℕ => (p : ℝ) < X')) hC hlx hLa ha0 hk hK₀ hX' hp₀ (by`.

Introduce `p hp`. Take `⟨hp1, hp2⟩` from `Finset.mem_filter.1 hp`. Conclude with `⟨hPr p (Finset.mem_filter.1 hp1).1, hp2⟩) (by`. Introduce `p hp`. Conclude with `hL p (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)`.

Establish `hmT : 0 ≤ m * T` using `by positivity`. Establish `hPr'` using `mul_le_mul_of_nonneg_left hPrB hmT`. Establish `hOr'` using `mul_le_mul_of_nonneg_left hOrB hmT`. Establish `hFl'` using `mul_le_mul_of_nonneg_left hFl hm0`. Establish `hF1` using `hS PClass.first`.

Establish `hF2` using `hS PClass.second`. Simplify using `only [← hdT] at hD`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem loss_bound : SecondKindLoss := by
  intro ι κ τ W below l Ps cl J TT TTp Iex at_ wz Id wd d gainW tauW gain tau lo fl
    a th w'' X'' X' C f N Sk Q₁ Q₂ lx La k K₀ L₁ p₀
    hU hPr hw'' hth0 hth hX'' haX ha1 hX' hp₀ hd hC hf hSk hQ₁ hQ₂ hlx hLa hk hK₀
    hat hIex hId hserved hhigh hled hdrop hfl hlo hL
  have h0 := split_classes_count ι κ τ W below l Ps cl J TT TTp
    (fun j t p => askAt (Iex j t p) (at_ t) p (wz j t p))
    (fun j t => Real.log d * askAt (Id j t) (at_ t) d (wd j t))
    gainW tauW gain tau lo fl hU hled hdrop
  generalize hask : (fun j t p => askAt (Iex j t p) (at_ t) (p : ℝ) (wz j t p) :
    κ → τ → ℕ → ℝ) = vonMangoldtClassSum at h0 hled ⊢
  generalize hdT : (fun j t => Real.log d * askAt (Id j t) (at_ t) d (wd j t) : κ → τ → ℝ) = dT
    at h0 ⊢
  generalize hm : (J.card : ℝ) = m at h0 ⊢
  generalize hT : (TT.card : ℝ) = T at h0 ⊢
  have hm0 : 0 ≤ m := by rw [← hm]; exact Nat.cast_nonneg _
  have hT0 : 0 ≤ T := by rw [← hT]; exact Nat.cast_nonneg _
  have ha0 : 0 ≤ a := by linarith
  have hat32 : ∀ t ∈ TT, at_ t ≤ 3 / 2 * a := by
    intro t ht
    have := (hat t ht).2
    nlinarith
  have hTop : ∀ j ∈ J, ∀ t ∈ TT, ∀ p ∈ Ps,
      2 * Real.log p * vonMangoldtClassSum j t p ≤ 4 * a * Real.log p / p := by
    intro j hj t ht p hp
    rw [← hask]
    exact top_loss_bound (Iex j t p) a (at_ t) p (wz j t p) (hPr p hp).two_le (hat t ht).1
      (hat32 t ht) (fun i hi => by linarith [(hIex j hj t ht p hp i hi).2])
      (fun i hi => (hIex j hj t ht p hp i hi).1)
  have hWhole : ∀ p ∈ Ps,
      2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p ≤ 4 * m * T * a * (Real.log p / p) := by
    intro p hp
    unfold wholeAsk
    simp only [Finset.mul_sum]
    refine (dsum_le J TT _ _ (fun j hj t ht => hTop j hj t ht p hp)).trans (le_of_eq ?_)
    rw [hm, hT]; ring
  have hS : ∀ c : PClass,
      ∑ p ∈ Ps.filter (fun p => cl p = c), 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p ≤
      4 * m * T * a * ∑ p ∈ Ps.filter (fun p => cl p = c), Real.log p / p := by
    intro c
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p hp => hWhole p (Finset.mem_filter.1 hp).1)
  have hHigh : ∑ p ∈ Ps.filter (fun p => cl p = PClass.high),
      2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p ≤
      m * T * (2 * Real.log (2 * X'') * (a * th ^ 2 + w'' * th)) := by
    unfold wholeAsk
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => Finset.sum_comm), ← hm, ← hT]
    apply dsum_le
    intro j hj t ht
    rw [← hask]
    exact high_bucket_bound a (at_ t) w'' X'' th _ (fun p => Iex j t p) (fun p => wz j t p)
      hw'' hth0 (by linarith) hX'' haX (hat t ht).1 (hat t ht).2
      (fun p hp => hhigh p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2)
      (fun p hp i hi => (hIex j hj t ht p (Finset.mem_filter.1 hp).1 i hi).1.pos)
      (fun p hp i hi => (hIex j hj t ht p (Finset.mem_filter.1 hp).1 i hi).2)
  have hD : ∑ j ∈ J, ∑ t ∈ TT, dT j t ≤ m * T * (2 * a * Real.log d / d) := by
    rw [← hm, ← hT]
    apply dsum_le
    intro j hj t ht
    rw [← hdT]
    exact d_term_bound (Id j t) a (at_ t) d (wd j t) hd (hat t ht).1 (hat32 t ht)
      (fun i hi => (hId j hj t ht i hi).2) (fun i hi => (hId j hj t ht i hi).1)
  have hServ : ∀ p ∈ Ps.filter (fun p => cl p = PClass.served),
      2 * Real.log p * servedLoss J TT TTp vonMangoldtClassSum lo fl p ≤
        4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) +
        2 * Real.log p * (m * T * cpF C Sk a p) +
        (if (p : ℝ) < X' then m * T * (2 * Real.log p * prF p₀ Q₁ Q₂ p) else 0) +
        (if (p : ℝ) < X' then m * T * (2 * Real.log p * orF C lx La a k L₁ p₀ p) else 0) +
        m * (2 * Real.log p * flF C f N a p) := by
    intro p hp
    obtain ⟨hpP, hc⟩ := Finset.mem_filter.1 hp
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hPr p hpP).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hsub := (hled p hpP hc).1
    have h1 : 2 * Real.log p * ∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p ≤
        4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) := by
      simp only [Finset.mul_sum]
      refine (dsum_le J (TT \ TTp p) _ _
        (fun j hj t ht => hTop j hj t (Finset.mem_sdiff.1 ht).1 p hpP)).trans (le_of_eq ?_)
      rw [hm]; ring
    have hcp0 : 0 ≤ cpF C Sk a p := by
      unfold cpF
      have : 0 ≤ Real.logb p (2 * a) := Real.logb_nonneg (by linarith) (by linarith)
      positivity
    have hpr0 : 0 ≤ prF p₀ Q₁ Q₂ p := by unfold prF; split_ifs <;> assumption
    have hor0 : 0 ≤ orF C lx La a k L₁ p₀ p := by
      unfold orF
      have : 0 ≤ (if p < p₀ then a * (p : ℝ) ^ (-(L₁ p)) else a / (p : ℝ) ^ 2) := by
        split_ifs
        · exact mul_nonneg ha0 (Real.rpow_nonneg hp0.le _)
        · positivity
      positivity
    have hloF0 : 0 ≤ loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p := by
      unfold loF; split_ifs <;> linarith
    have hcard : ((TTp p).card : ℝ) ≤ T := by
      rw [← hT]; exact_mod_cast Finset.card_le_card hsub
    have hcard0 : (0 : ℝ) ≤ ((TTp p).card : ℝ) := Nat.cast_nonneg _
    have h2 : m * (TTp p).card * lo p ≤ m * T * loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p := by
      calc m * (TTp p).card * lo p ≤ m * (TTp p).card * loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p :=
            mul_le_mul_of_nonneg_left (hlo p hpP hc) (by positivity)
        _ ≤ m * T * loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hm0) hloF0
    have h3 : m * fl p ≤ m * flF C f N a p := mul_le_mul_of_nonneg_left (hfl p hpP hc) hm0
    unfold servedLoss
    rw [hm]
    have h4 := mul_le_mul_of_nonneg_left (add_le_add h2 h3) (show 0 ≤ 2 * Real.log p by linarith)
    have e1 : 2 * Real.log p * (∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p + m * (TTp p).card * lo p +
        m * fl p) = 2 * Real.log p * ∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p +
        2 * Real.log p * (m * (TTp p).card * lo p + m * fl p) := by ring
    rw [e1]
    have e2 : 2 * Real.log p * (m * T * loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p + m * flF C f N a p) =
        2 * Real.log p * (m * T * cpF C Sk a p) +
        (if (p : ℝ) < X' then m * T * (2 * Real.log p * prF p₀ Q₁ Q₂ p) else 0) +
        (if (p : ℝ) < X' then m * T * (2 * Real.log p * orF C lx La a k L₁ p₀ p) else 0) +
        m * (2 * Real.log p * flF C f N a p) := by
      unfold loF
      split_ifs <;> ring
    rw [e2] at h4
    linarith
  have hS1 := Finset.sum_le_sum hServ
  simp only [Finset.sum_add_distrib] at hS1
  rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hS1
  have hs2 : ∀ p ∈ Ps.filter (fun p => cl p = PClass.served), 2 ≤ p :=
    fun p hp => (hPr p (Finset.mem_filter.1 hp).1).two_le
  have hcardS : ((Ps.filter (fun p => cl p = PClass.served)).card : ℝ) ≤ X'' := by
    have := interval_count 2 X'' (Ps.filter (fun p => cl p = PClass.served)) hX'' (by
      intro p hp
      exact ⟨by exact_mod_cast hs2 p hp,
        hserved p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2⟩)
    linarith
  have hCp := cp_bucket_bound C Sk a (m * T) X'' _ hC hSk (by linarith) (by positivity) hs2 hcardS
  have hFl := floor_bucket_bound C f N a X'' _ hC hf ha1 hs2 hcardS
  have hPrB := pr_bucket_bound p₀ X' Q₁ Q₂
    ((Ps.filter (fun p => cl p = PClass.served)).filter (fun p : ℕ => (p : ℝ) < X'))
    (by linarith) hQ₁ hQ₂ (by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      exact ⟨hPr p (Finset.mem_filter.1 hp1).1, hp2⟩)
  have hOrB := or_bucket_bound C lx La a k K₀ X' L₁ p₀
    ((Ps.filter (fun p => cl p = PClass.served)).filter (fun p : ℕ => (p : ℝ) < X'))
    hC hlx hLa ha0 hk hK₀ hX' hp₀ (by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      exact ⟨hPr p (Finset.mem_filter.1 hp1).1, hp2⟩) (by
      intro p hp
      exact hL p (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
  have hmT : 0 ≤ m * T := by positivity
  have hPr' := mul_le_mul_of_nonneg_left hPrB hmT
  have hOr' := mul_le_mul_of_nonneg_left hOrB hmT
  have hFl' := mul_le_mul_of_nonneg_left hFl hm0
  have hF1 := hS PClass.first
  have hF2 := hS PClass.second
  simp only [← hdT] at hD
  linarith

/- English proof (translation)
Introduce `X' ρ p i hX hρ0 hρ1 hp hi hlo hhi`. Establish `hi0 : i ≠ 0` using `by omega`. Use `set R : ℝ := X' ^ ((1 : ℝ) / i) with hR`. Establish `hR0 : 0 < R` using `Real.rpow_pos_of_pos hX _`. Establish `hRi : R ^ i = X'`.

Rewrite using `[hR, one_div]`. Conclude with `Real.rpow_inv_natCast_pow hX.le hi0`. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hcon`. Establish `hlt : p < R * (1 - ρ)` using `not_le.1 hcon`.

Establish `h1 : p ^ i < (R * (1 - ρ)) ^ i` using `pow_lt_pow_left₀ hlt hp hi0`. Rewrite `h1` using `[mul_pow, hRi]`. Establish `h2 : (1 - ρ) ^ i ≤ 1 - ρ` using `pow_le_of_le_one (by linarith) (by linarith) hi0`. Establish `h3 : X' * (1 - ρ) ^ i ≤ X' * (1 - ρ)` using `mul_le_mul_of_nonneg_left h2 hX.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Assume the negation of the conclusion as `hcon`. Establish `hlt : R * (1 + ρ) < p` using `not_le.1 hcon`. Establish `h1 : (R * (1 + ρ)) ^ i < p ^ i` using `pow_lt_pow_left₀ hlt (by positivity) hi0`. Rewrite `h1` using `[mul_pow, hRi]`. Establish `h2 : 1 + ρ ≤ (1 + ρ) ^ i` using `le_self_pow₀ (by linarith) hi0`.

Establish `h3 : X' * (1 + ρ) ≤ X' * (1 + ρ) ^ i` using `mul_le_mul_of_nonneg_left h2 hX.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem band_root_bound : BandRoot := by
  intro X' ρ p i hX hρ0 hρ1 hp hi hlo hhi
  have hi0 : i ≠ 0 := by omega
  set R : ℝ := X' ^ ((1 : ℝ) / i) with hR
  have hR0 : 0 < R := Real.rpow_pos_of_pos hX _
  have hRi : R ^ i = X' := by
    rw [hR, one_div]; exact Real.rpow_inv_natCast_pow hX.le hi0
  constructor
  · by_contra hcon
    have hlt : p < R * (1 - ρ) := not_le.1 hcon
    have h1 : p ^ i < (R * (1 - ρ)) ^ i := pow_lt_pow_left₀ hlt hp hi0
    rw [mul_pow, hRi] at h1
    have h2 : (1 - ρ) ^ i ≤ 1 - ρ := pow_le_of_le_one (by linarith) (by linarith) hi0
    have h3 : X' * (1 - ρ) ^ i ≤ X' * (1 - ρ) := mul_le_mul_of_nonneg_left h2 hX.le
    linarith
  · by_contra hcon
    have hlt : R * (1 + ρ) < p := not_le.1 hcon
    have h1 : (R * (1 + ρ)) ^ i < p ^ i := pow_lt_pow_left₀ hlt (by positivity) hi0
    rw [mul_pow, hRi] at h1
    have h2 : 1 + ρ ≤ (1 + ρ) ^ i := le_self_pow₀ (by linarith) hi0
    have h3 : X' * (1 + ρ) ≤ X' * (1 + ρ) ^ i := mul_le_mul_of_nonneg_left h2 hX.le
    linarith

/- English proof (translation)
Introduce `X' ρ p i hX hρ hp hpi`. Establish `hp8 : (8 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hpow0 : (0 : ℝ) < (p : ℝ) ^ i` using `by positivity`. Establish `h1 : Real.log ((p : ℝ) ^ i) ≤ Real.log (2 * X')` using `Real.log_le_log hpow0 (by nlinarith)`.

Rewrite `h1` using `[Real.log_pow, Real.log_mul (by norm_num) (by linarith)]`. Establish `h2 : Real.log 2 ≤ Real.log X'` using `Real.log_le_log (by norm_num) hX`. Establish `h8 : Real.log 8 ≤ Real.log p` using `Real.log_le_log (by norm_num) hp8`. Establish `e8 : Real.log 8 = 3 * Real.log 2`. Rewrite using `[show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num`.

Establish `hl2` using `Real.log_two_gt_d9`. Establish `hlp : 2 ≤ Real.log p` using `by linarith`. Establish `hi0 : (0 : ℝ) ≤ i` using `Nat.cast_nonneg i`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem band_exponent_bound : BandExponent := by
  intro X' ρ p i hX hρ hp hpi
  have hp8 : (8 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpow0 : (0 : ℝ) < (p : ℝ) ^ i := by positivity
  have h1 : Real.log ((p : ℝ) ^ i) ≤ Real.log (2 * X') :=
    Real.log_le_log hpow0 (by nlinarith)
  rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h1
  have h2 : Real.log 2 ≤ Real.log X' := Real.log_le_log (by norm_num) hX
  have h8 : Real.log 8 ≤ Real.log p := Real.log_le_log (by norm_num) hp8
  have e8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_gt_d9
  have hlp : 2 ≤ Real.log p := by linarith
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  nlinarith

/- English proof (translation)
Take `⟨C, hC⟩` from `Formalism.RankGapBounds.LocalQuadraticParts.ordersSumY_of Formalism.RankGapBounds.LocalQuadraticParts.powTwoPowEqOneIff_holds`. Use `⟨C, ?_⟩` and prove the remaining obligations. Introduce `e J I Y X' c p₀ P s he hJ hY hc0 hc hp₀ hP hs`. Establish `hf0 : ∀ p : ℕ, 0 ≤ Real.log p / (p : ℝ)` using `fun p => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)`. Establish `hterm : ∀ p ∈ s, Real.log p / (p : ℝ) ≤ (if ((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) then Real.log p / (p : ℝ) else 0) + ∑ i ∈ Finset.range I, (if (p₀ ≤ p ∧ P i * (1 - c) ≤ p ∧ (p : ℝ) ≤ P i * (1 + c)) …`.

Introduce `p hp`. Establish `hsum0 : 0 ≤ ∑ i ∈ Finset.range I, (if (p₀ ≤ p ∧ P i * (1 - c) ≤ p ∧ (p : ℝ) ≤ P i * (1 + c)) then Real.log p / (p : ℝ) else 0)`. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `i _`. Use `split_ifs`.

Conclude with `hf0 p`. Conclude with `le_rfl`. Break down `(hs p hp).2.2 with h | ⟨i, hi, hb⟩` into its components or cases. Rewrite using `[if_pos h]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `Finset.single_le_sum (f := fun i => (if (p₀ ≤ p ∧ P i * (1 - c) ≤ p ∧ (p : ℝ) ≤ P i * (1 + c)) then Real.log p / (p : ℝ) else 0)) (s := Finset.range I) (by`. Introduce `i _`. Use `split_ifs`. Conclude with `hf0 p`. Conclude with `le_rfl) (Finset.mem_range.2 hi)`.

Rewrite `h1` using `[if_pos hb]`. Establish `: 0 ≤ (if ((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) then Real.log p / (p : ℝ) else 0)` using `by split_ifs`. Conclude with `hf0 p`. Conclude with `le_rfl`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(Finset.sum_le_sum hterm).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_filter]`. Simplify using `only [← Finset.sum_filter]`. Apply `add_le_add` to reduce the goal to its premises. Apply `hC e J Y _ he hJ hY` to reduce the goal to its premises.

Introduce `l hl`. Take `⟨hl1, hl2⟩` from `Finset.mem_filter.1 hl`. Conclude with `⟨(hs l hl1).1, (hs l hl1).2.1, hl2.1, hl2.2⟩`. Apply `band_total I P X' c p₀ _ hc0 hc hp₀ hP` to reduce the goal to its premises. Introduce `i _ n hn`.

Conclude with `(Finset.mem_filter.1 hn).2`.
-/
theorem first_kind_bucket_bound : FirstKindBucket := by
  obtain ⟨C, hC⟩ := Formalism.RankGapBounds.LocalQuadraticParts.ordersSumY_of Formalism.RankGapBounds.LocalQuadraticParts.powTwoPowEqOneIff_holds
  refine ⟨C, ?_⟩
  intro e J I Y X' c p₀ P s he hJ hY hc0 hc hp₀ hP hs
  have hf0 : ∀ p : ℕ, 0 ≤ Real.log p / (p : ℝ) :=
    fun p => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hterm : ∀ p ∈ s, Real.log p / (p : ℝ) ≤
      (if ((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e),
          orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) then Real.log p / (p : ℝ) else 0) +
      ∑ i ∈ Finset.range I, (if (p₀ ≤ p ∧ P i * (1 - c) ≤ p ∧ (p : ℝ) ≤ P i * (1 + c)) then
          Real.log p / (p : ℝ) else 0) := by
    intro p hp
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range I,
        (if (p₀ ≤ p ∧ P i * (1 - c) ≤ p ∧ (p : ℝ) ≤ P i * (1 + c)) then
          Real.log p / (p : ℝ) else 0) := by
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact hf0 p
      · exact le_rfl
    rcases (hs p hp).2.2 with h | ⟨i, hi, hb⟩
    · rw [if_pos h]; linarith
    · have h1 := Finset.single_le_sum (f := fun i =>
          (if (p₀ ≤ p ∧ P i * (1 - c) ≤ p ∧ (p : ℝ) ≤ P i * (1 + c)) then
            Real.log p / (p : ℝ) else 0)) (s := Finset.range I) (by
          intro i _
          split_ifs
          · exact hf0 p
          · exact le_rfl) (Finset.mem_range.2 hi)
      rw [if_pos hb] at h1
      have : 0 ≤ (if ((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e),
          orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) then Real.log p / (p : ℝ) else 0) := by
        split_ifs
        · exact hf0 p
        · exact le_rfl
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_filter]
  simp only [← Finset.sum_filter]
  apply add_le_add
  · apply hC e J Y _ he hJ hY
    intro l hl
    obtain ⟨hl1, hl2⟩ := Finset.mem_filter.1 hl
    exact ⟨(hs l hl1).1, (hs l hl1).2.1, hl2.1, hl2.2⟩
  · apply band_total I P X' c p₀ _ hc0 hc hp₀ hP
    intro i _ n hn
    exact (Finset.mem_filter.1 hn).2

/- English proof (translation)
Introduce `Ω _ π Loss s Sig io D Y θ s₀ mTa hπ h1 hθ hs₀ hm hY hs hSig hmean hLoss hio`. Establish `hA` using `second_kind_bucket_bound Ω π s Sig Y θ s₀ mTa hπ hθ hs₀ hm hY hSig hs hmean`. Establish `hB` using `io_mean_bound Ω π s Sig (fun p o => 2 * Sig p o * (2 * mTa / p)) Y s₀ mTa hπ hs₀ hm hY hs hmean (fun p _ o => le_rfl)`. Take `⟨o, ho, hFG, -, -⟩` from `choose_window_second Ω π (fun o => ∑ p ∈ s, (if θ < Sig p o then 4 * mTa * Real.log p / p else 0)) (fun o => ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p))) _ _ hπ h1 (by`. Introduce `o`.

Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `p _`. Use `split_ifs`. Conclude with `div_nonneg (mul_nonneg (by linarith) (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p)`. Conclude with `le_rfl) (by`.

Introduce `o`. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `p hp`. Establish `h2` using `hSig p hp o`. Establish `h3` using `Real.log_natCast_nonneg p`.

Establish `h4 : (0 : ℝ) ≤ p` using `Nat.cast_nonneg p`. Use the proof step `positivity) hA hB`. Establish `hF0 : 0 ≤ ∑ p ∈ s, (if θ < Sig p o then 4 * mTa * Real.log p / p else 0)`. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `p _`.

Use `split_ifs`. Conclude with `div_nonneg (mul_nonneg (by linarith) (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p)`. Conclude with `le_rfl`. Establish `hG0 : 0 ≤ ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p))`. Apply `Finset.sum_nonneg` to reduce the goal to its premises.

Introduce `p hp`. Establish `h2` using `hSig p hp o`. Establish `h3` using `Real.log_natCast_nonneg p`. Establish `h4 : (0 : ℝ) ≤ p` using `Nat.cast_nonneg p`. Check the signs of the components of the expression.

Establish `hio' : ∑ p ∈ s, Real.log p * io p o ≤ ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p))` using `Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hio p hp o) (Real.log_natCast_nonneg p))`. Establish `e : (s₀ / θ + s₀) * (4 * mTa * (Real.log Y + Real.log 4)) = s₀ / θ * (4 * mTa * (Real.log Y + Real.log 4)) + 4 * mTa * s₀ * (Real.log Y + Real.log 4)` using `by ring`. Use `⟨o, ho, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Combine the linear relations using `[hLoss o]`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem loss_choice : LossChoice := by
  intro Ω _ π Loss s Sig io D Y θ s₀ mTa hπ h1 hθ hs₀ hm hY hs hSig hmean hLoss hio
  have hA := second_kind_bucket_bound Ω π s Sig Y θ s₀ mTa hπ hθ hs₀ hm hY hSig hs hmean
  have hB := io_mean_bound Ω π s Sig (fun p o => 2 * Sig p o * (2 * mTa / p)) Y s₀ mTa hπ hs₀ hm hY
    hs hmean (fun p _ o => le_rfl)
  obtain ⟨o, ho, hFG, -, -⟩ := choose_window_second Ω π
    (fun o => ∑ p ∈ s, (if θ < Sig p o then 4 * mTa * Real.log p / p else 0))
    (fun o => ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)))
    _ _ hπ h1 (by
      intro o
      apply Finset.sum_nonneg
      intro p _
      split_ifs
      · exact div_nonneg (mul_nonneg (by linarith) (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p)
      · exact le_rfl) (by
      intro o
      apply Finset.sum_nonneg
      intro p hp
      have h2 := hSig p hp o
      have h3 := Real.log_natCast_nonneg p
      have h4 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      positivity) hA hB
  have hF0 : 0 ≤ ∑ p ∈ s, (if θ < Sig p o then 4 * mTa * Real.log p / p else 0) := by
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact div_nonneg (mul_nonneg (by linarith) (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p)
    · exact le_rfl
  have hG0 : 0 ≤ ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)) := by
    apply Finset.sum_nonneg
    intro p hp
    have h2 := hSig p hp o
    have h3 := Real.log_natCast_nonneg p
    have h4 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    positivity
  have hio' : ∑ p ∈ s, Real.log p * io p o ≤ ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)) :=
    Finset.sum_le_sum (fun p hp =>
      mul_le_mul_of_nonneg_left (hio p hp o) (Real.log_natCast_nonneg p))
  have e : (s₀ / θ + s₀) * (4 * mTa * (Real.log Y + Real.log 4)) =
      s₀ / θ * (4 * mTa * (Real.log Y + Real.log 4)) +
        4 * mTa * s₀ * (Real.log Y + Real.log 4) := by ring
  refine ⟨o, ho, ?_, ?_⟩
  · rw [e]; linarith [hLoss o]
  · rw [e]; linarith

end

end Formalism.LFunctionChainParameters.DeficitSplitLemmas
