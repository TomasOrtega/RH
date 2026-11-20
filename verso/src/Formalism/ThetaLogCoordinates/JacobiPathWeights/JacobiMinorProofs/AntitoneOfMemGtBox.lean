import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementP

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace Pieri

/- English proof (translation)
Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.single_le_sum (f := fun m => ν m - μ m) (fun m _ => sub_nonneg.mpr (h m)) (Finset.mem_univ i)`.
-/
lemma sub_le_sum_sub {n : ℕ} (ν μ : Fin n → ℤ) (h : ∀ m, μ m ≤ ν m) (i : Fin n) :
    ν i - μ i ≤ ∑ m, ν m - ∑ m, μ m := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.single_le_sum (f := fun m => ν m - μ m) (fun m _ => sub_nonneg.mpr (h m))
    (Finset.mem_univ i)

/- English proof (translation)
Unfold `stripsUp`. Rewrite using `[Finset.mem_filter, Fintype.mem_piFinset]`. Unfold `HStrip`. Simplify using `only [Finset.mem_Icc]`. Prove the components needed by the constructor for the conclusion.

Conclude with `fun h => h.2`. Introduce `h`. Conclude with `⟨fun i => ⟨h.1 i, by linarith [sub_le_sum_sub ν μ h.1 i, h.2.2]⟩, h⟩`.
-/
lemma mem_stripsUp {n : ℕ} (μ ν : Fin n → ℤ) (b : ℕ) : ν ∈ stripsUp μ b ↔ HStrip ν μ b := by
  classical
  unfold stripsUp
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  unfold HStrip
  simp only [Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun i => ⟨h.1 i, by linarith [sub_le_sum_sub ν μ h.1 i, h.2.2]⟩, h⟩

/- English proof (translation)
Unfold `stripsDown`. Rewrite using `[Finset.mem_filter, Fintype.mem_piFinset]`. Unfold `HStrip`. Simplify using `only [Finset.mem_Icc]`. Prove the components needed by the constructor for the conclusion.

Conclude with `fun h => h.2`. Introduce `h`. Conclude with `⟨fun i => ⟨by linarith [sub_le_sum_sub μ ν h.1 i, h.2.2, h.1 i], by linarith [sub_le_sum_sub μ ν h.1 i, h.2.2, h.1 i]⟩, h⟩`.
-/
lemma mem_stripsDown {n : ℕ} (μ ν : Fin n → ℤ) (b : ℕ) : ν ∈ stripsDown μ b ↔ HStrip μ ν b := by
  classical
  unfold stripsDown
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  unfold HStrip
  simp only [Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun i => ⟨by linarith [sub_le_sum_sub μ ν h.1 i, h.2.2, h.1 i],
      by linarith [sub_le_sum_sub μ ν h.1 i, h.2.2, h.1 i]⟩, h⟩

/- English proof (translation)
Unfold `gtBox`. Simplify using `only [Fintype.mem_piFinset, Finset.mem_Icc]`.
-/
lemma mem_gtBox {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ : Fin n → ℤ) :
    κ ∈ gtBox μ ↔ ∀ i, μ i.succ ≤ κ i ∧ κ i ≤ μ i.castSucc := by
  unfold gtBox
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma dGT_succ {n : ℕ} (μ : Fin (n + 1) → ℤ) : dGT (n + 1) μ = ∑ κ ∈ gtBox μ, dGT n κ := rfl

/- English proof (translation)
Rewrite `hκ` using `[mem_gtBox]`. Introduce `i j hij`. Break down `eq_or_lt_of_le hij with h | h` into its components or cases. Rewrite using `[h]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma antitone_of_mem_gtBox {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hμ : Antitone μ)
    (hκ : κ ∈ gtBox μ) : Antitone κ := by
  rw [mem_gtBox] at hκ
  intro i j hij
  rcases eq_or_lt_of_le hij with h | h
  · rw [h]
  · calc κ j ≤ μ j.castSucc := (hκ j).2
      _ ≤ μ i.succ := hμ (Fin.succ_le_castSucc_iff.mpr h)
      _ ≤ κ i := (hκ i).1

open Classical in

def sLe {n : ℕ} (κ : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (κ i) (κ i + b)).filter fun l =>
    (∀ m, κ m ≤ l m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → l m' ≤ κ m) ∧
      ∑ m, l m - ∑ m, κ m ≤ (b : ℤ)

/- English proof (translation)
Unfold `sLe`. Rewrite using `[Finset.mem_filter, Fintype.mem_piFinset]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`. Introduce `h`.

Use `⟨fun i => Finset.mem_Icc.mpr ⟨h.1 i, ?_⟩, h⟩` and prove the remaining obligations. Use `sub_le_sum_sub l κ h.1 i` as an intermediate fact. Combine the linear relations using `[h.2.2]`.
-/
lemma mem_sLe {n : ℕ} (κ l : Fin n → ℤ) (b : ℕ) :
    l ∈ sLe κ b ↔ (∀ m, κ m ≤ l m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → l m' ≤ κ m) ∧
      ∑ m, l m - ∑ m, κ m ≤ (b : ℤ) := by
  unfold sLe
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨h.1 i, ?_⟩, h⟩
    have := sub_le_sum_sub l κ h.1 i
    linarith [h.2.2]

/- English proof (translation)
Establish `hnn : ∀ l : Fin n → ℤ, (∀ m, κ m ≤ l m) → 0 ≤ ∑ m, l m - ∑ m, κ m`. Introduce `l hl`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_nonneg (fun m _ => sub_nonneg.mpr (hl m))`. Use `symm`.

Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := sLe κ b) (t := Finset.range (b + 1)) (g := fun l => (∑ m, l m - ∑ m, κ m).toNat) (by`. Introduce `l hl`. Rewrite `hl` using `[mem_sLe]`. Use `hnn l hl.1` as an intermediate fact. Rewrite using `[Finset.mem_range]`.

Use the proof step `omega)]`. Use `Finset.sum_congr rfl (fun c hc => Finset.sum_congr ?_ (fun _ _ => rfl))` and prove the remaining obligations. Rewrite `hc` using `[Finset.mem_range]`. Use extensionality with `l`. Simplify using `only [Finset.mem_filter, mem_sLe, mem_stripsUp, HStrip]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `⟨⟨h1, h2, by omega⟩, by omega⟩`. Introduce and unpack `⟨⟨h1, h2, h3⟩, h4⟩`. Use `hnn l h1` as an intermediate fact.

Conclude with `⟨h1, h2, by omega⟩`.
-/
lemma sum_sLe {n : ℕ} (κ : Fin n → ℤ) (b : ℕ) (f : (Fin n → ℤ) → ℕ) :
    ∑ l ∈ sLe κ b, f l = ∑ c ∈ Finset.range (b + 1), ∑ l ∈ stripsUp κ c, f l := by
  have hnn : ∀ l : Fin n → ℤ, (∀ m, κ m ≤ l m) → 0 ≤ ∑ m, l m - ∑ m, κ m := by
    intro l hl
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg (fun m _ => sub_nonneg.mpr (hl m))
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (s := sLe κ b) (t := Finset.range (b + 1))
    (g := fun l => (∑ m, l m - ∑ m, κ m).toNat) (by
      intro l hl
      rw [mem_sLe] at hl
      have := hnn l hl.1
      rw [Finset.mem_range]
      omega)]
  refine Finset.sum_congr rfl (fun c hc => Finset.sum_congr ?_ (fun _ _ => rfl))
  rw [Finset.mem_range] at hc
  ext l
  simp only [Finset.mem_filter, mem_sLe, mem_stripsUp, HStrip]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, by omega⟩, by omega⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    have := hnn l h1
    exact ⟨h1, h2, by omega⟩

def Lo {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) : Fin (n + 1) → ℤ :=
  fun j => max (μ j) ((Fin.snoc l (μ (Fin.last n)) : Fin (n + 1) → ℤ) j)

def Hi {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) : Fin n → ℤ :=
  fun i => min (μ i.castSucc) (l i)

/- English proof (translation)
Simplify using `[Lo]`.
-/
lemma Lo_castSucc {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) (i : Fin n) :
    Lo μ l i.castSucc = max (μ i.castSucc) (l i) := by
  simp [Lo]

/- English proof (translation)
Simplify using `[Lo]`.
-/
lemma Lo_last {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    Lo μ l (Fin.last n) = μ (Fin.last n) := by
  simp [Lo]

/- English proof (translation)
Rewrite using `[Fin.sum_univ_castSucc (Lo μ l), Fin.sum_univ_castSucc μ]`. Simplify using `only [Lo_castSucc, Lo_last, Hi]`. Establish `h : ∑ i : Fin n, (max (μ i.castSucc) (l i) + min (μ i.castSucc) (l i)) = ∑ i : Fin n, (μ i.castSucc + l i)` using `Finset.sum_congr rfl (fun i _ => by rw [add_comm]; exact min_add_max _ _)`. Rewrite `h` using `[Finset.sum_add_distrib, Finset.sum_add_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sum_Lo_Hi {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    ∑ j, Lo μ l j + ∑ i, Hi μ l i = ∑ j, μ j + ∑ i, l i := by
  rw [Fin.sum_univ_castSucc (Lo μ l), Fin.sum_univ_castSucc μ]
  simp only [Lo_castSucc, Lo_last, Hi]
  have h : ∑ i : Fin n, (max (μ i.castSucc) (l i) + min (μ i.castSucc) (l i)) =
      ∑ i : Fin n, (μ i.castSucc + l i) :=
    Finset.sum_congr rfl (fun i _ => by rw [add_comm]; exact min_add_max _ _)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
  linarith

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun j => le_trans (le_max_left _ _) (h j), fun i => ?_⟩` and prove the remaining obligations. Use `h i.castSucc` as an intermediate fact. Rewrite `this` using `[Lo_castSucc]`.

Conclude with `le_trans (le_max_right _ _) this`. Introduce and unpack `⟨h1, h2⟩ j`. Use `Fin.lastCases ?_ (fun i => ?_) j` and prove the remaining obligations. Rewrite using `[Lo_last]`. Conclude with `h1 _`.

Rewrite using `[Lo_castSucc]`. Conclude with `max_le (h1 _) (h2 i)`.
-/
lemma Lo_le_iff {n : ℕ} (μ ν : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    (∀ j, Lo μ l j ≤ ν j) ↔ (∀ j, μ j ≤ ν j) ∧ (∀ i : Fin n, l i ≤ ν i.castSucc) := by
  constructor
  · intro h
    refine ⟨fun j => le_trans (le_max_left _ _) (h j), fun i => ?_⟩
    have := h i.castSucc
    rw [Lo_castSucc] at this
    exact le_trans (le_max_right _ _) this
  · rintro ⟨h1, h2⟩ j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Lo_last]; exact h1 _
    · rw [Lo_castSucc]; exact max_le (h1 _) (h2 i)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun i => le_trans (le_max_left _ _) (h i), fun m m' hm => ?_⟩` and prove the remaining obligations. Establish `e : m.succ = m'.castSucc` using `Fin.ext (by simp only [Fin.val_succ, Fin.coe_castSucc]; exact hm)`. Use `h m` as an intermediate fact.

Unfold `Lo at this`. Rewrite `this` using `[e, Fin.snoc_castSucc]`. Conclude with `le_trans (le_max_right _ _) this`. Introduce and unpack `⟨h1, h2⟩ i`. Unfold `Lo`.

Use `max_le (h1 i) ?_` and prove the remaining obligations. Establish `hi0` using `i.isLt`. Distinguish the cases in `hi : i.val + 1 < n`. Establish `e : i.succ = (⟨i.val + 1, hi⟩ : Fin n).castSucc` using `Fin.ext (by simp only [Fin.val_succ, Fin.coe_castSucc])`. Rewrite using `[e, Fin.snoc_castSucc]`.

Conclude with `h2 i _ rfl`. Establish `e : i.succ = Fin.last n` using `Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)`. Rewrite using `[e, Fin.snoc_last, ← e]`. Conclude with `h1 i`.
-/
lemma Lo_succ_le_iff {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ l : Fin n → ℤ) :
    (∀ i : Fin n, Lo μ l i.succ ≤ κ i) ↔
      (∀ i : Fin n, μ i.succ ≤ κ i) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → l m' ≤ κ m) := by
  constructor
  · intro h
    refine ⟨fun i => le_trans (le_max_left _ _) (h i), fun m m' hm => ?_⟩
    have e : m.succ = m'.castSucc := Fin.ext (by simp only [Fin.val_succ, Fin.coe_castSucc]; exact hm)
    have := h m
    unfold Lo at this
    rw [e, Fin.snoc_castSucc] at this
    exact le_trans (le_max_right _ _) this
  · rintro ⟨h1, h2⟩ i
    unfold Lo
    refine max_le (h1 i) ?_
    have hi0 := i.isLt
    by_cases hi : i.val + 1 < n
    · have e : i.succ = (⟨i.val + 1, hi⟩ : Fin n).castSucc :=
        Fin.ext (by simp only [Fin.val_succ, Fin.coe_castSucc])
      rw [e, Fin.snoc_castSucc]
      exact h2 i _ rfl
    · have e : i.succ = Fin.last n := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
      rw [e, Fin.snoc_last, ← e]
      exact h1 i

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i`. Conclude with `h i.castSucc i.succ (by simp only [Fin.val_succ, Fin.coe_castSucc])`. Introduce `h m m' hm`. Establish `hlt : m.val < n` using `by have := m'.isLt; omega`.

Take `⟨i, rfl⟩ : ∃ i : Fin n, m = i.castSucc` from `⟨⟨m.val, hlt⟩, Fin.ext rfl⟩`. Simplify using `only [Fin.coe_castSucc] at hm`. Establish `e2 : m' = i.succ` using `Fin.ext (by simp only [Fin.val_succ]; omega)`. Substitute `e2` using the available equality. Conclude with `h i`.
-/
lemma strip2_iff {n : ℕ} (μ ν : Fin (n + 1) → ℤ) :
    (∀ m m' : Fin (n + 1), m.val + 1 = m'.val → ν m' ≤ μ m) ↔ ∀ i : Fin n, ν i.succ ≤ μ i.castSucc := by
  constructor
  · intro h i
    exact h i.castSucc i.succ (by simp only [Fin.val_succ, Fin.coe_castSucc])
  · intro h m m' hm
    have hlt : m.val < n := by have := m'.isLt; omega
    obtain ⟨i, rfl⟩ : ∃ i : Fin n, m = i.castSucc := ⟨⟨m.val, hlt⟩, Fin.ext rfl⟩
    simp only [Fin.coe_castSucc] at hm
    have e2 : m' = i.succ := Fin.ext (by simp only [Fin.val_succ]; omega)
    subst e2
    exact h i

/- English proof (translation)
Unfold `HStrip`. Rewrite using `[mem_gtBox, Lo_le_iff, strip2_iff]`. Simplify using `only [Hi, le_min_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2, h3⟩, h4⟩`.

Conclude with `⟨⟨h1, fun i => (h4 i).2⟩, fun i => ⟨h2 i, (h4 i).1⟩, h3⟩`. Introduce and unpack `⟨⟨h1, h2⟩, h3, h4⟩`. Conclude with `⟨⟨h1, fun i => (h3 i).1, h4⟩, fun i => ⟨(h3 i).2, h2 i⟩⟩`.
-/
lemma cond_up {n : ℕ} (μ ν : Fin (n + 1) → ℤ) (l : Fin n → ℤ) (b : ℕ) :
    (HStrip ν μ b ∧ l ∈ gtBox ν) ↔
      (∀ j, Lo μ l j ≤ ν j) ∧ (∀ i, ν i.succ ≤ Hi μ l i) ∧ ∑ j, ν j - ∑ j, μ j = (b : ℤ) := by
  unfold HStrip
  rw [mem_gtBox, Lo_le_iff, strip2_iff]
  simp only [Hi, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨⟨h1, fun i => (h4 i).2⟩, fun i => ⟨h2 i, (h4 i).1⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, fun i => (h3 i).1, h4⟩, fun i => ⟨(h3 i).2, h2 i⟩⟩

/- English proof (translation)
Rewrite using `[mem_gtBox, mem_sLe, Lo_succ_le_iff]`. Simplify using `only [Hi, le_min_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3, h4⟩`. Conclude with `⟨⟨fun i => (h1 i).1, h3⟩, fun i => ⟨(h1 i).2, h2 i⟩, h4⟩`.

Introduce and unpack `⟨⟨h1, h2⟩, h3, h4⟩`. Conclude with `⟨fun i => ⟨h1 i, (h3 i).1⟩, fun i => (h3 i).2, h2, h4⟩`.
-/
lemma cond_low {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ l : Fin n → ℤ) (b : ℕ) :
    (κ ∈ gtBox μ ∧ l ∈ sLe κ b) ↔
      (∀ i, Lo μ l i.succ ≤ κ i) ∧ (∀ i, κ i ≤ Hi μ l i) ∧ ∑ i, l i - ∑ i, κ i ≤ (b : ℤ) := by
  rw [mem_gtBox, mem_sLe, Lo_succ_le_iff]
  simp only [Hi, le_min_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨fun i => (h1 i).1, h3⟩, fun i => ⟨(h1 i).2, h2 i⟩, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun i => ⟨h1 i, (h3 i).1⟩, fun i => (h3 i).2, h2, h4⟩

def fw {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) (ν : Fin (n + 1) → ℤ) : Fin n → ℤ :=
  fun i => Lo μ l i.succ + Hi μ l i - ν i.succ

def bw {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) (b : ℕ) (κ : Fin n → ℤ) : Fin (n + 1) → ℤ :=
  Fin.cons (Lo μ l 0 + b - (∑ i, l i - ∑ i, κ i)) (fun i => Lo μ l i.succ + Hi μ l i - κ i)

/- English proof (translation)
Establish `h1` using `sum_Lo_Hi μ l`. Establish `h2` using `Fin.sum_univ_succ (Lo μ l)`. Establish `h3` using `Fin.sum_univ_succ ν`. Simplify using `only [fw, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sum_fw {n : ℕ} (μ ν : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    ∑ i, fw μ l ν i = ∑ j, μ j + ∑ i, l i - Lo μ l 0 - ∑ j, ν j + ν 0 := by
  have h1 := sum_Lo_Hi μ l
  have h2 := Fin.sum_univ_succ (Lo μ l)
  have h3 := Fin.sum_univ_succ ν
  simp only [fw, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith

/- English proof (translation)
Establish `h1` using `sum_Lo_Hi μ l`. Establish `h2` using `Fin.sum_univ_succ (Lo μ l)`. Rewrite using `[Fin.sum_univ_succ (bw μ l b κ)]`. Simplify using `only [bw, Fin.cons_zero, Fin.cons_succ, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sum_bw {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ l : Fin n → ℤ) (b : ℕ) :
    ∑ j, bw μ l b κ j = ∑ j, μ j + b := by
  have h1 := sum_Lo_Hi μ l
  have h2 := Fin.sum_univ_succ (Lo μ l)
  rw [Fin.sum_univ_succ (bw μ l b κ)]
  simp only [bw, Fin.cons_zero, Fin.cons_succ, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith

/- English proof (translation)
Rewrite using `[Finset.sum_sigma', Finset.sum_sigma']`. Use `Finset.sum_nbij' (fun x : (Σ _ : Fin (n + 1) → ℤ, Fin n → ℤ) => (⟨fw μ x.2 x.1, x.2⟩ : Σ _ : Fin n → ℤ, Fin n → ℤ)) (fun y : (Σ _ : Fin n → ℤ, Fin n → ℤ) => (⟨bw μ y.2 b y.1, y.2⟩ : Σ _ : Fin (n + 1) → ℤ, Fin n → ℤ)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨ν, l⟩ h`. Simplify using `only [Finset.mem_sigma, mem_stripsUp] at h`. Rewrite `h` using `[cond_up]`.

Simplify using `only [Finset.mem_sigma]`. Rewrite using `[cond_low]`. Take `⟨h1, h2, h3⟩` from `h`. Establish `hs` using `sum_fw μ ν l`. Use `⟨fun i => ?_, fun i => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [fw]`. Combine the linear relations using `[h2 i]`. Simplify using `only [fw]`. Combine the linear relations using `[h1 i.succ]`. Use `h1 0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce and unpack `⟨κ, l⟩ h`. Simplify using `only [Finset.mem_sigma] at h`. Rewrite `h` using `[cond_low]`. Simplify using `only [Finset.mem_sigma]`.

Rewrite using `[mem_stripsUp, cond_up]`. Take `⟨h1, h2, h3⟩` from `h`. Establish `hs` using `sum_bw μ κ l b`. Use `⟨fun j => ?_, fun i => ?_, by linarith⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations.

Simplify using `only [bw, Fin.cons_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [bw, Fin.cons_succ]`. Combine the linear relations using `[h2 i]`. Simplify using `only [bw, Fin.cons_succ]`.

Combine the linear relations using `[h1 i]`. Introduce and unpack `⟨ν, l⟩ h`. Simplify using `only [Finset.mem_sigma, mem_stripsUp] at h`. Establish `h3 : ∑ m, ν m - ∑ m, μ m = (b : ℤ)`. Establish `h'` using `h.1`.

Unfold `HStrip at h'`. Conclude with `h'.2.2`. Establish `hs` using `sum_fw μ ν l`. Use `show (⟨bw μ l b (fw μ l ν), l⟩ : Σ _ : Fin (n + 1) → ℤ, Fin n → ℤ) = ⟨ν, l⟩`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using `only [bw, Fin.cons_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [bw, Fin.cons_succ, fw]`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨κ, l⟩ _ show (⟨fw μ l (bw μ l b κ), l⟩ : Σ _ : Fin n → ℤ, Fin n → ℤ) = ⟨κ, l⟩`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [fw, bw, Fin.cons_succ]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `x _`. Both sides reduce to the same expression.
-/
lemma toggle_sum {n : ℕ} (μ : Fin (n + 1) → ℤ) (b : ℕ) (f : (Fin n → ℤ) → ℕ) :
    ∑ ν ∈ stripsUp μ b, ∑ l ∈ gtBox ν, f l = ∑ κ ∈ gtBox μ, ∑ l ∈ sLe κ b, f l := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x : (Σ _ : Fin (n + 1) → ℤ, Fin n → ℤ) => (⟨fw μ x.2 x.1, x.2⟩ : Σ _ : Fin n → ℤ, Fin n → ℤ))
    (fun y : (Σ _ : Fin n → ℤ, Fin n → ℤ) => (⟨bw μ y.2 b y.1, y.2⟩ : Σ _ : Fin (n + 1) → ℤ, Fin n → ℤ))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨ν, l⟩ h
    simp only [Finset.mem_sigma, mem_stripsUp] at h
    rw [cond_up] at h
    simp only [Finset.mem_sigma]
    rw [cond_low]
    obtain ⟨h1, h2, h3⟩ := h
    have hs := sum_fw μ ν l
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · simp only [fw]; linarith [h2 i]
    · simp only [fw]; linarith [h1 i.succ]
    · have := h1 0; linarith
  · rintro ⟨κ, l⟩ h
    simp only [Finset.mem_sigma] at h
    rw [cond_low] at h
    simp only [Finset.mem_sigma]
    rw [mem_stripsUp, cond_up]
    obtain ⟨h1, h2, h3⟩ := h
    have hs := sum_bw μ κ l b
    refine ⟨fun j => ?_, fun i => ?_, by linarith⟩
    · refine Fin.cases ?_ (fun i => ?_) j
      · simp only [bw, Fin.cons_zero]; linarith
      · simp only [bw, Fin.cons_succ]; linarith [h2 i]
    · simp only [bw, Fin.cons_succ]; linarith [h1 i]
  · rintro ⟨ν, l⟩ h
    simp only [Finset.mem_sigma, mem_stripsUp] at h
    have h3 : ∑ m, ν m - ∑ m, μ m = (b : ℤ) := by
      have h' := h.1
      unfold HStrip at h'
      exact h'.2.2
    have hs := sum_fw μ ν l
    show (⟨bw μ l b (fw μ l ν), l⟩ : Σ _ : Fin (n + 1) → ℤ, Fin n → ℤ) = ⟨ν, l⟩
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [bw, Fin.cons_zero]; linarith
    · simp only [bw, Fin.cons_succ, fw]; ring
  · rintro ⟨κ, l⟩ _
    show (⟨fw μ l (bw μ l b κ), l⟩ : Σ _ : Fin n → ℤ, Fin n → ℤ) = ⟨κ, l⟩
    congr 1
    funext i
    simp only [fw, bw, Fin.cons_succ]
    ring
  · intro x _
    rfl

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `zero => simp`. Consider the case `succ b ih`. Rewrite using `[Finset.sum_range_succ, ih, show n + (b + 1) - 1 = n + b by omega, show n + (b + 1) = n + b + 1 by omega, Nat.choose_succ_succ]`.
-/
lemma hockey (n b : ℕ) : ∑ c ∈ Finset.range (b + 1), (n + c - 1).choose c = (n + b).choose b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih, show n + (b + 1) - 1 = n + b by omega,
      show n + (b + 1) = n + b + 1 by omega, Nat.choose_succ_succ]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `μ b _`. Break down `Nat.eq_zero_or_pos b with rfl | hb` into its components or cases. Establish `e : stripsUp μ 0 = {μ}`.

Use extensionality with `ν`. Rewrite using `[mem_stripsUp, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `_`. Conclude with `Subsingleton.elim _ _`.

Introduce and unpack `rfl`. Unfold `HStrip`. Simplify using the standard rewrite rules. Rewrite using `[e, Finset.sum_singleton]`. Simplify using the standard rewrite rules.

Establish `e : stripsUp μ b = ∅`. Use extensionality with `ν`. Rewrite using `[mem_stripsUp]`. Simplify using `[HStrip]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e, Finset.sum_empty, Nat.choose_eq_zero_of_lt (by omega), mul_zero]`. Consider the case `succ n ih`. Introduce `μ b hμ`. Simplify using `only [dGT_succ]`. Rewrite using `[toggle_sum μ b (dGT n)]`.

Establish `e : ∀ κ ∈ gtBox μ, ∑ l ∈ sLe κ b, dGT n l = dGT n κ * (n + b).choose b`. Introduce `κ hκ`. Rewrite using `[sum_sLe, ← hockey n b, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Conclude with `ih κ c (antitone_of_mem_gtBox hμ hκ)`.

Rewrite using `[Finset.sum_congr rfl e, ← Finset.sum_mul, show n + 1 + b - 1 = n + b by omega]`.
-/
theorem up (n : ℕ) : ∀ (μ : Fin n → ℤ) (b : ℕ), Antitone μ →
    ∑ ν ∈ stripsUp μ b, dGT n ν = dGT n μ * (n + b - 1).choose b := by
  induction n with
  | zero =>
    intro μ b _
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have e : stripsUp μ 0 = {μ} := by
        ext ν
        rw [mem_stripsUp, Finset.mem_singleton]
        constructor
        · intro _
          exact Subsingleton.elim _ _
        · rintro rfl
          unfold HStrip
          simp
      rw [e, Finset.sum_singleton]
      simp
    · have e : stripsUp μ b = ∅ := by
        ext ν
        rw [mem_stripsUp]
        simp [HStrip]
        omega
      rw [e, Finset.sum_empty, Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  | succ n ih =>
    intro μ b hμ
    simp only [dGT_succ]
    rw [toggle_sum μ b (dGT n)]
    have e : ∀ κ ∈ gtBox μ, ∑ l ∈ sLe κ b, dGT n l = dGT n κ * (n + b).choose b := by
      intro κ hκ
      rw [sum_sLe, ← hockey n b, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      exact ih κ c (antitone_of_mem_gtBox hμ hκ)
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul, show n + 1 + b - 1 = n + b by omega]

def star {n : ℕ} (μ : Fin n → ℤ) : Fin n → ℤ := fun i => -μ (Fin.rev i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[star]`.
-/
lemma star_star {n : ℕ} (μ : Fin n → ℤ) : star (star μ) = μ := by
  funext i
  simp [star]

/- English proof (translation)
Introduce `i j hij`. Simplify using `only [star, neg_le_neg_iff]`. Conclude with `hμ (Fin.rev_le_rev.mpr hij)`.
-/
lemma antitone_star {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) : Antitone (star μ) := by
  intro i j hij
  simp only [star, neg_le_neg_iff]
  exact hμ (Fin.rev_le_rev.mpr hij)

/- English proof (translation)
Simplify using `only [star, Finset.sum_neg_distrib]`. Use `congr 1`. Conclude with `Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)`.
-/
lemma sum_star {n : ℕ} (μ : Fin n → ℤ) : ∑ i, star μ i = -∑ i, μ i := by
  simp only [star, Finset.sum_neg_distrib]
  congr 1
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)

/- English proof (translation)
Rewrite `h`, the goal using `[mem_gtBox]`. Introduce `i`. Simplify using `only [star]`. Establish `h1` using `h i.rev`. Rewrite using `[Fin.rev_succ, Fin.rev_castSucc]`.

Conclude with `⟨neg_le_neg h1.2, neg_le_neg h1.1⟩`.
-/
lemma star_mem_gtBox {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (h : κ ∈ gtBox μ) :
    star κ ∈ gtBox (star μ) := by
  rw [mem_gtBox] at h ⊢
  intro i
  simp only [star]
  have h1 := h i.rev
  rw [Fin.rev_succ, Fin.rev_castSucc]
  exact ⟨neg_le_neg h1.2, neg_le_neg h1.1⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `μ`. Rewrite using `[Subsingleton.elim (star μ) μ]`. Consider the case `succ n ih`.

Introduce `μ`. Rewrite using `[dGT_succ, dGT_succ]`. Use `Finset.sum_nbij' star star (fun κ hκ => ?_) (fun κ hκ => star_mem_gtBox hκ) (fun κ _ => star_star κ) (fun κ _ => star_star κ) (fun κ _ => (ih κ).symm)` and prove the remaining obligations. Simplify `star_mem_gtBox hκ` using `[star_star]`.
-/
lemma dGT_star (n : ℕ) : ∀ μ : Fin n → ℤ, dGT n (star μ) = dGT n μ := by
  induction n with
  | zero =>
    intro μ
    rw [Subsingleton.elim (star μ) μ]
  | succ n ih =>
    intro μ
    rw [dGT_succ, dGT_succ]
    refine Finset.sum_nbij' star star (fun κ hκ => ?_) (fun κ hκ => star_mem_gtBox hκ)
      (fun κ _ => star_star κ) (fun κ _ => star_star κ) (fun κ _ => (ih κ).symm)
    simpa [star_star] using star_mem_gtBox hκ

/- English proof (translation)
Unfold `HStrip at h ⊢`. Take `⟨h1, h2, h3⟩` from `h`. Use `⟨fun m => ?_, fun m m' hm => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [star]`. Conclude with `neg_le_neg (h1 _)`.

Simplify using `only [star]`. Apply `neg_le_neg` to reduce the goal to its premises. Apply `h2` to reduce the goal to its premises. Use `m'.isLt` as an intermediate fact. Simplify using `only [Fin.val_rev]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[sum_star, sum_star]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma HStrip_star {n : ℕ} {μ ν : Fin n → ℤ} {b : ℕ} (h : HStrip μ ν b) : HStrip (star ν) (star μ) b := by
  unfold HStrip at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun m => ?_, fun m m' hm => ?_, ?_⟩
  · simp only [star]
    exact neg_le_neg (h1 _)
  · simp only [star]
    apply neg_le_neg
    apply h2
    have := m'.isLt
    simp only [Fin.val_rev]
    omega
  · rw [sum_star, sum_star]
    linarith

/- English proof (translation)
Rewrite using `[← dGT_star n μ, ← up n (star μ) b (antitone_star hμ)]`. Use `Finset.sum_nbij' star star (fun ν hν => ?_) (fun ν hν => ?_) (fun ν _ => star_star ν) (fun ν _ => star_star ν) (fun ν _ => (dGT_star n ν).symm)` and prove the remaining obligations. Rewrite `hν` using `[mem_stripsDown]`. Rewrite using `[mem_stripsUp]`. Conclude with `HStrip_star hν`.

Rewrite `hν` using `[mem_stripsUp]`. Rewrite using `[mem_stripsDown]`. Simplify `HStrip_star hν` using `only [star_star]`.
-/
theorem down (n : ℕ) (μ : Fin n → ℤ) (b : ℕ) (hμ : Antitone μ) :
    ∑ ν ∈ stripsDown μ b, dGT n ν = dGT n μ * (n + b - 1).choose b := by
  rw [← dGT_star n μ, ← up n (star μ) b (antitone_star hμ)]
  refine Finset.sum_nbij' star star (fun ν hν => ?_) (fun ν hν => ?_)
    (fun ν _ => star_star ν) (fun ν _ => star_star ν) (fun ν _ => (dGT_star n ν).symm)
  · rw [mem_stripsDown] at hν
    rw [mem_stripsUp]
    exact HStrip_star hν
  · rw [mem_stripsUp] at hν
    rw [mem_stripsDown]
    simpa only [star_star] using HStrip_star hν

end Pieri

/- English proof (translation)
Unfold `StripsMem`. Use `first`. Consider the case `exact fun n μ ν b => ⟨Pieri.mem_stripsUp μ ν b, Pieri.mem_stripsDown μ ν b⟩`. Consider the case `exact ⟨fun n μ ν b => Pieri.mem_stripsUp μ ν b, fun n μ ν b => Pieri.mem_stripsDown μ ν b⟩`. Consider the case `done`.
-/
theorem strips_mem : StripsMem := by
  unfold StripsMem
  first
  | exact fun n μ ν b => ⟨Pieri.mem_stripsUp μ ν b, Pieri.mem_stripsDown μ ν b⟩
  | exact ⟨fun n μ ν b => Pieri.mem_stripsUp μ ν b, fun n μ ν b => Pieri.mem_stripsDown μ ν b⟩
  | done

/- English proof (translation)
Unfold `GTPieri`. Use `first`. Consider the case `exact fun n μ b hμ => ⟨Pieri.up n μ b hμ, Pieri.down n μ b hμ⟩`. Consider the case `exact ⟨fun n μ b hμ => Pieri.up n μ b hμ, fun n μ b hμ => Pieri.down n μ b hμ⟩`. Consider the case `done`.
-/
theorem gelfand_tsetlin_pieri : GTPieri := by
  unfold GTPieri
  first
  | exact fun n μ b hμ => ⟨Pieri.up n μ b hμ, Pieri.down n μ b hμ⟩
  | exact ⟨fun n μ b hμ => Pieri.up n μ b hμ, fun n μ b hμ => Pieri.down n μ b hμ⟩
  | done

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
