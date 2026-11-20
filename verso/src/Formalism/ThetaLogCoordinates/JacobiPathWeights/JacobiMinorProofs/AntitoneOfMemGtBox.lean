import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementP

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace Pieri

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma sub_le_sum_sub {n : ℕ} (ν μ : Fin n → ℤ) (h : ∀ m, μ m ≤ ν m) (i : Fin n) :
    ν i - μ i ≤ ∑ m, ν m - ∑ m, μ m := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.single_le_sum (f := fun m => ν m - μ m) (fun m _ => sub_nonneg.mpr (h m))
    (Finset.mem_univ i)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
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
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
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
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
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
Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.
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
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact. Supply the required witnesses or components. A detailed English derivation is pending.
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
Simplify using the standard rewrite rules.
-/
lemma Lo_castSucc {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) (i : Fin n) :
    Lo μ l i.castSucc = max (μ i.castSucc) (l i) := by
  simp [Lo]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma Lo_last {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    Lo μ l (Fin.last n) = μ (Fin.last n) := by
  simp [Lo]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
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
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Establish an intermediate fact. Substitute using the available equality. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
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
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
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
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sum_fw {n : ℕ} (μ ν : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    ∑ i, fw μ l ν i = ∑ j, μ j + ∑ i, l i - Lo μ l 0 - ∑ j, ν j + ν 0 := by
  have h1 := sum_Lo_Hi μ l
  have h2 := Fin.sum_univ_succ (Lo μ l)
  have h3 := Fin.sum_univ_succ ν
  simp only [fw, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sum_bw {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ l : Fin n → ℤ) (b : ℕ) :
    ∑ j, bw μ l b κ j = ∑ j, μ j + b := by
  have h1 := sum_Lo_Hi μ l
  have h2 := Fin.sum_univ_succ (Lo μ l)
  rw [Fin.sum_univ_succ (bw μ l b κ)]
  simp only [bw, Fin.cons_zero, Fin.cons_succ, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Establish an intermediate fact. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Assume the hypotheses and unpack their components.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses.

Both sides reduce to the same expression. A detailed English derivation is pending.
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
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
lemma hockey (n b : ℕ) : ∑ c ∈ Finset.range (b + 1), (n + c - 1).choose c = (n + b).choose b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih, show n + (b + 1) - 1 = n + b by omega,
      show n + (b + 1) = n + b + 1 by omega, Nat.choose_succ_succ]

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the hypotheses and unpack their components.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
lemma star_star {n : ℕ} (μ : Fin n → ℤ) : star (star μ) = μ := by
  funext i
  simp [star]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma antitone_star {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) : Antitone (star μ) := by
  intro i j hij
  simp only [star, neg_le_neg_iff]
  exact hμ (Fin.rev_le_rev.mpr hij)

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
lemma sum_star {n : ℕ} (μ : Fin n → ℤ) : ∑ i, star μ i = -∑ i, μ i := by
  simp only [star, Finset.sum_neg_distrib]
  congr 1
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components.
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
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
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
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem strips_mem : StripsMem := by
  unfold StripsMem
  first
  | exact fun n μ ν b => ⟨Pieri.mem_stripsUp μ ν b, Pieri.mem_stripsDown μ ν b⟩
  | exact ⟨fun n μ ν b => Pieri.mem_stripsUp μ ν b, fun n μ ν b => Pieri.mem_stripsDown μ ν b⟩
  | done

/- English proof (translation)
Replace the relevant objects with their definitions. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem gelfand_tsetlin_pieri : GTPieri := by
  unfold GTPieri
  first
  | exact fun n μ b hμ => ⟨Pieri.up n μ b hμ, Pieri.down n μ b hμ⟩
  | exact ⟨fun n μ b hμ => Pieri.up n μ b hμ, fun n μ b hμ => Pieri.down n μ b hμ⟩
  | done

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
