import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace Formalism.MainNotions.J

open Finset Matrix

section Pattern

variable {n : ℕ} {F : Type} [Field F]

def Pat (S : Finset (Fin n × Fin n)) (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, (i, j) ∉ S → A i j = if i = j then 1 else 0

/- English proof (translation)
Establish `ht : A.BlockTriangular id`. Introduce `i j hij`. Establish `hn : (i, j) ∉ S` using `fun hm => absurd (hS _ hm) (not_lt.mpr (le_of_lt hij))`. Establish `hij' : j < i` using `hij`. Rewrite using `[h i j hn, if_neg (ne_of_gt hij')]`.

Rewrite using `[Matrix.det_of_isUpperTriangular ht]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Establish `hn : (i, i) ∉ S` using `fun hm => lt_irrefl _ (hS _ hm)`. Rewrite using `[h i i hn, if_pos rfl]`.
-/
theorem pat_det (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) (A : Matrix (Fin n) (Fin n) F)
    (h : Pat S A) : A.det = 1 := by
  have ht : A.BlockTriangular id := by
    intro i j hij
    have hn : (i, j) ∉ S := fun hm => absurd (hS _ hm) (not_lt.mpr (le_of_lt hij))
    have hij' : j < i := hij
    rw [h i j hn, if_neg (ne_of_gt hij')]
  rw [Matrix.det_of_isUpperTriangular ht]
  refine Finset.prod_eq_one fun i _ => ?_
  have hn : (i, i) ∉ S := fun hm => lt_irrefl _ (hS _ hm)
  rw [h i i hn, if_pos rfl]

def patMat (S : Finset (Fin n × Fin n)) (φ : S → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if h : (i, j) ∈ S then φ ⟨(i, j), h⟩ else if i = j then 1 else 0

/- English proof (translation)
Introduce `i j h` and use `by simp [patMat, h]`.
-/
theorem patMat_pat (S : Finset (Fin n × Fin n)) (φ : S → F) : Pat S (patMat S φ) := fun i j h => by
  simp [patMat, h]

def patEquiv (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) :
    {A : GL (Fin n) F // Pat S (A : Matrix (Fin n) (Fin n) F)} ≃ (S → F) where
  toFun A := fun p => (A.1 : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2
  invFun φ := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (patMat S φ)
    (by rw [pat_det S hS _ (patMat_pat S φ)]; exact one_ne_zero), patMat_pat S φ⟩
  left_inv A := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    show patMat S (fun p => (A.1 : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2) i j = (A.1 : Matrix (Fin n) (Fin n) F) i j
    by_cases h : (i, j) ∈ S
    · simp [patMat, h]
    · simp [patMat, h, A.2 i j h]
  right_inv φ := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    show patMat S φ i j = _
    simp [patMat, h]

/- English proof (translation)
Rewrite using `[Nat.card_congr (patEquiv S hS), Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]`.
-/
theorem card_pat [Finite F] (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) :
    Nat.card {A : GL (Fin n) F // Pat S (A : Matrix (Fin n) (Fin n) F)} = Nat.card F ^ S.card := by
  rw [Nat.card_congr (patEquiv S hS), Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]

end Pattern

def upS (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

/- English proof (translation)
Unfold `upS`. Rewrite using `[Finset.card_filter, Fintype.sum_prod_type_right]`. Establish `: ∀ j : Fin n, (∑ i : Fin n, if i < j then 1 else 0) = (j : ℕ)`. Introduce `j`. Rewrite using `[← Finset.card_filter]`.

Establish `: (univ.filter fun i : Fin n => i < j) = Finset.Iio j` using `by ext; simp`. Rewrite using `[this, Fin.card_Iio]`. Simplify using `only [this]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]`.
-/
theorem card_upS (n : ℕ) : (upS n).card = n * (n - 1) / 2 := by
  unfold upS
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have : ∀ j : Fin n, (∑ i : Fin n, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have : (univ.filter fun i : Fin n => i < j) = Finset.Iio j := by ext; simp
    rw [this, Fin.card_Iio]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

def rowS (k rS n : ℕ) : Finset (Fin n × Fin n) :=
  (upS n).filter fun p => ¬ (p.2.val = rS + k ∧ rS ≤ p.1.val)

/- English proof (translation)
Establish `h` using `Finset.card_filter_add_card_filter_not (s := upS n) (fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val)`. Rewrite `h` using `[card_upS]`. Establish `hk : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val).card = k`. Establish `: ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val) = (univ : Finset (Fin k)).image fun i => ((⟨rS + i.val, by omega⟩ : Fin n), (⟨rS + k, hn⟩ : Fin n))`. Use extensionality with `⟨a, b⟩`.

Simplify using `only [upS, mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hab, hb, ha⟩`. Establish `hab' : a.val < b.val` using `hab`. Conclude with `⟨⟨a.val - rS, by omega⟩, Fin.ext (by simp; omega), Fin.ext (by simp [hb])⟩`.

Introduce and unpack `⟨i, rfl, rfl⟩`. Use `⟨?_, rfl, by simp⟩` and prove the remaining obligations. Use `show rS + i.val < rS + k`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]`.

Introduce `i j hij`. Use `congrArg (fun p : Fin n × Fin n => p.1.val) hij` as an intermediate fact. Simplify using `at this`. Conclude with `Fin.ext this`. Unfold `rowS`.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_rowS (k rS n : ℕ) (hn : rS + k < n) : (rowS k rS n).card + k = n * (n - 1) / 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := upS n)
    (fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val)
  rw [card_upS] at h
  have hk : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val).card = k := by
    have : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val) =
        (univ : Finset (Fin k)).image fun i => ((⟨rS + i.val, by omega⟩ : Fin n), (⟨rS + k, hn⟩ : Fin n)) := by
      ext ⟨a, b⟩
      simp only [upS, mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨hab, hb, ha⟩
        have hab' : a.val < b.val := hab
        exact ⟨⟨a.val - rS, by omega⟩, Fin.ext (by simp; omega), Fin.ext (by simp [hb])⟩
      · rintro ⟨i, rfl, rfl⟩
        refine ⟨?_, rfl, by simp⟩
        show rS + i.val < rS + k
        omega
    rw [this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro i j hij
    have := congrArg (fun p : Fin n × Fin n => p.1.val) hij
    simp at this
    exact Fin.ext this
  unfold rowS
  omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i j hij`. Simplify using `only [upS, mem_filter, mem_univ, true_and, not_lt] at hij`. Break down `eq_or_lt_of_le hij with h | h` into its components or cases. Substitute `h` using the available equality.

Simplify using `[h2]`. Rewrite using `[h1 i j h, if_neg (ne_of_gt h)]`. Introduce `h`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[h i j (by simp [upS, le_of_lt hij]), if_neg (ne_of_gt hij)]`.

Rewrite using `[h i i (by simp [upS]), if_pos rfl]`.
-/
theorem isUnitri_iff {n : ℕ} {F : Type} [Field F] (A : Matrix (Fin n) (Fin n) F) :
    StandardLattice.IsUnitri A ↔ Pat (upS n) A := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    simp only [upS, mem_filter, mem_univ, true_and, not_lt] at hij
    rcases eq_or_lt_of_le hij with h | h
    · subst h; simp [h2]
    · rw [h1 i j h, if_neg (ne_of_gt h)]
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [h i j (by simp [upS, le_of_lt hij]), if_neg (ne_of_gt hij)]
    · rw [h i i (by simp [upS]), if_pos rfl]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3, h4⟩ i j hij`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using `[h2]`.

Rewrite using `[if_neg e]`. Establish `e' : i.val ≠ j.val` using `fun h => e (Fin.ext h)`. Simplify using `only [rowS, upS, mem_filter, mem_univ, true_and, not_and] at hij`. Distinguish the cases in `hlt : i < j`. Choose the witnesses or unpack the hypotheses as in `⟨hj, hi⟩ : j.val = rS + k ∧ rS ≤ i.val := by`.

Assume the negation of the conclusion as `hc`. Conclude with `hij hlt (fun a b => hc ⟨a, b⟩)`. Establish `hlt' : i.val < j.val` using `hlt`. Apply the tactic sequence `exact h4 i j hj e (by unfold StandardLattice.blk; split_ifs <;> omega)`. Establish `hlt' : j.val < i.val`.

Establish `: ¬ i.val < j.val` using `hlt`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hb : StandardLattice.blk rS k j.val < StandardLattice.blk rS k i.val`. Conclude with `h1 i j hb`. Use `h3 i j ?_ hlt' revert hb` and prove the remaining obligations.

Unfold `StandardLattice.blk`. Apply the tactic sequence `split_ifs <;> omega`. Introduce `h`. Use `⟨fun i j hij => ?_, fun i => ?_, fun i j hb hij => ?_, fun i j hj hne hb => ?_⟩` and prove the remaining obligations. Establish `hlt : j.val < i.val` using `by revert hij`.

Unfold `StandardLattice.blk`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hlt2 : ¬ i < j` using `fun hh => by`. Establish `: i.val < j.val` using `hh`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h i j (by simp [rowS, upS, hlt2]), if_neg (fun e => by subst e; omega)]`. Rewrite using `[h i i (by simp [rowS, upS]), if_pos rfl]`. Establish `hlt2 : ¬ i < j` using `not_lt.mpr (le_of_lt hij)`. Rewrite using `[h i j (by simp [rowS, upS, hlt2]), if_neg (ne_of_gt hij)]`. Establish `hi : rS ≤ i.val` using `by revert hb`.

Unfold `StandardLattice.blk`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[h i j (by simp [rowS, hj, hi]), if_neg hne]`.
-/
theorem isRowLev_iff {n : ℕ} {F : Type} [Field F] (k rS : ℕ) (A : Matrix (Fin n) (Fin n) F) :
    StandardLattice.IsRowLev k rS A ↔ Pat (rowS k rS n) A := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ i j hij
    by_cases e : i = j
    · subst e; simp [h2]
    rw [if_neg e]
    have e' : i.val ≠ j.val := fun h => e (Fin.ext h)
    simp only [rowS, upS, mem_filter, mem_univ, true_and, not_and] at hij
    by_cases hlt : i < j
    · obtain ⟨hj, hi⟩ : j.val = rS + k ∧ rS ≤ i.val := by
        by_contra hc
        exact hij hlt (fun a b => hc ⟨a, b⟩)
      have hlt' : i.val < j.val := hlt
      exact h4 i j hj e (by unfold StandardLattice.blk; split_ifs <;> omega)
    · have hlt' : j.val < i.val := by
        have : ¬ i.val < j.val := hlt
        omega
      by_cases hb : StandardLattice.blk rS k j.val < StandardLattice.blk rS k i.val
      · exact h1 i j hb
      · refine h3 i j ?_ hlt'
        revert hb
        unfold StandardLattice.blk
        split_ifs <;> omega
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hb hij => ?_, fun i j hj hne hb => ?_⟩
    · have hlt : j.val < i.val := by
        revert hij
        unfold StandardLattice.blk
        split_ifs <;> omega
      have hlt2 : ¬ i < j := fun hh => by
        have : i.val < j.val := hh
        omega
      rw [h i j (by simp [rowS, upS, hlt2]), if_neg (fun e => by subst e; omega)]
    · rw [h i i (by simp [rowS, upS]), if_pos rfl]
    · have hlt2 : ¬ i < j := not_lt.mpr (le_of_lt hij)
      rw [h i j (by simp [rowS, upS, hlt2]), if_neg (ne_of_gt hij)]
    · have hi : rS ≤ i.val := by
        revert hb
        unfold StandardLattice.blk
        split_ifs <;> omega
      rw [h i j (by simp [rowS, hj, hi]), if_neg hne]

end Formalism.MainNotions.J

end
