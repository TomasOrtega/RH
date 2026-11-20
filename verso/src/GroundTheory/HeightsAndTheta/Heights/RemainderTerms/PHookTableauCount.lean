import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
Establish `key : ∀ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v i - v j) = ∏ j : Fin (n + 1), if i < j then v i - v j else 1`. Introduce `i`. Rewrite using `[← Finset.prod_filter, Finset.filter_lt_eq_Ioi]`. Unfold `vandermondeOf`. Simplify using `only [key]`.

Rewrite using `[Fin.prod_univ_succ]`. Use `congr 1`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[Fin.succ_pos]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Fin.prod_univ_succ]`. Simplify using `only [Fin.succ_lt_succ_iff, Fin.not_lt_zero, if_false, one_mul]`. Rewrite using `[← Finset.prod_filter, Finset.filter_lt_eq_Ioi]`.
-/
theorem vandermondeOf_succ {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R) :
    vandermondeOf v =
      (∏ j : Fin n, (v 0 - v j.succ)) * vandermondeOf (fun j : Fin n => v j.succ) := by
  have key : ∀ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v i - v j) =
      ∏ j : Fin (n + 1), if i < j then v i - v j else 1 := by
    intro i
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  unfold vandermondeOf
  simp only [key]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.succ_lt_succ_iff, Fin.not_lt_zero, if_false, one_mul]
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]

/- English proof (translation)
Establish `hc : youngCells (fun _ : Fin m => (0 : ℕ)) = ∅`. Use extensionality with `c`. Simplify using `[youngCells]`. Establish `: IsEmpty (youngCells (fun _ : Fin m => (0 : ℕ)))` using `⟨fun p => by simpa [hc] using p.2⟩`. Establish `: IsEmpty (Fin (youngCells (fun _ : Fin m => (0 : ℕ))).card)`.

Rewrite using `[hc]`. Conclude with `Fin.isEmpty'`. Unfold `numStandardTable`. Rewrite using `[Nat.card_eq_one_iff_unique]`. Use `⟨⟨fun a b => Subtype.ext (Equiv.ext fun p => isEmptyElim p)⟩, ⟨⟨Equiv.equivOfIsEmpty _ _, fun p => isEmptyElim p⟩⟩⟩` and prove the remaining obligations.
-/
theorem numStandardTable_zero (m : ℕ) : numStandardTable (fun _ : Fin m => (0 : ℕ)) = 1 := by
  have hc : youngCells (fun _ : Fin m => (0 : ℕ)) = ∅ := by
    ext c
    simp [youngCells]
  have : IsEmpty (youngCells (fun _ : Fin m => (0 : ℕ))) :=
    ⟨fun p => by simpa [hc] using p.2⟩
  have : IsEmpty (Fin (youngCells (fun _ : Fin m => (0 : ℕ))).card) := by
    rw [hc]
    exact Fin.isEmpty'
  unfold numStandardTable
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (Equiv.ext fun p => isEmptyElim p)⟩,
    ⟨⟨Equiv.equivOfIsEmpty _ _, fun p => isEmptyElim p⟩⟩⟩

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ l ih => rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, mul_comm]`.
-/
theorem prod_range_sub_eq_descFactorial (n l : ℕ) :
    ∏ j ∈ Finset.range l, (n - j) = n.descFactorial l := by
  induction l with
  | zero => simp
  | succ l ih => rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, mul_comm]

/- English proof (translation)
Rewrite using `[Fin.prod_univ_eq_prod_range (fun j => l - j) l, ← Finset.prod_range_reflect (fun j => l - j) l]`. Establish `: ∀ j ∈ Finset.range l, l - (l - 1 - j) = j + 1`. Introduce `j hj`. Use `Finset.mem_range.1 hj` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finset.prod_congr rfl this, Finset.prod_range_add_one_eq_factorial]`.
-/
theorem prod_fin_sub_eq_factorial (l : ℕ) : ∏ j : Fin l, (l - (j : ℕ)) = l.factorial := by
  rw [Fin.prod_univ_eq_prod_range (fun j => l - j) l,
    ← Finset.prod_range_reflect (fun j => l - j) l]
  have : ∀ j ∈ Finset.range l, l - (l - 1 - j) = j + 1 := by
    intro j hj
    have := Finset.mem_range.1 hj
    omega
  rw [Finset.prod_congr rfl this, Finset.prod_range_add_one_eq_factorial]

/- English proof (translation)
Unfold `vandermondeOf`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vandermondeOf_add_const {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (c : R) :
    vandermondeOf (fun j => v j + c) = vandermondeOf v := by
  unfold vandermondeOf
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `hanti : Antitone (hookShape (l + 1) k l)`. Introduce `i j hij`. Establish `hij' : (i : ℕ) ≤ j` using `hij`. Unfold `hookShape`. Apply the tactic sequence `split_ifs <;> omega`.

Establish `e0 : hookShape (l + 1) k l 0 + (l + 1 - 1 - ((0 : Fin (l + 1)) : ℕ)) = k`. Simplify using `[hookShape]`. Use linear arithmetic over natural numbers and integers. Establish `es : ∀ j : Fin l, hookShape (l + 1) k l j.succ + (l + 1 - 1 - ((j.succ : Fin (l + 1)) : ℕ)) = (0 + (l - 1 - (j : ℕ))) + 1`. Introduce `j`.

Use `j.isLt` as an intermediate fact. Unfold `hookShape`. Rewrite using `[Fin.val_succ, if_neg (by omega), if_pos (by omega)]`. Use linear arithmetic over natural numbers and integers. Establish `hsum : ∑ i, hookShape (l + 1) k l i = k`.

Rewrite using `[Fin.sum_univ_succ]`. Establish `hs1 : ∀ j : Fin l, hookShape (l + 1) k l j.succ = 1` using `fun j => by`. Establish `h1` using `es j`. Establish `h2` using `j.isLt`. Establish `h3 : ((j.succ : Fin (l + 1)) : ℕ) = j + 1` using `Fin.val_succ j`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [hs1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]`. Use `e0` as an intermediate fact. Establish `hval : ((0 : Fin (l + 1)) : ℕ) = 0` using `rfl`. Use linear arithmetic over natural numbers and integers.

Establish `hf` using `h (l + 1) (hookShape (l + 1) k l) hanti`. Simplify using `only [vandermondeOf_succ, Fin.prod_univ_succ] at hf`. Rewrite `hf` using `[e0, hsum]`. Simplify using `only [es] at hf`. Establish `hz` using `h l (fun _ => 0) antitone_const`.

Use `beta_reduce at hz`. Rewrite `hz` using `[numStandardTable_zero]`. Simplify using `only [Finset.sum_const_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at hz`. Use `set V := vandermondeOf (fun j : Fin l => ((0 + (l - 1 - (j : ℕ)) : ℕ) : ℚ)) with hV`. Use `set P := ∏ j : Fin l, ((0 + (l - 1 - (j : ℕ))).factorial : ℚ) with hP`.

Establish `hP0 : P ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => by positivity`. Establish `hVP : V = P`. Clear denominators, using `at hz` for the nonvanishing conditions. Conclude with `hz.symm`. Establish `hshift : vandermondeOf (fun j : Fin l => (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ) : ℚ)) = V`.

Rewrite using `[hV, ← vandermondeOf_add_const (fun j : Fin l => ((0 + (l - 1 - (j : ℕ)) : ℕ) : ℚ)) 1]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hnum : ∏ j : Fin l, ((k : ℚ) - (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ) : ℚ)) = ((k - 1).descFactorial l : ℚ)`. Rewrite using `[← prod_range_sub_eq_descFactorial, Nat.cast_prod, ← Finset.prod_range_reflect (fun j => ((k - 1 - j : ℕ) : ℚ)) l, ← Fin.prod_univ_eq_prod_range (fun j => ((k - 1 - (l - 1 - j) : ℕ) : ℚ)) l]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `j.isLt` as an intermediate fact. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]`.

Use `push_cast`. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hden : ∏ j : Fin l, (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ).factorial : ℚ) = (l.factorial : ℚ) * P`.

Rewrite using `[hP, ← prod_fin_sub_eq_factorial, Nat.cast_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `j.isLt` as an intermediate fact. Rewrite using `[Nat.factorial_succ, Nat.cast_mul]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers. Rewrite `hf` using `[hnum, hshift, hden, hVP, Nat.descFactorial_eq_factorial_mul_choose]`. Establish `hk0 : ((k.factorial : ℕ) : ℚ) ≠ 0` using `by positivity`. Establish `hl0 : ((l.factorial : ℕ) : ℚ) ≠ 0` using `by positivity`. Establish `: (numStandardTable (hookShape (l + 1) k l) : ℚ) = ((k - 1).choose l : ℚ)`.

Rewrite using `[hf]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Conclude with `this` after adjusting the coercions.
-/
theorem numStandardTable_hookShape_succ (h : FrobeniusDimensionFormula.Statement) {k l : ℕ}
    (hlk : l < k) : numStandardTable (hookShape (l + 1) k l) = Nat.choose (k - 1) l := by
  have hanti : Antitone (hookShape (l + 1) k l) := by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    unfold hookShape
    split_ifs <;> omega
  have e0 : hookShape (l + 1) k l 0 + (l + 1 - 1 - ((0 : Fin (l + 1)) : ℕ)) = k := by
    simp [hookShape]
    omega
  have es : ∀ j : Fin l, hookShape (l + 1) k l j.succ + (l + 1 - 1 - ((j.succ : Fin (l + 1)) : ℕ)) =
      (0 + (l - 1 - (j : ℕ))) + 1 := by
    intro j
    have := j.isLt
    unfold hookShape
    rw [Fin.val_succ, if_neg (by omega), if_pos (by omega)]
    omega
  have hsum : ∑ i, hookShape (l + 1) k l i = k := by
    rw [Fin.sum_univ_succ]
    have hs1 : ∀ j : Fin l, hookShape (l + 1) k l j.succ = 1 := fun j => by
      have h1 := es j
      have h2 := j.isLt
      have h3 : ((j.succ : Fin (l + 1)) : ℕ) = j + 1 := Fin.val_succ j
      omega
    simp only [hs1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    have := e0
    have hval : ((0 : Fin (l + 1)) : ℕ) = 0 := rfl
    omega
  have hf := h (l + 1) (hookShape (l + 1) k l) hanti
  simp only [vandermondeOf_succ, Fin.prod_univ_succ] at hf
  rw [e0, hsum] at hf
  simp only [es] at hf
  have hz := h l (fun _ => 0) antitone_const
  beta_reduce at hz
  rw [numStandardTable_zero] at hz
  simp only [Finset.sum_const_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at hz
  set V := vandermondeOf (fun j : Fin l => ((0 + (l - 1 - (j : ℕ)) : ℕ) : ℚ)) with hV
  set P := ∏ j : Fin l, ((0 + (l - 1 - (j : ℕ))).factorial : ℚ) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => by positivity
  have hVP : V = P := by
    field_simp at hz
    exact hz.symm
  have hshift : vandermondeOf (fun j : Fin l => (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ) : ℚ)) = V := by
    rw [hV, ← vandermondeOf_add_const (fun j : Fin l => ((0 + (l - 1 - (j : ℕ)) : ℕ) : ℚ)) 1]
    congr 1
    funext j
    push_cast
    ring
  have hnum : ∏ j : Fin l, ((k : ℚ) - (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ) : ℚ)) =
      ((k - 1).descFactorial l : ℚ) := by
    rw [← prod_range_sub_eq_descFactorial, Nat.cast_prod,
      ← Finset.prod_range_reflect (fun j => ((k - 1 - j : ℕ) : ℚ)) l,
      ← Fin.prod_univ_eq_prod_range (fun j => ((k - 1 - (l - 1 - j) : ℕ) : ℚ)) l]
    refine Finset.prod_congr rfl fun j _ => ?_
    have := j.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hden : ∏ j : Fin l, (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ).factorial : ℚ) =
      (l.factorial : ℚ) * P := by
    rw [hP, ← prod_fin_sub_eq_factorial, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have := j.isLt
    rw [Nat.factorial_succ, Nat.cast_mul]
    congr 2
    omega
  rw [hnum, hshift, hden, hVP, Nat.descFactorial_eq_factorial_mul_choose] at hf
  have hk0 : ((k.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hl0 : ((l.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have : (numStandardTable (hookShape (l + 1) k l) : ℚ) = ((k - 1).choose l : ℚ) := by
    rw [hf]
    push_cast
    field_simp
  exact_mod_cast this

/- English proof (translation)
Introduce `r k l hlk hlr`. Rewrite using `[← YoungDiagramCombinatorics.numSYT_hookShape r k l hlr, YoungDiagramCombinatorics.numSYT_hookShape (l + 1) k l (by omega)]`. Conclude with `numStandardTable_hookShape_succ h hlk`.
-/
theorem HookTableauCount.proof (h : FrobeniusDimensionFormula.Statement) :
    HookTableauCount.Statement := by
  intro r k l hlk hlr
  rw [← YoungDiagramCombinatorics.numSYT_hookShape r k l hlr, YoungDiagramCombinatorics.numSYT_hookShape (l + 1) k l (by omega)]
  exact numStandardTable_hookShape_succ h hlk

end GroundTheory.Heights₂.Heights.RestTerms
