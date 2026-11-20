import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.JointShapeUniq

/- English proof (translation)
Simplify using `[pad]`. Use linear arithmetic over natural numbers and integers.
-/
theorem length_pad {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) :
    (pad x (n - x.length - y.length) y).length = n := by
  simp [pad]; omega

/- English proof (translation)
Substitute `h` using the available equality. Use `List.ext_getElem (by simp) fun i h1 h2 => ?_` and prove the remaining obligations. Simplify using `[List.getElem?_eq_getElem h2]`.
-/
theorem ofFn_getD {L : List ℚ} {n : ℕ} (h : L.length = n) :
    List.ofFn (fun i : Fin n => L.getD i 0) = L := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem?_eq_getElem h2]

/- English proof (translation)
Rewrite using `[List.filter_append, List.filter_append, List.filter_eq_self.2 (by simpa using hx), List.filter_eq_nil_iff.2 (by simp), List.filter_eq_nil_iff.2 (fun v hv => by have := hy v hv; simp; omega)]`. Simplify using the standard rewrite rules.
-/
theorem filter_pos {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) (k : ℕ) :
    (x ++ List.replicate k 0 ++ y).filter (fun v => decide (0 < v)) = x := by
  rw [List.filter_append, List.filter_append, List.filter_eq_self.2 (by simpa using hx),
    List.filter_eq_nil_iff.2 (by simp),
    List.filter_eq_nil_iff.2 (fun v hv => by have := hy v hv; simp; omega)]
  simp

/- English proof (translation)
Rewrite using `[List.filter_append, List.filter_append, List.filter_eq_nil_iff.2 (fun v hv => by have := hx v hv; simp; omega), List.filter_eq_nil_iff.2 (by simp), List.filter_eq_self.2 (by simpa using hy)]`. Simplify using the standard rewrite rules.
-/
theorem filter_neg {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) (k : ℕ) :
    (x ++ List.replicate k 0 ++ y).filter (fun v => decide (v < 0)) = y := by
  rw [List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.2 (fun v hv => by have := hx v hv; simp; omega),
    List.filter_eq_nil_iff.2 (by simp), List.filter_eq_self.2 (by simpa using hy)]
  simp

/- English proof (translation)
Establish `e1 : pad x (n - x.length - y.length) y = pad x' (n - x'.length - y'.length) y'`. Rewrite using `[← ofFn_getD (length_pad h), ← ofFn_getD (length_pad h'), funext e]`. Establish `e2` using `List.map_injective_iff.2 (Int.cast_injective (α := ℚ)) e1`. Conclude with `⟨by rw [← filter_pos hx hy, e2, filter_pos hx' hy'], by rw [← filter_neg hx hy, e2, filter_neg hx' hy']⟩`.
-/
theorem pad_inj {x y x' y' : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0)
    (hx' : ∀ v ∈ x', 0 < v) (hy' : ∀ v ∈ y', v < 0) {n : ℕ}
    (h : x.length + y.length ≤ n) (h' : x'.length + y'.length ≤ n)
    (e : ∀ i : Fin n, (pad x (n - x.length - y.length) y).getD i 0 =
      (pad x' (n - x'.length - y'.length) y').getD i 0) : x = x' ∧ y = y' := by
  have e1 : pad x (n - x.length - y.length) y = pad x' (n - x'.length - y'.length) y' := by
    rw [← ofFn_getD (length_pad h), ← ofFn_getD (length_pad h'), funext e]
  have e2 := List.map_injective_iff.2 (Int.cast_injective (α := ℚ)) e1
  exact ⟨by rw [← filter_pos hx hy, e2, filter_pos hx' hy'],
    by rw [← filter_neg hx hy, e2, filter_neg hx' hy']⟩

def absSum (x : List ℤ) : ℚ := (x.map fun v : ℤ => |(v : ℚ)|).sum

/- English proof (translation)
Establish `: ∑ i : Fin n, |(pad x (n - x.length - y.length) y).getD i 0| = ((pad x (n - x.length - y.length) y).map fun v => |v|).sum` using `by conv_rhs => rw [← ofFn_getD (length_pad h), List.map_ofFn, List.sum_ofFn]`. Both sides reduce to the same expression. Rewrite using `[this]`. Simplify using `[pad, absSum, Function.comp_def]`.
-/
theorem sum_abs_pad {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) :
    ∑ i : Fin n, |(pad x (n - x.length - y.length) y).getD i 0| = absSum x + absSum y := by
  have : ∑ i : Fin n, |(pad x (n - x.length - y.length) y).getD i 0| =
      ((pad x (n - x.length - y.length) y).map fun v => |v|).sum := by
    conv_rhs => rw [← ofFn_getD (length_pad h), List.map_ofFn, List.sum_ofFn]
    rfl
  rw [this]
  simp [pad, absSum, Function.comp_def]

/- English proof (translation)
Introduce `μ μ₁ h`. Use function extensionality and compare the values at `a`. Use `congrFun h a` as an intermediate fact. Apply the tactic sequence `rcases a with a | a <;> simpa [shiftNu] using this`.
-/
theorem shiftNu_injective {p q : ℕ} (c : ℚ) :
    Function.Injective (shiftNu (p := p) (q := q) c) := by
  intro μ μ₁ h
  funext a
  have := congrFun h a
  rcases a with a | a <;> simpa [shiftNu] using this

/- English proof (translation)
Introduce `p q r s μ μ₁ μ' μ₁' h h₁`. Take `⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, l1, l2, l3, l4, e1, e2⟩` from `h`. Take `⟨a', b', c', d', ha', hc', hb', hd', -, -, -, -, l1', l2', l3', l4', e1', e2'⟩` from `h₁`. Use `⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩` and prove the remaining obligations. Substitute `h` using the available equality.

Establish `e` using `e1.symm.trans e1'`. Take `⟨rfl, rfl⟩` from `pad_inj ha hb ha' hb' l1 l1' fun i => congrFun e (.inl i)`. Take `⟨rfl, rfl⟩` from `pad_inj hc hd hc' hd' l2 l2' fun i => congrFun e (.inr i)`. Conclude with `shiftNu_injective _ (e2.trans e2'.symm)`. Substitute `h` using the available equality.

Establish `e` using `e2.symm.trans e2'`. Take `⟨rfl, rfl⟩` from `pad_inj ha hd ha' hd' l3 l3' fun i => congrFun e (.inl i)`. Take `⟨rfl, rfl⟩` from `pad_inj hc hb hc' hb' l4 l4' fun i => congrFun e (.inr i)`. Conclude with `shiftNu_injective _ (e1.trans e1'.symm)`. Simplify using `only [degW, e1, e2, Fintype.sum_sum_type, ofBlocks]`.

Rewrite using `[sum_abs_pad l1, sum_abs_pad l2, sum_abs_pad l3, sum_abs_pad l4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jointShape_unique_deg : ∀ (p q r s : ℕ) (μ μ₁ : Ix p q → ℚ) (μ' μ₁' : Ix r s → ℚ),
    JointShape p q r s μ μ' → JointShape p q r s μ₁ μ₁' →
      (μ = μ₁ ↔ μ' = μ₁') ∧ degW (cPair r s) μ = degW (cPair p q) μ' := by
  intro p q r s μ μ₁ μ' μ₁' h h₁
  obtain ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, l1, l2, l3, l4, e1, e2⟩ := h
  obtain ⟨a', b', c', d', ha', hc', hb', hd', -, -, -, -, l1', l2', l3', l4', e1', e2'⟩ := h₁
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · subst h
    have e := e1.symm.trans e1'
    obtain ⟨rfl, rfl⟩ := pad_inj ha hb ha' hb' l1 l1' fun i => congrFun e (.inl i)
    obtain ⟨rfl, rfl⟩ := pad_inj hc hd hc' hd' l2 l2' fun i => congrFun e (.inr i)
    exact shiftNu_injective _ (e2.trans e2'.symm)
  · subst h
    have e := e2.symm.trans e2'
    obtain ⟨rfl, rfl⟩ := pad_inj ha hd ha' hd' l3 l3' fun i => congrFun e (.inl i)
    obtain ⟨rfl, rfl⟩ := pad_inj hc hb hc' hb' l4 l4' fun i => congrFun e (.inr i)
    exact shiftNu_injective _ (e1.trans e1'.symm)
  · simp only [degW, e1, e2, Fintype.sum_sum_type, ofBlocks]
    rw [sum_abs_pad l1, sum_abs_pad l2, sum_abs_pad l3, sum_abs_pad l4]
    ring

end GlobalTheory.JointShapeUniq
