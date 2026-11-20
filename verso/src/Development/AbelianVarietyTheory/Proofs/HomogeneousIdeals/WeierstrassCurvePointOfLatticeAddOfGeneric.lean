import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero

open Filter PeriodPair WeierstrassCurve
open scoped Topology

noncomputable section

namespace GlobalTheory

variable (L : PeriodPair)

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Rewrite using `[← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]`. Establish `h` using `derivWeierstrassP_sq L z hz`. Simplify using `only [_root_.GlobalTheory.latticeCurve]`. Take the linear combination `h / 4`.
-/
theorem _root_.GlobalTheory.latticeCurve_nonsingular {z : ℂ} (hz : z ∉ L.lattice) :
    (_root_.GlobalTheory.latticeCurve L).toAffine.Nonsingular (℘[L] z) (℘'[L] z / 2) := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]
  have h := derivWeierstrassP_sq L z hz
  simp only [_root_.GlobalTheory.latticeCurve]
  linear_combination h / 4

open Classical in

def latticePoint (z : ℂ) : (latticeCurve L).toAffine.Point :=
  if hz : z ∈ L.lattice then 0 else .some _ _ (latticeCurve_nonsingular L hz)

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.latticePoint, dif_pos hz]`.
-/
theorem _root_.GlobalTheory.latticePoint_of_mem {z : ℂ} (hz : z ∈ L.lattice) :
    _root_.GlobalTheory.latticePoint L z = 0 := by
  rw [_root_.GlobalTheory.latticePoint, dif_pos hz]

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.latticePoint, dif_neg hz]`.
-/
theorem _root_.GlobalTheory.latticePoint_of_notMem {z : ℂ} (hz : z ∉ L.lattice) :
    _root_.GlobalTheory.latticePoint L z =
      .some (℘[L] z) (℘'[L] z / 2) (_root_.GlobalTheory.latticeCurve_nonsingular L hz) := by
  rw [_root_.GlobalTheory.latticePoint, dif_neg hz]

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hz`. Rewrite `h` using `[_root_.GlobalTheory.latticePoint_of_notMem L hz]`. Conclude with `WeierstrassCurve.Affine.Point.some_ne_zero _ h`.

Conclude with `_root_.GlobalTheory.latticePoint_of_mem L`.
-/
theorem _root_.GlobalTheory.latticePoint_eq_zero_iff {z : ℂ} :
    _root_.GlobalTheory.latticePoint L z = 0 ↔ z ∈ L.lattice := by
  constructor
  · intro h
    by_contra hz
    rw [_root_.GlobalTheory.latticePoint_of_notMem L hz] at h
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ h
  · exact _root_.GlobalTheory.latticePoint_of_mem L

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Distinguish the cases in `hz : z ∈ L.lattice`. Rewrite using `[_root_.GlobalTheory.latticePoint_of_mem L hz, _root_.GlobalTheory.latticePoint_of_mem L (neg_mem hz), neg_zero]`. Establish `hz' : -z ∉ L.lattice` using `fun h => hz (by simpa using neg_mem h)`. Rewrite using `[_root_.GlobalTheory.latticePoint_of_notMem L hz, _root_.GlobalTheory.latticePoint_of_notMem L hz', WeierstrassCurve.Affine.Point.neg_some]`. Apply the tactic sequence `simp [weierstrassP_neg, derivWeierstrassP_neg, WeierstrassCurve.Affine.negY, _root_.GlobalTheory.latticeCurve] <;> ring`.
-/
theorem _root_.GlobalTheory.latticePoint_neg (z : ℂ) :
    _root_.GlobalTheory.latticePoint L (-z) = -_root_.GlobalTheory.latticePoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [_root_.GlobalTheory.latticePoint_of_mem L hz,
      _root_.GlobalTheory.latticePoint_of_mem L (neg_mem hz), neg_zero]
  · have hz' : -z ∉ L.lattice := fun h => hz (by simpa using neg_mem h)
    rw [_root_.GlobalTheory.latticePoint_of_notMem L hz, _root_.GlobalTheory.latticePoint_of_notMem L hz',
      WeierstrassCurve.Affine.Point.neg_some]
    simp [weierstrassP_neg, derivWeierstrassP_neg, WeierstrassCurve.Affine.negY,
      _root_.GlobalTheory.latticeCurve] <;> ring

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Introduce `P`. Consider the cases of `P with`. Consider the case `zero => exact ⟨0, _root_.GlobalTheory.latticePoint_of_mem L (zero_mem _)⟩`. Consider the case `some x y h`. Establish `he` using `h.1`.

Rewrite `he` using `[WeierstrassCurve.Affine.equation_iff]`. Simplify using `only [_root_.GlobalTheory.latticeCurve] at he`. Take `⟨z, hz, hx, hy⟩` from `_root_.GlobalTheory.exists_weierstrassP_eq_and_derivWeierstrassP_eq L (x := x) (y := 2 * y) (by linear_combination 4 * he)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.GlobalTheory.latticePoint_of_notMem L hz]`.

Simplify using `only [WeierstrassCurve.Affine.Point.some.injEq]`. Conclude with `⟨hx, by rw [hy]; ring⟩`.
-/
theorem _root_.GlobalTheory.latticePoint_surjective :
    Function.Surjective (_root_.GlobalTheory.latticePoint L) := by
  intro P
  cases P with
  | zero => exact ⟨0, _root_.GlobalTheory.latticePoint_of_mem L (zero_mem _)⟩
  | some x y h =>
    have he := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simp only [_root_.GlobalTheory.latticeCurve] at he
    obtain ⟨z, hz, hx, hy⟩ :=
      _root_.GlobalTheory.exists_weierstrassP_eq_and_derivWeierstrassP_eq L (x := x) (y := 2 * y)
        (by linear_combination 4 * he)
    refine ⟨z, ?_⟩
    rw [_root_.GlobalTheory.latticePoint_of_notMem L hz]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx, by rw [hy]; ring⟩

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Distinguish the cases in `hz : z ∈ L.lattice`. Establish `hw : w ∈ L.lattice` using `by simpa using sub_mem hz h`. Rewrite using `[_root_.GlobalTheory.latticePoint_of_mem L hz, _root_.GlobalTheory.latticePoint_of_mem L hw]`. Establish `hw : w ∉ L.lattice` using `fun hw => hz (by simpa using add_mem h hw)`. Rewrite using `[_root_.GlobalTheory.latticePoint_of_notMem L hz, _root_.GlobalTheory.latticePoint_of_notMem L hw]`.

Establish `e1 : ℘[L] z = ℘[L] w` using `by simpa using weierstrassP_add_coe L w ⟨z - w, h⟩`. Establish `e2 : ℘'[L] z = ℘'[L] w` using `by simpa using derivWeierstrassP_add_coe L w ⟨z - w, h⟩`. Simplify using `only [WeierstrassCurve.Affine.Point.some.injEq]`. Conclude with `⟨e1, by rw [e2]⟩`.
-/
private theorem latticePoint_eq_of_sub_mem_lattice {z w : ℂ} (h : z - w ∈ L.lattice) :
    _root_.GlobalTheory.latticePoint L z = _root_.GlobalTheory.latticePoint L w := by
  by_cases hz : z ∈ L.lattice
  · have hw : w ∈ L.lattice := by simpa using sub_mem hz h
    rw [_root_.GlobalTheory.latticePoint_of_mem L hz, _root_.GlobalTheory.latticePoint_of_mem L hw]
  · have hw : w ∉ L.lattice := fun hw => hz (by simpa using add_mem h hw)
    rw [_root_.GlobalTheory.latticePoint_of_notMem L hz, _root_.GlobalTheory.latticePoint_of_notMem L hw]
    have e1 : ℘[L] z = ℘[L] w := by simpa using weierstrassP_add_coe L w ⟨z - w, h⟩
    have e2 : ℘'[L] z = ℘'[L] w := by simpa using derivWeierstrassP_add_coe L w ⟨z - w, h⟩
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨e1, by rw [e2]⟩

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Establish `hsub : ℘[L] z - ℘[L] w ≠ 0` using `sub_ne_zero.mpr hne`. Establish `hsub' : ℘[L] w - ℘[L] z ≠ 0` using `sub_ne_zero.mpr hne.symm`. Distinguish the cases in `hw' : ℘'[L] w ≠ 0`. Conclude with `_root_.GlobalTheory.weierstrassP_add_of_ne_of_deriv_ne_zero L hz hw hne hw'`. Distinguish the cases in `hz' : ℘'[L] z ≠ 0`.

Take `⟨h1, h2⟩` from `_root_.GlobalTheory.weierstrassP_add_of_ne_of_deriv_ne_zero L hw hz hne.symm hz'`. Rewrite `h1`, `h2` using `[add_comm w z]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `push_neg at hw' hz'`.

Establish `h2w : w + w ∈ L.lattice` using `(_root_.GlobalTheory.derivWeierstrassP_eq_zero_iff L hw).mp hw'`. Establish `h2z : z + z ∈ L.lattice` using `(_root_.GlobalTheory.derivWeierstrassP_eq_zero_iff L hz).mp hz'`. Establish `hzw : z + w ∉ L.lattice` using `fun h => hne ((_root_.GlobalTheory.weierstrassP_eq_iff L hz hw).mpr (Or.inr h))`. Establish `hd : ℘'[L] (z + w) = 0`. Use `(_root_.GlobalTheory.derivWeierstrassP_eq_zero_iff L hzw).mpr ?_` and prove the remaining obligations.

Establish `e : z + w + (z + w) = (z + z) + (w + w)` using `by ring`. Rewrite using `[e]`. Conclude with `add_mem h2z h2w`. Establish `hne2 : ℘[L] (z + w) ≠ ℘[L] w`. Rewrite using `[Ne, _root_.GlobalTheory.weierstrassP_eq_iff L hzw hw, not_or]`.

Prove the components needed by the constructor for the conclusion. Simplify using `using hz`. Introduce `h`. Apply `hz` to reduce the goal to its premises. Establish `e : z = z + w + w - (w + w)` using `by ring`.

Rewrite using `[e]`. Conclude with `sub_mem h h2w`. Establish `ez` using `derivWeierstrassP_sq L z hz`. Establish `ew` using `derivWeierstrassP_sq L w hw`. Establish `es` using `derivWeierstrassP_sq L (z + w) hzw`.

Rewrite `ez` using `[hz']`. Rewrite `ew` using `[hw']`. Rewrite `es` using `[hd]`. Establish `k1 : 4 * (℘[L] z ^ 2 + ℘[L] z * ℘[L] w + ℘[L] w ^ 2) = L.g₂`. Establish `e : (℘[L] z - ℘[L] w) * (4 * (℘[L] z ^ 2 + ℘[L] z * ℘[L] w + ℘[L] w ^ 2) - L.g₂) = 0`.

Take the linear combination `ew - ez`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hsub)`. Establish `k2 : 4 * (℘[L] (z + w) ^ 2 + ℘[L] (z + w) * ℘[L] w + ℘[L] w ^ 2) = L.g₂`. Establish `e : (℘[L] (z + w) - ℘[L] w) * (4 * (℘[L] (z + w) ^ 2 + ℘[L] (z + w) * ℘[L] w + ℘[L] w ^ 2) - L.g₂) = 0`. Take the linear combination `ew - es`.

Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hne2))`. Establish `key : ℘[L] (z + w) = -℘[L] z - ℘[L] w`. Establish `hza : ℘[L] z - ℘[L] (z + w) ≠ 0`. Introduce `h`. Apply `hzw` to reduce the goal to its premises.

Establish `h'` using `(_root_.GlobalTheory.weierstrassP_eq_iff L hz hzw).mp (sub_eq_zero.mp h)`. Break down `h' with h' | h'` into its components or cases. Conclude with `(hw (by simpa using neg_mem h')).elim`. It suffices to derive a contradiction. Apply `hw` to reduce the goal to its premises.

Establish `e2 : w = z + (z + w) - (z + z)` using `by ring`. Rewrite using `[e2]`. Conclude with `sub_mem h' h2z`. Establish `e : (℘[L] z - ℘[L] (z + w)) * (4 * (℘[L] z + ℘[L] w + ℘[L] (z + w))) = 0`. Take the linear combination `k1 - k2`.

Use `(mul_eq_zero.mp e).resolve_left hza` as an intermediate fact. Take the linear combination `this / 4`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hz', hw', key]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hd, hz', hw']`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem weierstrassP_add_and_deriv_add_of_ne {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) = ((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)) ^ 2 / 4 - ℘[L] z - ℘[L] w ∧
    ℘'[L] (z + w) = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) +
      ℘'[L] z) := by
  have hsub : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hne
  have hsub' : ℘[L] w - ℘[L] z ≠ 0 := sub_ne_zero.mpr hne.symm
  by_cases hw' : ℘'[L] w ≠ 0
  · exact _root_.GlobalTheory.weierstrassP_add_of_ne_of_deriv_ne_zero L hz hw hne hw'
  by_cases hz' : ℘'[L] z ≠ 0
  · obtain ⟨h1, h2⟩ := _root_.GlobalTheory.weierstrassP_add_of_ne_of_deriv_ne_zero L hw hz hne.symm hz'
    rw [add_comm w z] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [h1]
      field_simp
      ring
    · rw [h2]
      field_simp
      ring
  push_neg at hw' hz'
  have h2w : w + w ∈ L.lattice := (_root_.GlobalTheory.derivWeierstrassP_eq_zero_iff L hw).mp hw'
  have h2z : z + z ∈ L.lattice := (_root_.GlobalTheory.derivWeierstrassP_eq_zero_iff L hz).mp hz'
  have hzw : z + w ∉ L.lattice := fun h => hne ((_root_.GlobalTheory.weierstrassP_eq_iff L hz hw).mpr (Or.inr h))
  have hd : ℘'[L] (z + w) = 0 := by
    refine (_root_.GlobalTheory.derivWeierstrassP_eq_zero_iff L hzw).mpr ?_
    have e : z + w + (z + w) = (z + z) + (w + w) := by ring
    rw [e]
    exact add_mem h2z h2w
  have hne2 : ℘[L] (z + w) ≠ ℘[L] w := by
    rw [Ne, _root_.GlobalTheory.weierstrassP_eq_iff L hzw hw, not_or]
    constructor
    · simpa using hz
    · intro h
      apply hz
      have e : z = z + w + w - (w + w) := by ring
      rw [e]
      exact sub_mem h h2w
  have ez := derivWeierstrassP_sq L z hz
  have ew := derivWeierstrassP_sq L w hw
  have es := derivWeierstrassP_sq L (z + w) hzw
  rw [hz'] at ez
  rw [hw'] at ew
  rw [hd] at es
  have k1 : 4 * (℘[L] z ^ 2 + ℘[L] z * ℘[L] w + ℘[L] w ^ 2) = L.g₂ := by
    have e : (℘[L] z - ℘[L] w) * (4 * (℘[L] z ^ 2 + ℘[L] z * ℘[L] w + ℘[L] w ^ 2) - L.g₂) = 0 := by
      linear_combination ew - ez
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hsub)
  have k2 : 4 * (℘[L] (z + w) ^ 2 + ℘[L] (z + w) * ℘[L] w + ℘[L] w ^ 2) = L.g₂ := by
    have e : (℘[L] (z + w) - ℘[L] w) *
        (4 * (℘[L] (z + w) ^ 2 + ℘[L] (z + w) * ℘[L] w + ℘[L] w ^ 2) - L.g₂) = 0 := by
      linear_combination ew - es
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hne2))
  have key : ℘[L] (z + w) = -℘[L] z - ℘[L] w := by
    have hza : ℘[L] z - ℘[L] (z + w) ≠ 0 := by
      intro h
      apply hzw
      have h' := (_root_.GlobalTheory.weierstrassP_eq_iff L hz hzw).mp (sub_eq_zero.mp h)
      rcases h' with h' | h'
      · exact (hw (by simpa using neg_mem h')).elim
      · exfalso
        apply hw
        have e2 : w = z + (z + w) - (z + z) := by ring
        rw [e2]
        exact sub_mem h' h2z
    have e : (℘[L] z - ℘[L] (z + w)) * (4 * (℘[L] z + ℘[L] w + ℘[L] (z + w))) = 0 := by
      linear_combination k1 - k2
    have := (mul_eq_zero.mp e).resolve_left hza
    linear_combination this / 4
  refine ⟨?_, ?_⟩
  · rw [hz', hw', key]
    ring
  · rw [hd, hz', hw']
    ring

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Establish `hne : ℘[L] z ≠ ℘[L] w` using `fun h => ((_root_.GlobalTheory.weierstrassP_eq_iff L hz hw).mp h).elim hsub hadd`. Establish `hd : ℘[L] z - ℘[L] w ≠ 0` using `sub_ne_zero.mpr hne`. Take `⟨h1, h2⟩` from `weierstrassP_add_and_deriv_add_of_ne L hz hw hne`. Rewrite using `[_root_.GlobalTheory.latticePoint_of_notMem L hz, _root_.GlobalTheory.latticePoint_of_notMem L hw, _root_.GlobalTheory.latticePoint_of_notMem L hadd]`. Rewrite using `[WeierstrassCurve.Affine.Point.add_some (fun h => hne h.1)]`.

Simplify using `only [WeierstrassCurve.Affine.Point.some.injEq]`. Rewrite using `[WeierstrassCurve.Affine.slope_of_X_ne hne]`. Simplify using `only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, _root_.GlobalTheory.latticeCurve]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[h1]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, h1]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem latticePoint_add_of_not_mem {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (hsub : z - w ∉ L.lattice) (hadd : z + w ∉ L.lattice) :
    _root_.GlobalTheory.latticePoint L (z + w) =
      _root_.GlobalTheory.latticePoint L z + _root_.GlobalTheory.latticePoint L w := by
  classical
  have hne : ℘[L] z ≠ ℘[L] w := fun h => ((_root_.GlobalTheory.weierstrassP_eq_iff L hz hw).mp h).elim hsub hadd
  have hd : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨h1, h2⟩ := weierstrassP_add_and_deriv_add_of_ne L hz hw hne
  rw [_root_.GlobalTheory.latticePoint_of_notMem L hz, _root_.GlobalTheory.latticePoint_of_notMem L hw,
    _root_.GlobalTheory.latticePoint_of_notMem L hadd]
  rw [WeierstrassCurve.Affine.Point.add_some (fun h => hne h.1)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, _root_.GlobalTheory.latticeCurve]
  constructor
  · rw [h1]
    field_simp
    ring
  · rw [h2, h1]
    field_simp
    ring

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in

/- English proof (translation)
Distinguish the cases in `hz : z ∈ L.lattice`. Rewrite using `[_root_.GlobalTheory.latticePoint_of_mem L hz, zero_add]`. Conclude with `latticePoint_eq_of_sub_mem_lattice L (by simpa using hz)`. Distinguish the cases in `hw : w ∈ L.lattice`. Rewrite using `[_root_.GlobalTheory.latticePoint_of_mem L hw, add_zero]`.

Conclude with `latticePoint_eq_of_sub_mem_lattice L (by simpa using hw)`. Distinguish the cases in `hs : z + w ∈ L.lattice`. Rewrite using `[_root_.GlobalTheory.latticePoint_of_mem L hs, latticePoint_eq_of_sub_mem_lattice L (z := w) (w := -z) (by rw [sub_neg_eq_add, add_comm]; exact hs), _root_.GlobalTheory.latticePoint_neg, add_neg_cancel]`. Distinguish the cases in `hd : z - w ∈ L.lattice`. Rewrite using `[latticePoint_eq_of_sub_mem_lattice L (z := w) (w := z) (by rw [← neg_sub]; exact neg_mem hd), latticePoint_eq_of_sub_mem_lattice L (z := z + w) (w := z + z) (by rw [show z + w - (z + z) = -(z - w) by ring]; exact neg_mem hd)]`.

Establish `hc : ({u : ℂ | u ∈ L.lattice} ∪ {u | u + u ∈ L.lattice} ∪ {u | u + z ∈ L.lattice} ∪ {u | u + -z ∈ L.lattice}).Countable`. Use `(((_root_.GlobalTheory.countable_periodLattice L).union ?_).union (_root_.GlobalTheory.countable_add_mem_periodLattice L z)).union (_root_.GlobalTheory.countable_add_mem_periodLattice L (-z))` and prove the remaining obligations. Use `((_root_.GlobalTheory.countable_periodLattice L).image (fun x => x / 2)).mono ?_` and prove the remaining obligations. Introduce `u hu`. Conclude with `⟨u + u, hu, by ring⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, u ∉ ({u : ℂ | u ∈ L.lattice} ∪ {u | u + u ∈ L.lattice} ∪ {u | u + z ∈ L.lattice} ∪ {u | u + -z ∈ L.lattice}) := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `not_countable_complex (hc.mono fun u _ => h u)`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or] at hu`.

Take `⟨⟨⟨hu1, hu2⟩, hu3⟩, hu4⟩` from `hu`. Establish `hzu : z + u ∉ L.lattice` using `by rw [add_comm]; exact hu3`. Establish `hzmu : z + -u ∉ L.lattice` using `fun h => hu4 (by`. Use `neg_mem h` as an intermediate fact. Rewrite using `[show -(z + -u) = u + -z by ring] at this)` and apply the resulting hypothesis.

Establish `hnu : -u ∉ L.lattice` using `fun h => hu1 (by simpa using neg_mem h)`. Establish `hzz : z + z ∉ L.lattice` using `fun h => hs (by`. Use `sub_mem h hd` as an intermediate fact. Rewrite using `[show z + z - (z - w) = z + w by ring] at this)` and apply the resulting hypothesis. Establish `e : z + z = (z + u) + (z + -u)` using `by ring`.

Rewrite using `[e, latticePoint_add_of_not_mem L hzu hzmu (by rw [show z + u - (z + -u) = u + u by ring]; exact hu2) (by rw [← e]; exact hzz), latticePoint_add_of_not_mem L hz hu1 (by rw [sub_eq_add_neg]; exact hzmu) hzu, latticePoint_add_of_not_mem L hz hnu (by rw [sub_neg_eq_add]; exact hzu) …`. Normalize the expressions using the abelian group laws. Conclude with `latticePoint_add_of_not_mem L hz hw hd hs`.
-/
theorem _root_.GlobalTheory.latticePoint_add (z w : ℂ) :
    _root_.GlobalTheory.latticePoint L (z + w) =
      _root_.GlobalTheory.latticePoint L z + _root_.GlobalTheory.latticePoint L w := by
  by_cases hz : z ∈ L.lattice
  · rw [_root_.GlobalTheory.latticePoint_of_mem L hz, zero_add]
    exact latticePoint_eq_of_sub_mem_lattice L (by simpa using hz)
  by_cases hw : w ∈ L.lattice
  · rw [_root_.GlobalTheory.latticePoint_of_mem L hw, add_zero]
    exact latticePoint_eq_of_sub_mem_lattice L (by simpa using hw)
  by_cases hs : z + w ∈ L.lattice
  · rw [_root_.GlobalTheory.latticePoint_of_mem L hs,
      latticePoint_eq_of_sub_mem_lattice L (z := w) (w := -z)
        (by rw [sub_neg_eq_add, add_comm]; exact hs),
      _root_.GlobalTheory.latticePoint_neg, add_neg_cancel]
  by_cases hd : z - w ∈ L.lattice
  · rw [latticePoint_eq_of_sub_mem_lattice L (z := w) (w := z)
        (by rw [← neg_sub]; exact neg_mem hd),
      latticePoint_eq_of_sub_mem_lattice L (z := z + w) (w := z + z)
        (by rw [show z + w - (z + z) = -(z - w) by ring]; exact neg_mem hd)]
    have hc : ({u : ℂ | u ∈ L.lattice} ∪ {u | u + u ∈ L.lattice} ∪ {u | u + z ∈ L.lattice} ∪
        {u | u + -z ∈ L.lattice}).Countable := by
      refine (((_root_.GlobalTheory.countable_periodLattice L).union ?_).union
        (_root_.GlobalTheory.countable_add_mem_periodLattice L z)).union (_root_.GlobalTheory.countable_add_mem_periodLattice L (-z))
      refine ((_root_.GlobalTheory.countable_periodLattice L).image (fun x => x / 2)).mono ?_
      intro u hu
      exact ⟨u + u, hu, by ring⟩
    obtain ⟨u, hu⟩ : ∃ u, u ∉ ({u : ℂ | u ∈ L.lattice} ∪ {u | u + u ∈ L.lattice} ∪
        {u | u + z ∈ L.lattice} ∪ {u | u + -z ∈ L.lattice}) := by
      by_contra h
      push_neg at h
      exact not_countable_complex (hc.mono fun u _ => h u)
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hu
    obtain ⟨⟨⟨hu1, hu2⟩, hu3⟩, hu4⟩ := hu
    have hzu : z + u ∉ L.lattice := by rw [add_comm]; exact hu3
    have hzmu : z + -u ∉ L.lattice := fun h => hu4 (by
      have := neg_mem h
      rwa [show -(z + -u) = u + -z by ring] at this)
    have hnu : -u ∉ L.lattice := fun h => hu1 (by simpa using neg_mem h)
    have hzz : z + z ∉ L.lattice := fun h => hs (by
      have := sub_mem h hd
      rwa [show z + z - (z - w) = z + w by ring] at this)
    have e : z + z = (z + u) + (z + -u) := by ring
    rw [e, latticePoint_add_of_not_mem L hzu hzmu
        (by rw [show z + u - (z + -u) = u + u by ring]; exact hu2)
        (by rw [← e]; exact hzz),
      latticePoint_add_of_not_mem L hz hu1 (by rw [sub_eq_add_neg]; exact hzmu) hzu,
      latticePoint_add_of_not_mem L hz hnu (by rw [sub_neg_eq_add]; exact hzu) hzmu,
      _root_.GlobalTheory.latticePoint_neg]
    abel
  · exact latticePoint_add_of_not_mem L hz hw hd hs

def latticePointHom : ℂ →+ (latticeCurve L).toAffine.Point :=
  AddMonoidHom.mk' (latticePoint L) (latticePoint_add L)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma latticePointHom_apply (z : ℂ) : latticePointHom L z = latticePoint L z := rfl

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Use extensionality with `z`. Rewrite using `[AddMonoidHom.mem_ker, _root_.GlobalTheory.latticePointHom_apply, _root_.GlobalTheory.latticePoint_eq_zero_iff, Submodule.mem_toAddSubgroup]`.
-/
theorem _root_.GlobalTheory.ker_latticePointHom :
    (_root_.GlobalTheory.latticePointHom L).ker = L.lattice.toAddSubgroup := by
  ext z
  rw [AddMonoidHom.mem_ker, _root_.GlobalTheory.latticePointHom_apply,
    _root_.GlobalTheory.latticePoint_eq_zero_iff, Submodule.mem_toAddSubgroup]

def latticePointEquiv : (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (latticeCurve L).toAffine.Point :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_latticePointHom L).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (latticePoint_surjective L))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma latticePointEquiv_mk (z : ℂ) :
    latticePointEquiv L (z : ℂ ⧸ L.lattice.toAddSubgroup) = latticePoint L z := rfl

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
/- English proof (translation)
Rewrite using `[← _root_.GlobalTheory.latticePoint_eq_zero_iff, sub_eq_add_neg, _root_.GlobalTheory.latticePoint_add, _root_.GlobalTheory.latticePoint_neg, ← sub_eq_add_neg, sub_eq_zero]`.
-/
theorem _root_.GlobalTheory.latticePoint_eq_iff {z w : ℂ} :
    _root_.GlobalTheory.latticePoint L z = _root_.GlobalTheory.latticePoint L w ↔ z - w ∈ L.lattice := by
  rw [← _root_.GlobalTheory.latticePoint_eq_zero_iff, sub_eq_add_neg, _root_.GlobalTheory.latticePoint_add,
    _root_.GlobalTheory.latticePoint_neg, ← sub_eq_add_neg, sub_eq_zero]

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in

/- English proof (translation)
The claim follows from `weierstrassP_add_and_deriv_add_of_ne L hz hw hne`.
-/
theorem _root_.GlobalTheory.weierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) = ((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)) ^ 2 / 4 - ℘[L] z - ℘[L] w ∧
    ℘'[L] (z + w) = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) +
      ℘'[L] z) :=
  weierstrassP_add_and_deriv_add_of_ne L hz hw hne

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in

/- English proof (translation)
Establish `hmw : -w ∉ L.lattice` using `fun h => hw (by simpa using neg_mem h)`. Establish `hne' : ℘[L] z ≠ ℘[L] (-w)` using `by rwa [weierstrassP_neg]`. Take `⟨h1, -⟩` from `weierstrassP_add_and_deriv_add_of_ne L hz hw hne`. Take `⟨h2, -⟩` from `weierstrassP_add_and_deriv_add_of_ne L hz hmw hne'`. Rewrite `h2` using `[weierstrassP_neg, derivWeierstrassP_neg, ← sub_eq_add_neg]`.

Establish `ez` using `derivWeierstrassP_sq L z hz`. Establish `ew` using `derivWeierstrassP_sq L w hw`. Establish `hsub : ℘[L] z - ℘[L] w ≠ 0` using `sub_ne_zero.mpr hne`. Establish `hy : ℘'[L] z ^ 2 = ℘'[L] w ^ 2 + (℘[L] z - ℘[L] w) * (4 * (℘[L] z ^ 2 + ℘[L] z * ℘[L] w + ℘[L] w ^ 2) - L.g₂)`. Take the linear combination `ez - ew`.

Rewrite using `[h1, h2]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `4 * hy`.
-/
theorem _root_.GlobalTheory.weierstrassP_add_add_sub {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) + ℘[L] (z - w) - 2 * ℘[L] w =
      (6 * ℘[L] w ^ 2 - L.g₂ / 2) / (℘[L] z - ℘[L] w) + ℘'[L] w ^ 2 / (℘[L] z - ℘[L] w) ^ 2 := by
  have hmw : -w ∉ L.lattice := fun h => hw (by simpa using neg_mem h)
  have hne' : ℘[L] z ≠ ℘[L] (-w) := by rwa [weierstrassP_neg]
  obtain ⟨h1, -⟩ := weierstrassP_add_and_deriv_add_of_ne L hz hw hne
  obtain ⟨h2, -⟩ := weierstrassP_add_and_deriv_add_of_ne L hz hmw hne'
  rw [weierstrassP_neg, derivWeierstrassP_neg, ← sub_eq_add_neg] at h2
  have ez := derivWeierstrassP_sq L z hz
  have ew := derivWeierstrassP_sq L w hw
  have hsub : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hne
  have hy : ℘'[L] z ^ 2 = ℘'[L] w ^ 2 + (℘[L] z - ℘[L] w) *
      (4 * (℘[L] z ^ 2 + ℘[L] z * ℘[L] w + ℘[L] w ^ 2) - L.g₂) := by
    linear_combination ez - ew
  rw [h1, h2]
  field_simp
  linear_combination 4 * hy

open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in

/- English proof (translation)
Introduce `h6`. Establish `ew` using `derivWeierstrassP_sq L w hw`. Rewrite `ew` using `[h]`. Establish `hΔ` using `_root_.GlobalTheory.latticeCurve_Δ_ne_zero L`. Rewrite `hΔ` using `[_root_.GlobalTheory.latticeCurve_Δ]`.

Apply `hΔ` to reduce the goal to its premises. Establish `hg2 : L.g₂ = 12 * ℘[L] w ^ 2` using `by linear_combination -2 * h6`. Establish `hg3 : L.g₃ = -8 * ℘[L] w ^ 3` using `by linear_combination ew + 2 * ℘[L] w * h6`. Rewrite using `[hg2, hg3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.weierstrassP_second_ne_zero {w : ℂ} (hw : w ∉ L.lattice)
    (h : ℘'[L] w = 0) : 6 * ℘[L] w ^ 2 - L.g₂ / 2 ≠ 0 := by
  intro h6
  have ew := derivWeierstrassP_sq L w hw
  rw [h] at ew
  have hΔ := _root_.GlobalTheory.latticeCurve_Δ_ne_zero L
  rw [_root_.GlobalTheory.latticeCurve_Δ] at hΔ
  apply hΔ
  have hg2 : L.g₂ = 12 * ℘[L] w ^ 2 := by linear_combination -2 * h6
  have hg3 : L.g₃ = -8 * ℘[L] w ^ 3 := by linear_combination ew + 2 * ℘[L] w * h6
  rw [hg2, hg3]
  ring

end GlobalTheory
