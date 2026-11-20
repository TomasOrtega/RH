import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticRational
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticDegree
import GroundTheory.GlobalFields.ComplexMultiplication.Uniformization
import GroundTheory.GlobalFields.ComplexMultiplication.UniformizationAddition

open Complex Filter Topology Set
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

open WeierstrassCurve.Affine

variable {L : PeriodPair}

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `h2` using `finsum_toNat_torusOrder_weierstrassP_sub (L := L) c`. Establish `h0 : ∀ x : Torus L, (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat = 0`. Introduce `x`.

Take `⟨z, rfl⟩` from `Torus.mk_surjective L x`. Rewrite using `[torusOrder_mk (isEllipticFunction_weierstrassP_sub c)]`. Distinguish the cases in `hz : z ∈ L.lattice`. Establish `hc : MeromorphicAt (fun _ : ℂ ↦ -c) z` using `analyticAt_const.meromorphicAt`. Establish `e : (fun w ↦ ℘[L] w - c) = ℘[L] + fun _ ↦ -c`.

Use function extensionality and compare the values at `w`. Simplify using `[sub_eq_add_neg]`. Establish `hlt : meromorphicOrderAt ℘[L] z < meromorphicOrderAt (fun _ : ℂ ↦ -c) z`. Rewrite using `[L.order_weierstrassP z hz]`. Conclude with `lt_of_lt_of_le (by decide) analyticAt_const.meromorphicOrderAt_nonneg`.

Rewrite using `[e, meromorphicOrderAt_add_eq_left_of_lt hc hlt, L.order_weierstrassP z hz]`. Both sides reduce to the same expression. Establish `ha : AnalyticAt ℂ (fun w ↦ ℘[L] w - c) z` using `(L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const`. Establish `h0 : analyticOrderAt (fun w ↦ ℘[L] w - c) z = 0` using `ha.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 (hcon z hz))`. Rewrite using `[ha.meromorphicOrderAt_eq, h0]`.

Both sides reduce to the same expression. Simplify using `[h0] at h2`.
-/
theorem exists_weierstrassP_eq (c : ℂ) : ∃ z, z ∉ L.lattice ∧ ℘[L] z = c := by
  by_contra hcon
  push_neg at hcon
  have h2 := finsum_toNat_torusOrder_weierstrassP_sub (L := L) c
  have h0 : ∀ x : Torus L, (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
    rw [torusOrder_mk (isEllipticFunction_weierstrassP_sub c)]
    by_cases hz : z ∈ L.lattice
    · have hc : MeromorphicAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicAt
      have e : (fun w ↦ ℘[L] w - c) = ℘[L] + fun _ ↦ -c := by
        funext w
        simp [sub_eq_add_neg]
      have hlt : meromorphicOrderAt ℘[L] z < meromorphicOrderAt (fun _ : ℂ ↦ -c) z := by
        rw [L.order_weierstrassP z hz]
        exact lt_of_lt_of_le (by decide) analyticAt_const.meromorphicOrderAt_nonneg
      rw [e, meromorphicOrderAt_add_eq_left_of_lt hc hlt, L.order_weierstrassP z hz]
      rfl
    · have ha : AnalyticAt ℂ (fun w ↦ ℘[L] w - c) z :=
        (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
      have h0 : analyticOrderAt (fun w ↦ ℘[L] w - c) z = 0 :=
        ha.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 (hcon z hz))
      rw [ha.meromorphicOrderAt_eq, h0]
      rfl
  simp [h0] at h2

variable (L) in

def toPoint (z : ℂ) : (weierstrassCurve L).toAffine.Point :=
  haveI := Classical.propDecidable (z ∈ L.lattice)
  if h : z ∈ L.lattice then 0 else
    .some (℘[L] z) (℘'[L] z / 2) (equation_iff_nonsingular.1 (equation_weierstrassP L h))

/- English proof (translation)
Rewrite using `[toPoint, dif_pos h]`.
-/
lemma toPoint_of_mem {z : ℂ} (h : z ∈ L.lattice) : toPoint L z = 0 := by
  rw [toPoint, dif_pos h]

/- English proof (translation)
Rewrite using `[toPoint, dif_neg h]`.
-/
lemma toPoint_of_notMem {z : ℂ} (h : z ∉ L.lattice) :
    toPoint L z = .some (℘[L] z) (℘'[L] z / 2)
      (equation_iff_nonsingular.1 (equation_weierstrassP L h)) := by
  rw [toPoint, dif_neg h]

/- English proof (translation)
Substitute `hx hy` using the available equality. Both sides reduce to the same expression. Use the proof step `@[simp]`.
-/
lemma point_some_congr {x y x' y' : ℂ} {h : (weierstrassCurve L).toAffine.Nonsingular x y}
    {h' : (weierstrassCurve L).toAffine.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx hy
  rfl

@[simp]
/- English proof (translation)
The claim follows from `toPoint_of_mem L.lattice.zero_mem`.
-/
lemma toPoint_zero : toPoint L 0 = 0 := toPoint_of_mem L.lattice.zero_mem

/- English proof (translation)
Distinguish the cases in `hz : z ∈ L.lattice`. Rewrite using `[toPoint_of_mem hz, toPoint_of_mem (add_mem hz hl)]`. Establish `hzl : z + l ∉ L.lattice` using `fun h ↦ hz (by simpa using sub_mem h hl)`. Rewrite using `[toPoint_of_notMem hz, toPoint_of_notMem hzl]`. Conclude with `point_some_congr (isPeriodic_weierstrassP z l hl) (by rw [isPeriodic_derivWeierstrassP z l hl])`.
-/
lemma toPoint_add_mem {z l : ℂ} (hl : l ∈ L.lattice) : toPoint L (z + l) = toPoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, toPoint_of_mem (add_mem hz hl)]
  · have hzl : z + l ∉ L.lattice := fun h ↦ hz (by simpa using sub_mem h hl)
    rw [toPoint_of_notMem hz, toPoint_of_notMem hzl]
    exact point_some_congr (isPeriodic_weierstrassP z l hl)
      (by rw [isPeriodic_derivWeierstrassP z l hl])

/- English proof (translation)
Simplify using `using toPoint_add_mem (z := w) h`.
-/
lemma toPoint_eq_of_sub_mem {z w : ℂ} (h : z - w ∈ L.lattice) : toPoint L z = toPoint L w := by
  simpa using toPoint_add_mem (z := w) h

/- English proof (translation)
Distinguish the cases in `hz : z ∈ L.lattice`. Rewrite using `[toPoint_of_mem hz, toPoint_of_mem (neg_mem hz), neg_zero]`. Establish `hz' : -z ∉ L.lattice` using `fun h ↦ hz (by simpa using neg_mem h)`. Rewrite using `[toPoint_of_notMem hz, toPoint_of_notMem hz', Point.neg_some]`. Use `point_some_congr (L.weierstrassP_neg z) ?_` and prove the remaining obligations.

Simplify using `[negY, L.derivWeierstrassP_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem toPoint_neg (z : ℂ) : toPoint L (-z) = -toPoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, toPoint_of_mem (neg_mem hz), neg_zero]
  · have hz' : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
    rw [toPoint_of_notMem hz, toPoint_of_notMem hz', Point.neg_some]
    refine point_some_congr (L.weierstrassP_neg z) ?_
    simp [negY, L.derivWeierstrassP_neg]
    ring

/- English proof (translation)
Use `⟨fun h ↦ ?_, toPoint_of_mem⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hz`. Rewrite `h` using `[toPoint_of_notMem hz]`. Conclude with `Point.some_ne_zero _ h`.
-/
theorem toPoint_eq_zero_iff {z : ℂ} : toPoint L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h ↦ ?_, toPoint_of_mem⟩
  by_contra hz
  rw [toPoint_of_notMem hz] at h
  exact Point.some_ne_zero _ h

/- English proof (translation)
Distinguish the cases in `hz : z ∈ L.lattice`. Rewrite using `[toPoint_of_mem hz, zero_add, add_comm, toPoint_add_mem hz]`. Distinguish the cases in `hw : w ∈ L.lattice`. Rewrite using `[toPoint_of_mem hw, add_zero, toPoint_add_mem hw]`. Distinguish the cases in `hzw' : z + w ∈ L.lattice`.

Establish `: toPoint L w = toPoint L (-z)` using `toPoint_eq_of_sub_mem (by rwa [sub_neg_eq_add, add_comm])`. Rewrite using `[toPoint_of_mem hzw', this, toPoint_neg, add_neg_cancel]`. Distinguish the cases in `hzw : z - w ∈ L.lattice`. Establish `hwz : toPoint L w = toPoint L z` using `toPoint_eq_of_sub_mem (by simpa using neg_mem hzw)`. Establish `h2 : toPoint L (z + w) = toPoint L (2 * z)` using `toPoint_eq_of_sub_mem (by rw [show z + w - 2 * z = -(z - w) by ring]; exact neg_mem hzw)`.

Establish `h2z : 2 * z ∉ L.lattice` using `fun h ↦ hzw' (by`. Rewrite using `[show z + w = 2 * z - (z - w) by ring]; exact sub_mem h hzw)`. Establish `hd : ℘'[L] z ≠ 0` using `fun h ↦ h2z ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hz).2 h)`. Establish `hy : ℘'[L] z / 2 ≠ (weierstrassCurve L).toAffine.negY (℘[L] z) (℘'[L] z / 2)`. Simplify using `only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃, zero_mul, sub_zero]`.

Introduce `h`. Apply `hd` to reduce the goal to its premises. Take the linear combination `h`. Rewrite using `[h2, hwz, toPoint_of_notMem hz, toPoint_of_notMem h2z, Point.add_self_of_Y_ne hy]`. Establish `hsl : (weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] z) (℘'[L] z / 2) (℘'[L] z / 2) = tangentSlope L z / 2`.

Establish `hden : ℘'[L] z / 2 - (weierstrassCurve L).toAffine.negY (℘[L] z) (℘'[L] z / 2) = ℘'[L] z`. Simplify using `only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[slope_of_Y_ne rfl hy, hden]`. Simplify using `only [tangentSlope, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₄]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hx : ℘[L] (2 * z) = (weierstrassCurve L).toAffine.addX (℘[L] z) (℘[L] z) ((weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] z) (℘'[L] z / 2) (℘'[L] z / 2))`. Rewrite using `[hsl, weierstrassP_two_mul hz h2z]`. Simplify using `only [addX, weierstrassCurve_a₁, weierstrassCurve_a₂]`.

Expand and normalize the polynomial expressions, which then agree. Use `point_some_congr hx ?_` and prove the remaining obligations. Rewrite using `[addY, negAddY, ← hx, hsl, derivWeierstrassP_two_mul hz h2z]`. Simplify using `only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hne : ℘[L] z ≠ ℘[L] w` using `fun h ↦ (sub_mem_or_add_mem_of_weierstrassP_eq hz hw h).elim hzw hzw'`. Rewrite using `[toPoint_of_notMem hz, toPoint_of_notMem hw, toPoint_of_notMem hzw', Point.add_of_X_ne hne]`. Establish `hsl : (weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) = chordSlope L z w / 2`. Rewrite using `[slope_of_X_ne hne, chordSlope]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hx : ℘[L] (z + w) = (weierstrassCurve L).toAffine.addX (℘[L] z) (℘[L] w) ((weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2))`. Rewrite using `[hsl, weierstrassP_add hz hw hzw hzw']`. Simplify using `only [addX, weierstrassCurve_a₁, weierstrassCurve_a₂]`. Expand and normalize the polynomial expressions, which then agree. Use `point_some_congr hx ?_` and prove the remaining obligations.

Rewrite using `[addY, negAddY, ← hx, hsl, derivWeierstrassP_add hz hw hzw hzw']`. Simplify using `only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem toPoint_add (z w : ℂ) : toPoint L (z + w) = toPoint L z + toPoint L w := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, zero_add, add_comm, toPoint_add_mem hz]
  by_cases hw : w ∈ L.lattice
  · rw [toPoint_of_mem hw, add_zero, toPoint_add_mem hw]
  by_cases hzw' : z + w ∈ L.lattice
  · have : toPoint L w = toPoint L (-z) := toPoint_eq_of_sub_mem (by rwa [sub_neg_eq_add, add_comm])
    rw [toPoint_of_mem hzw', this, toPoint_neg, add_neg_cancel]
  by_cases hzw : z - w ∈ L.lattice
  ·
    have hwz : toPoint L w = toPoint L z := toPoint_eq_of_sub_mem (by simpa using neg_mem hzw)
    have h2 : toPoint L (z + w) = toPoint L (2 * z) :=
      toPoint_eq_of_sub_mem (by rw [show z + w - 2 * z = -(z - w) by ring]; exact neg_mem hzw)
    have h2z : 2 * z ∉ L.lattice := fun h ↦ hzw' (by
      rw [show z + w = 2 * z - (z - w) by ring]; exact sub_mem h hzw)
    have hd : ℘'[L] z ≠ 0 := fun h ↦ h2z ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hz).2 h)
    have hy : ℘'[L] z / 2 ≠ (weierstrassCurve L).toAffine.negY (℘[L] z) (℘'[L] z / 2) := by
      simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃, zero_mul, sub_zero]
      intro h
      apply hd
      linear_combination h
    rw [h2, hwz, toPoint_of_notMem hz, toPoint_of_notMem h2z, Point.add_self_of_Y_ne hy]
    have hsl : (weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] z) (℘'[L] z / 2) (℘'[L] z / 2) =
        tangentSlope L z / 2 := by
      have hden : ℘'[L] z / 2 - (weierstrassCurve L).toAffine.negY (℘[L] z) (℘'[L] z / 2) =
          ℘'[L] z := by
        simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
        ring
      rw [slope_of_Y_ne rfl hy, hden]
      simp only [tangentSlope, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₄]
      field_simp
      ring
    have hx : ℘[L] (2 * z) = (weierstrassCurve L).toAffine.addX (℘[L] z) (℘[L] z)
        ((weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] z) (℘'[L] z / 2) (℘'[L] z / 2)) := by
      rw [hsl, weierstrassP_two_mul hz h2z]
      simp only [addX, weierstrassCurve_a₁, weierstrassCurve_a₂]
      ring
    refine point_some_congr hx ?_
    rw [addY, negAddY, ← hx, hsl, derivWeierstrassP_two_mul hz h2z]
    simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
    ring
  ·
    have hne : ℘[L] z ≠ ℘[L] w := fun h ↦
      (sub_mem_or_add_mem_of_weierstrassP_eq hz hw h).elim hzw hzw'
    rw [toPoint_of_notMem hz, toPoint_of_notMem hw, toPoint_of_notMem hzw',
      Point.add_of_X_ne hne]
    have hsl : (weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) =
        chordSlope L z w / 2 := by
      rw [slope_of_X_ne hne, chordSlope]
      ring
    have hx : ℘[L] (z + w) = (weierstrassCurve L).toAffine.addX (℘[L] z) (℘[L] w)
        ((weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2)) := by
      rw [hsl, weierstrassP_add hz hw hzw hzw']
      simp only [addX, weierstrassCurve_a₁, weierstrassCurve_a₂]
      ring
    refine point_some_congr hx ?_
    rw [addY, negAddY, ← hx, hsl, derivWeierstrassP_add hz hw hzw hzw']
    simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
    ring

/- English proof (translation)
Introduce and unpack `(_ | ⟨x, y, h⟩)`. Conclude with `⟨0, toPoint_zero⟩`. Take `⟨z, hz, hx⟩` from `exists_weierstrassP_eq (L := L) x`. Establish `hE` using `(weierstrassCurve_equation_iff L x y).1 h.1`. Establish `hP` using `L.derivWeierstrassP_sq z hz`.

Rewrite `hP` using `[hx]`. Establish `hz' : -z ∉ L.lattice` using `fun h ↦ hz (by simpa using neg_mem h)`. Establish `hy : (y - ℘'[L] z / 2) * (y + ℘'[L] z / 2) = 0` using `by linear_combination hE / 4 - hP / 4`. Break down `mul_eq_zero.1 hy with h1 | h1` into its components or cases. Use `⟨z, ?_⟩` and prove the remaining obligations.

Rewrite using `[toPoint_of_notMem hz]`. Conclude with `point_some_congr hx (by linear_combination -h1)`. Use `⟨-z, ?_⟩` and prove the remaining obligations. Rewrite using `[toPoint_of_notMem hz']`. Conclude with `point_some_congr (by rw [L.weierstrassP_neg, hx]) (by rw [L.derivWeierstrassP_neg]; linear_combination -h1)`.
-/
theorem toPoint_surjective : Function.Surjective (toPoint L) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, toPoint_zero⟩
  obtain ⟨z, hz, hx⟩ := exists_weierstrassP_eq (L := L) x
  have hE := (weierstrassCurve_equation_iff L x y).1 h.1
  have hP := L.derivWeierstrassP_sq z hz
  rw [hx] at hP
  have hz' : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
  have hy : (y - ℘'[L] z / 2) * (y + ℘'[L] z / 2) = 0 := by linear_combination hE / 4 - hP / 4
  rcases mul_eq_zero.1 hy with h1 | h1
  · refine ⟨z, ?_⟩
    rw [toPoint_of_notMem hz]
    exact point_some_congr hx (by linear_combination -h1)
  · refine ⟨-z, ?_⟩
    rw [toPoint_of_notMem hz']
    exact point_some_congr (by rw [L.weierstrassP_neg, hx])
      (by rw [L.derivWeierstrassP_neg]; linear_combination -h1)

variable (L) in

def toPointHom : ℂ →+ (weierstrassCurve L).toAffine.Point where
  toFun := toPoint L
  map_zero' := toPoint_zero
  map_add' := toPoint_add

variable (L) in

def torusToPoint : Torus L →+ (weierstrassCurve L).toAffine.Point :=
  QuotientAddGroup.lift L.lattice.toAddSubgroup (toPointHom L) fun _ hl ↦ toPoint_of_mem hl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma torusToPoint_mk (z : ℂ) : torusToPoint L (Torus.mk L z) = toPoint L z := rfl

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `Torus.mk_surjective L x`. Rewrite `hx` using `[torusToPoint_mk, toPoint_eq_zero_iff]`. Conclude with `(QuotientAddGroup.eq_zero_iff z).2 hx`.
-/
lemma torusToPoint_injective : Function.Injective (torusToPoint L) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
  rw [torusToPoint_mk, toPoint_eq_zero_iff] at hx
  exact (QuotientAddGroup.eq_zero_iff z).2 hx

/- English proof (translation)
The claim follows from `fun P ↦ by obtain ⟨z, hz⟩ := toPoint_surjective (L := L) P exact ⟨Torus.mk L z, hz⟩`.
-/
lemma torusToPoint_surjective : Function.Surjective (torusToPoint L) := fun P ↦ by
  obtain ⟨z, hz⟩ := toPoint_surjective (L := L) P
  exact ⟨Torus.mk L z, hz⟩

variable (L) in

def torusEquivPoint : Torus L ≃+ (weierstrassCurve L).toAffine.Point :=
  AddEquiv.ofBijective (torusToPoint L) ⟨torusToPoint_injective, torusToPoint_surjective⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem torusEquivPoint_mk (z : ℂ) : torusEquivPoint L (Torus.mk L z) = toPoint L z := rfl

end Elliptic
end GroundTheory.Global
