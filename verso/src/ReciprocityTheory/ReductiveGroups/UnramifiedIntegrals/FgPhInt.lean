import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgDefs
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

/- English proof (translation)
Establish `hl : C.IsLogPair l linv` using `hF.1`. Establish `hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0` using `PowerSeries.constantCoeff_X`. Establish `hXpt : C.IsPt R (PowerSeries.X : MvPowerSeries Unit K)` using `C.Pts.isPt_X`. Use `set q : K → MvPowerSeries Unit K := fun a => PowerSeries.subst (C.fmul l linv a (PowerSeries.X : MvPowerSeries Unit K)) ph with hq`. Use `set B : MvPowerSeries Unit K := C.be0 l linv ph (PowerSeries.X : MvPowerSeries Unit K) (PowerSeries.X : MvPowerSeries Unit K) with hB`.

Establish `hphX : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) ph = ph` using `PowerSeries.X_subst ph`. Establish `hE : ∀ m : ℤ, C.LG R (q (1 + (m : K)) - ph - q (m : K) - (m : K) • B)`. Introduce `m`. Establish `h` using `C.zLinInt K R l linv ph hF h1 m Unit _ _ hXpt hXpt`. Unfold `C.Cong at h`.

Rewrite `h` using `[C.be0]`. Establish `e : C.fadd l linv (PowerSeries.X : MvPowerSeries Unit K) (C.fmul l linv (m : K) (PowerSeries.X : MvPowerSeries Unit K)) = C.fmul l linv (1 + (m : K)) (PowerSeries.X : MvPowerSeries Unit K)`. Rewrite using `[C.Pts.fmul_add hl 1 (m : K) hX, C.Pts.fmul_one hl hX]`. Rewrite `h` using `[e, hphX]`. Conclude with `h`.

Establish `hq0 : q 0 = 0`. Simplify using `only [hq]`. Rewrite using `[C.Pts.fmul_zero_left hl, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2]`. Establish `hN : C.LG R (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K)))`. Establish `h` using `hneg`.

Unfold `C.PhNormAt C.Cong at h`. Rewrite `h` using `[C.Pts.mulBy_eq_fmul]`. Conclude with `h`. Establish `hG : C.LG R (B - (2 : K) • (ph : MvPowerSeries Unit K))`. Establish `h` using `C.Calc.lg_add (hE (-1)) hN`.

Establish `e : (q (1 + ((-1 : ℤ) : K)) - ph - q ((-1 : ℤ) : K) - ((-1 : ℤ) : K) • B) + (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K))) = B - (2 : K) • (ph : MvPowerSeries Unit K)`. Establish `e0 : (1 : K) + ((-1 : ℤ) : K) = 0` using `by push_cast; ring`. Establish `e1 : (((-1 : ℤ) : K)) = -1` using `by push_cast; ring`. Rewrite using `[e0, hq0, e1]`. Use `module`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `hstep : ∀ m : ℤ, C.LG R ((q (((m + 1 : ℤ)) : K) - ((((m + 1 : ℤ)) : K) * (((m + 1 : ℤ)) : K)) • (ph : MvPowerSeries Unit K)) - (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K)))`. Introduce `m`. Establish `h` using `C.Calc.lg_add (hE m) (C.lGBinom K R Unit (m : K) (C.intBinomScalar K R m) _ hG)`. Establish `e1 : (((m + 1 : ℤ)) : K) = 1 + (m : K)` using `by push_cast; ring`.

Rewrite using `[e1]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `module`. Establish `main : ∀ m : ℤ, C.LG R (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K))`. Introduce `m`.

Proceed by induction on `m using Int.induction_on with`. Consider the case `zero`. Establish `: q ((0 : ℤ) : K) - (((0 : ℤ) : K) * ((0 : ℤ) : K)) • (ph : MvPowerSeries Unit K) = 0`. Rewrite using `[Int.cast_zero, hq0]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `C.Calc.lg_zero`. Consider the case `succ i ih`. Establish `h` using `C.Calc.lg_add (hstep i) ih`. Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Consider the case `pred i ih`. Establish `h` using `C.Calc.lg_add (C.Calc.lg_neg (hstep (-(i : ℤ) - 1))) ih`. Rewrite `h` using `[sub_add_cancel]`. Use `h using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.

Establish `h` using `main n`. Unfold `C.PhNormAt C.Cong`. Rewrite using `[C.Pts.mulBy_eq_fmul]`. Conclude with `h`.
-/
theorem phNorm_int {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hF : C.Frame R l linv ph) (h1 : C.F1 R l linv ph) (hneg : C.PhNormAt R l linv ph (-1) (-1))
    (h2 : (2 : K)⁻¹ ∈ R) (n : ℤ) : C.PhNormAt R l linv ph (n : K) (n : K) := by
  have hl : C.IsLogPair l linv := hF.1
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have hXpt : C.IsPt R (PowerSeries.X : MvPowerSeries Unit K) := C.Pts.isPt_X

  set q : K → MvPowerSeries Unit K :=
    fun a => PowerSeries.subst (C.fmul l linv a (PowerSeries.X : MvPowerSeries Unit K)) ph with hq
  set B : MvPowerSeries Unit K :=
    C.be0 l linv ph (PowerSeries.X : MvPowerSeries Unit K) (PowerSeries.X : MvPowerSeries Unit K)
    with hB
  have hphX : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) ph = ph :=
    PowerSeries.X_subst ph

  have hE : ∀ m : ℤ, C.LG R (q (1 + (m : K)) - ph - q (m : K) - (m : K) • B) := by
    intro m
    have h := C.zLinInt K R l linv ph hF h1 m Unit _ _ hXpt hXpt
    unfold C.Cong at h
    rw [C.be0] at h
    have e : C.fadd l linv (PowerSeries.X : MvPowerSeries Unit K)
        (C.fmul l linv (m : K) (PowerSeries.X : MvPowerSeries Unit K)) =
        C.fmul l linv (1 + (m : K)) (PowerSeries.X : MvPowerSeries Unit K) := by
      rw [C.Pts.fmul_add hl 1 (m : K) hX, C.Pts.fmul_one hl hX]
    rw [e, hphX] at h
    exact h
  have hq0 : q 0 = 0 := by
    simp only [hq]
    rw [C.Pts.fmul_zero_left hl, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2]
  have hN : C.LG R (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K))) := by
    have h := hneg
    unfold C.PhNormAt C.Cong at h
    rw [C.Pts.mulBy_eq_fmul] at h
    exact h

  have hG : C.LG R (B - (2 : K) • (ph : MvPowerSeries Unit K)) := by
    have h := C.Calc.lg_add (hE (-1)) hN
    have e : (q (1 + ((-1 : ℤ) : K)) - ph - q ((-1 : ℤ) : K) - ((-1 : ℤ) : K) • B) +
        (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K))) =
        B - (2 : K) • (ph : MvPowerSeries Unit K) := by
      have e0 : (1 : K) + ((-1 : ℤ) : K) = 0 := by push_cast; ring
      have e1 : (((-1 : ℤ) : K)) = -1 := by push_cast; ring
      rw [e0, hq0, e1]
      module
    rwa [e] at h
  have hstep : ∀ m : ℤ, C.LG R ((q (((m + 1 : ℤ)) : K) -
      ((((m + 1 : ℤ)) : K) * (((m + 1 : ℤ)) : K)) • (ph : MvPowerSeries Unit K)) -
      (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K))) := by
    intro m
    have h := C.Calc.lg_add (hE m) (C.lGBinom K R Unit (m : K) (C.intBinomScalar K R m) _ hG)
    have e1 : (((m + 1 : ℤ)) : K) = 1 + (m : K) := by push_cast; ring
    rw [e1]
    convert h using 1
    module
  have main : ∀ m : ℤ, C.LG R (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K)) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      have : q ((0 : ℤ) : K) - (((0 : ℤ) : K) * ((0 : ℤ) : K)) • (ph : MvPowerSeries Unit K) = 0 := by
        rw [Int.cast_zero, hq0]; simp
      rw [this]; exact C.Calc.lg_zero
    | succ i ih =>
      have h := C.Calc.lg_add (hstep i) ih
      rwa [sub_add_cancel] at h
    | pred i ih =>
      have h := C.Calc.lg_add (C.Calc.lg_neg (hstep (-(i : ℤ) - 1))) ih
      rw [sub_add_cancel] at h
      convert h using 1
      abel
  have h := main n
  unfold C.PhNormAt C.Cong
  rw [C.Pts.mulBy_eq_fmul]
  exact h

end ReciprocityTheory.ChartRestriction.L1
