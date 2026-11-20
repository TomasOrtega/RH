import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocPoly

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

namespace GlobalTheory.HenQ.DetSplit

variable {K : Type} [Field K] [NumberField K] [IsTotallyReal K] {n : ℕ}

omit [NumberField K] in
/- English proof (translation)
Establish `h` using `(InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.dist_eq r 0`. Establish `h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 : w.Completion) = 0` using `map_zero _`. Rewrite using `[← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]`. Conclude with `h`.
-/
theorem norm_realSymm (w : InfinitePlace K) (r : ℝ) :
    ‖((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r : w.Completion)‖ = |r| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.dist_eq r 0
  have h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 : w.Completion) = 0 :=
    map_zero _
  rw [← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]
  exact h

/- English proof (translation)
Rewrite using `[GroundTheory.Global.IdeleGroup.ideleModule_eq]`. Establish `h1 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).1 = UpperTheory.V.TR.infEq K u.val` using `by show (1 : InfiniteAdeleRing K) - UpperTheory.V.TR.infEq K 1 + UpperTheory.V.TR.infEq K u.val = _`. Simplify using the standard rewrite rules. Establish `h2 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).2 = 1` using `by show (1 : Af K) - 0 + 0 = 1`. Simplify using the standard rewrite rules.

Rewrite using `[h1, h2]`. Establish `h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : Af K) v‖ = 1` using `finprod_eq_one_of_forall_eq_one fun v => by exact norm_one`. Rewrite using `[h3, mul_one]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[(IsTotallyReal.isReal w).mult_eq_one, pow_one]`.

Conclude with `norm_realSymm w (u.val w)`.
-/
theorem ideleModule_infId (u : (Rinf K)ˣ) :
    (GroundTheory.Global.IdeleGroup.ideleModule K (UpperTheory.V.TR.infId K u) : ℝ) = ∏ w, |u.val w| := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).1 = UpperTheory.V.TR.infEq K u.val := by
    show (1 : InfiniteAdeleRing K) - UpperTheory.V.TR.infEq K 1 + UpperTheory.V.TR.infEq K u.val = _
    simp
  have h2 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).2 = 1 := by
    show (1 : Af K) - 0 + 0 = 1
    simp
  rw [h1, h2]
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : Af K) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by exact norm_one
  rw [h3, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  exact norm_realSymm w (u.val w)

end GlobalTheory.HenQ.DetSplit
