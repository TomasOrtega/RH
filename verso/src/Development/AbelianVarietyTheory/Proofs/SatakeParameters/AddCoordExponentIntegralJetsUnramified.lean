import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HurwitzSubstituteTwoSeries
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExponentialSpecification
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExistsUnitFactorizationBounded
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstZeroOfConstantCoeff
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.AddJet

open MvPowerSeries Formalism.L2.KerInert.Jet
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2)
open Formalism.L2.Th1.D (expF IsMul)

section Ball

variable (K : Type) [NormedField K] [IsUltrametricDist K]

def ball : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ball {x : K} : x ∈ ball K ↔ ‖x‖ ≤ 1 := Iff.rfl

end Ball

section Exp

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

/- English proof (translation)
The claim follows from `IsUltrametricDist.norm_natCast_le_one K n`.
-/
theorem norm_natCast_le (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_derivative]`. Unfold `lgF`. Rewrite using `[PowerSeries.coeff_mk, Finset.sum_mul]`. Use `(ball K).sum_mem fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Establish `hp : (l : K) ≠ 0` using `by exact_mod_cast (show l ≠ 0 by omega)`. Establish `e : ((n : K) + 1) = (l : K) ^ j * (l : K) ^ j`. Rewrite using `[← pow_add, ← two_mul]`. Establish `h' : ((n + 1 : ℕ) : K) = (((l ^ 2) ^ j : ℕ) : K)` using `by rw [h]`. Move the coercions through the operations in `at h'`.

Rewrite using `[h', ← pow_mul]`. Rewrite using `[e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hp), one_mul]`. Conclude with `(ball K).pow_mem (norm_natCast_le l) j`. Rewrite using `[zero_mul]`. Conclude with `(ball K).zero_mem`.
-/
theorem lgF_deriv_int (l : ℕ) (hl : 2 ≤ l) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative K (lgF K l)) ∈ ball K := by
  rw [PowerSeries.coeff_derivative]
  unfold lgF
  rw [PowerSeries.coeff_mk, Finset.sum_mul]
  refine (ball K).sum_mem fun j _ => ?_
  split_ifs with h
  · have hp : (l : K) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
    have e : ((n : K) + 1) = (l : K) ^ j * (l : K) ^ j := by
      rw [← pow_add, ← two_mul]
      have h' : ((n + 1 : ℕ) : K) = (((l ^ 2) ^ j : ℕ) : K) := by rw [h]
      push_cast at h'
      rw [h', ← pow_mul]
    rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hp), one_mul]
    exact (ball K).pow_mem (norm_natCast_le l) j
  · rw [zero_mul]
    exact (ball K).zero_mem

/- English proof (translation)
Rewrite using `[Formalism.L2.Th1.D.FormalExponential.expF_eq l hl]`. Use `hur_substInv (ball K) (Formalism.L2.Th1.D.Pair.cc_lgF hl) _ ?_ (lgF_deriv_int l hl)` and prove the remaining obligations. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, zero_add, Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hl]`. Simplify using the standard rewrite rules.
-/
theorem hur_expF (l : ℕ) (hl : 2 ≤ l) :
    Hur (ball K) ((expF K l : PowerSeries K) : MvPowerSeries Unit K) := by
  rw [Formalism.L2.Th1.D.FormalExponential.expF_eq l hl]
  refine hur_substInv (ball K) (Formalism.L2.Th1.D.Pair.cc_lgF hl) _ ?_ (lgF_deriv_int l hl)
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, zero_add,
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hl]
  simp

/- English proof (translation)
The claim follows from `(Formalism.L2.Th1.D.exponential_specification K l hl).1`.
-/
theorem cc_expF (l : ℕ) (hl : 2 ≤ l) : PowerSeries.constantCoeff (expF K l) = 0 :=
  (Formalism.L2.Th1.D.exponential_specification K l hl).1

/- English proof (translation)
Unfold `at1`. Rewrite using `[PowerSeries.subst_def]`. Conclude with `hur_subst (ball K) (fun _ => constantCoeff_X i) (fun _ => hur_X (ball K) i) (hur_expF l hl)`.
-/
theorem hurwitz_integral_expSeries_single_variable {ι : Type} [Fintype ι] [DecidableEq ι] (l : ℕ) (hl : 2 ≤ l) (i : ι) :
    Hur (ball K) (at1 i (expF K l) : MvPowerSeries ι K) := by
  unfold at1
  rw [PowerSeries.subst_def]
  exact hur_subst (ball K) (fun _ => constantCoeff_X i) (fun _ => hur_X (ball K) i) (hur_expF l hl)

/- English proof (translation)
Take `⟨h0, hI⟩` from `hs`. Rewrite `h0`, `hI` using `[sub_zero]`. Establish `hφ0 : ∀ i : τ, constantCoeff (at1 i (expF K l) : MvPowerSeries τ K) = 0` using `fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (cc_expF l hl)`. Establish `hE : Hur (ball K) (Formalism.L2.Th1.C.mvExp h)` using `hur_of_int _ fun n => hI n`. Establish `hS` using `hur_subst (ball K) hφ0 (fun i => hurwitz_integral_expSeries_single_variable l hl i) hE`.

Rewrite `hS` using `[Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp h0 hφ0]`. Use `set g := subst (fun i => (at1 i (expF K l) : MvPowerSeries τ K)) h with hg`. Establish `hg0 : constantCoeff g = 0` using `by rw [hg, cc_subst hφ0, h0]`. Establish `h1 : constantCoeff (Formalism.L2.Th1.C.mvExp g) = 1` using `Formalism.L2.Th1.C.constantCoeff_mvExp hg0`. Establish `hEi : Hur (ball K) (Formalism.L2.Th1.C.mvExp g)⁻¹` using `hur_inv _ hS h1`.

Use `hur_of_pderiv _ (by rw [hg0]; exact (ball K).zero_mem) fun i => ?_` and prove the remaining obligations. Establish `e : pderiv K i g = pderiv K i (Formalism.L2.Th1.C.mvExp g) * (Formalism.L2.Th1.C.mvExp g)⁻¹`. Rewrite using `[Formalism.L2.Th1.C.pderiv_mvExp hg0, mul_assoc, MvPowerSeries.mul_inv_cancel _ (by rw [h1]; exact one_ne_zero), mul_one]`. Rewrite using `[e]`. Conclude with `hur_mul _ (hur_pderiv _ hS i) hEi`.
-/
theorem hur_of_simeq0 {τ : Type} [Fintype τ] [DecidableEq τ] (l : ℕ) (hl : 2 ≤ l)
    {h : MvPowerSeries τ K} (hs : Simeq h 0) :
    Hur (ball K) (subst (fun i => (at1 i (expF K l) : MvPowerSeries τ K)) h) := by
  obtain ⟨h0, hI⟩ := hs
  rw [sub_zero] at h0 hI
  have hφ0 : ∀ i : τ, constantCoeff (at1 i (expF K l) : MvPowerSeries τ K) = 0 :=
    fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (cc_expF l hl)
  have hE : Hur (ball K) (Formalism.L2.Th1.C.mvExp h) := hur_of_int _ fun n => hI n
  have hS := hur_subst (ball K) hφ0 (fun i => hurwitz_integral_expSeries_single_variable l hl i) hE
  rw [Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp h0 hφ0] at hS
  set g := subst (fun i => (at1 i (expF K l) : MvPowerSeries τ K)) h with hg
  have hg0 : constantCoeff g = 0 := by rw [hg, cc_subst hφ0, h0]
  have h1 : constantCoeff (Formalism.L2.Th1.C.mvExp g) = 1 := Formalism.L2.Th1.C.constantCoeff_mvExp hg0
  have hEi : Hur (ball K) (Formalism.L2.Th1.C.mvExp g)⁻¹ := hur_inv _ hS h1
  refine hur_of_pderiv _ (by rw [hg0]; exact (ball K).zero_mem) fun i => ?_
  have e : pderiv K i g = pderiv K i (Formalism.L2.Th1.C.mvExp g) * (Formalism.L2.Th1.C.mvExp g)⁻¹ := by
    rw [Formalism.L2.Th1.C.pderiv_mvExp hg0, mul_assoc,
      MvPowerSeries.mul_inv_cancel _ (by rw [h1]; exact one_ne_zero), mul_one]
  rw [e]
  exact hur_mul _ (hur_pderiv _ hS i) hEi

end Exp

end GlobalTheory.AddJet

namespace GlobalTheory.AddJet

open MvPowerSeries Formalism.L2.KerInert.Jet Formalism.L2.Th1.D.Pair
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 cob)
open Formalism.L2.Th1.D (expF IsMul addC)

section Transfer

variable {K : Type} [Field K]

/- English proof (translation)
Establish `h0` using `(Formalism.L2.Th1.D.exponential_specification K l hl).1`. Establish `hs` using `hs2 hu hw`. Unfold `addC`. Rewrite using `[subst2_comp hs (constantCoeff_inVar_eq_zero _ h0) (constantCoeff_inVar_eq_zero _ h0), subst_single_var hs, subst_single_var hs]`. Both sides reduce to the same expression.
-/
theorem subst_addC (l : ℕ) (hl : 2 ≤ l) {τ : Type} {u w : MvPowerSeries τ K} (hu : constantCoeff u = 0)
    (hw : constantCoeff w = 0) (be0 : MvPowerSeries (Fin 2) K) :
    subst ![u, w] (addC l be0) =
      subst ![PowerSeries.subst u (expF K l), PowerSeries.subst w (expF K l)] be0 := by
  have h0 := (Formalism.L2.Th1.D.exponential_specification K l hl).1
  have hs := hs2 hu hw
  unfold addC
  rw [subst2_comp hs (constantCoeff_inVar_eq_zero _ h0) (constantCoeff_inVar_eq_zero _ h0), subst_single_var hs, subst_single_var hs]
  rfl

/- English proof (translation)
Establish `h0` using `(Formalism.L2.Th1.D.exponential_specification K l hl).1`. Unfold `at1`. Rewrite using `[ps_comp (constantCoeff_X x) h0, (Formalism.L2.Th1.D.exponential_specification K l hl).2.1, PowerSeries.subst_X (PowerSeries.HasSubst.X x)]`.
-/
theorem logSeries_subst_expSeries_variable (l : ℕ) (hl : 2 ≤ l) {τ : Type} (x : τ) :
    PowerSeries.subst (at1 x (expF K l) : MvPowerSeries τ K) (lgF K l) = X x := by
  have h0 := (Formalism.L2.Th1.D.exponential_specification K l hl).1
  unfold at1
  rw [ps_comp (constantCoeff_X x) h0, (Formalism.L2.Th1.D.exponential_specification K l hl).2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.X x)]

/- English proof (translation)
Establish `h0` using `(Formalism.L2.Th1.D.exponential_specification K l hl).1`. Establish `ha` using `constantCoeff_inVar_eq_zero (0 : Fin 3) h0`. Establish `hb` using `constantCoeff_inVar_eq_zero (1 : Fin 3) h0`. Apply the tactic sequence `have hc : constantCoeff (subst ![(at1 0 (expF K l) : MvPowerSeries (Fin 3) K), at1 1 (expF K l)] F) = 0 := constantCoeff_subst_eq_zero (hs2 ha hb) (by intro i; fin_cases i <;> simp [ha, hb]) hF0`. Establish `hlog` using `log_law hF0 hF ha hb`.

Rewrite `hlog` using `[logSeries_subst_expSeries_variable l hl, logSeries_subst_expSeries_variable l hl]`. Rewrite using `[← hlog, exp_log Formalism.L2.Th1.D.exponential_specification hl hc]`.
-/
theorem law_at_exp (l : ℕ) (hl : 2 ≤ l) {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0)
    (hF : cob F (lgF K l) = 0) :
    subst ![(at1 0 (expF K l) : MvPowerSeries (Fin 3) K), at1 1 (expF K l)] F =
      PowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 3) K) (expF K l) := by
  have h0 := (Formalism.L2.Th1.D.exponential_specification K l hl).1
  have ha := constantCoeff_inVar_eq_zero (0 : Fin 3) h0
  have hb := constantCoeff_inVar_eq_zero (1 : Fin 3) h0
  have hc : constantCoeff (subst ![(at1 0 (expF K l) : MvPowerSeries (Fin 3) K), at1 1 (expF K l)] F) = 0 :=
    constantCoeff_subst_eq_zero (hs2 ha hb) (by intro i; fin_cases i <;> simp [ha, hb]) hF0
  have hlog := log_law hF0 hF ha hb
  rw [logSeries_subst_expSeries_variable l hl, logSeries_subst_expSeries_variable l hl] at hlog
  rw [← hlog, exp_log Formalism.L2.Th1.D.exponential_specification hl hc]

/- English proof (translation)
Establish `h0` using `(Formalism.L2.Th1.D.exponential_specification K l hl).1`. Establish `ha` using `constantCoeff_inVar_eq_zero x h0`. Establish `hm` using `Formalism.L2.Th1.D.FormalExponential.isMul_root (K := K) hl hζ`. Establish `hw : PowerSeries.subst (at1 x (expF K l) : MvPowerSeries τ K) (PowerSeries.C ζ * PowerSeries.X) = C ζ * at1 x (expF K l)`. Establish `hs` using `PowerSeries.HasSubst.of_constantCoeff_zero ha`.

Rewrite using `[PowerSeries.subst_mul hs, PowerSeries.subst_C, PowerSeries.subst_X hs]`. Establish `hwc : constantCoeff (C ζ * at1 x (expF K l) : MvPowerSeries τ K) = 0`. Rewrite using `[map_mul, ha, mul_zero]`. Establish `hl2` using `log_mul hm ha`. Rewrite `hl2` using `[hw, logSeries_subst_expSeries_variable l hl]`.

Rewrite using `[← hl2, exp_log Formalism.L2.Th1.D.exponential_specification hl hwc]`.
-/
theorem exp_mul_root (l : ℕ) (hl : 2 ≤ l) {ζ : K} (hζ : ζ ^ (l ^ 2 - 1) = 1) {τ : Type} (x : τ) :
    PowerSeries.subst (C ζ * X x : MvPowerSeries τ K) (expF K l) = C ζ * at1 x (expF K l) := by
  have h0 := (Formalism.L2.Th1.D.exponential_specification K l hl).1
  have ha := constantCoeff_inVar_eq_zero x h0
  have hm := Formalism.L2.Th1.D.FormalExponential.isMul_root (K := K) hl hζ
  have hw : PowerSeries.subst (at1 x (expF K l) : MvPowerSeries τ K) (PowerSeries.C ζ * PowerSeries.X) =
      C ζ * at1 x (expF K l) := by
    have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
    rw [PowerSeries.subst_mul hs, PowerSeries.subst_C, PowerSeries.subst_X hs]
  have hwc : constantCoeff (C ζ * at1 x (expF K l) : MvPowerSeries τ K) = 0 := by
    rw [map_mul, ha, mul_zero]
  have hl2 := log_mul hm ha
  rw [hw, logSeries_subst_expSeries_variable l hl] at hl2
  rw [← hl2, exp_log Formalism.L2.Th1.D.exponential_specification hl hwc]

end Transfer

end GlobalTheory.AddJet

namespace GlobalTheory.AddJet

open MvPowerSeries Formalism.L2.KerInert.Jet

section Deriv

variable {K : Type} [Field K]

/- English proof (translation)
The claim follows from `constantCoeff_X i`.
-/
theorem constantCoeff_X_fin_three (i : Fin 3) : constantCoeff (X i : MvPowerSeries (Fin 3) K) = 0 := constantCoeff_X i

/- English proof (translation)
Establish `h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) K) = 0` using `by simp`. Simplify using `only [map_sub]`. Rewrite using `[pd2 _ h01 (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]`. Simplify using `only [map_add, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide), pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide), mul_zero, add_zero, mul_one, zero_add, sub_zero]`. Rewrite using `[pd2 _ h01 (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]`.

Simplify using `[pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide), pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide)]`.
-/
theorem dd_first (B : MvPowerSeries (Fin 2) K) :
    pderiv K 0 (pderiv K 1 (subst ![(X 0 + X 1 : MvPowerSeries (Fin 3) K), X 2] B -
      subst ![(X 0 : MvPowerSeries (Fin 3) K), X 2] B - subst ![(X 1 : MvPowerSeries (Fin 3) K), X 2] B)) =
      subst ![(X 0 + X 1 : MvPowerSeries (Fin 3) K), X 2] (pderiv K 0 (pderiv K 0 B)) := by
  have h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) K) = 0 := by simp
  simp only [map_sub]
  rw [pd2 _ h01 (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]
  simp only [map_add, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide), mul_zero, add_zero, mul_one, zero_add, sub_zero]
  rw [pd2 _ h01 (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]
  simp [pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide)]

/- English proof (translation)
Establish `h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) K) = 0` using `by simp`. Simplify using `only [map_sub]`. Rewrite using `[pd2 _ (constantCoeff_X_fin_three 2) h01, pd2 _ (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 0), pd2 _ (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 1)]`. Simplify using `only [map_add, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide), pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide), mul_zero, add_zero, mul_one, zero_add, sub_zero]`. Rewrite using `[pd2 _ (constantCoeff_X_fin_three 2) h01, pd2 _ (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 1)]`.

Simplify using `[pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide), pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide)]`.
-/
theorem dd_second (B : MvPowerSeries (Fin 2) K) :
    pderiv K 0 (pderiv K 1 (subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0 + X 1] B -
      subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0] B - subst ![(X 2 : MvPowerSeries (Fin 3) K), X 1] B)) =
      subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0 + X 1] (pderiv K 1 (pderiv K 1 B)) := by
  have h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) K) = 0 := by simp
  simp only [map_sub]
  rw [pd2 _ (constantCoeff_X_fin_three 2) h01, pd2 _ (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 0), pd2 _ (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 1)]
  simp only [map_add, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide), mul_zero, add_zero, mul_one, zero_add, sub_zero]
  rw [pd2 _ (constantCoeff_X_fin_three 2) h01, pd2 _ (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 1)]
  simp [pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide)]

/- English proof (translation)
Establish `ha : HasSubst (![u, w] : Fin 2 → MvPowerSeries (Fin 3) K)` using `hasSubst_of_constantCoeff_zero (cc2 hu hw)`. Establish `hbs : HasSubst b` using `hasSubst_of_constantCoeff_zero hb`. Rewrite using `[subst_comp_subst_apply ha hbs]`. Establish `e : (fun s => subst b ((![u, w] : Fin 2 → MvPowerSeries (Fin 3) K) s)) = X`. Use function extensionality and compare the values at `s`.

Use `fin_cases s`. Simplify using `using hbu`. Simplify using `using hbw`. Rewrite using `[e, subst_self]`. Both sides reduce to the same expression.
-/
theorem restr' (g : MvPowerSeries (Fin 2) K) (u w : MvPowerSeries (Fin 3) K)
    (b : Fin 3 → MvPowerSeries (Fin 2) K)
    (hu : constantCoeff u = 0) (hw : constantCoeff w = 0) (hb : ∀ j, constantCoeff (b j) = 0)
    (hbu : subst b u = X 0) (hbw : subst b w = X 1) :
    subst b (subst ![u, w] g) = g := by
  have ha : HasSubst (![u, w] : Fin 2 → MvPowerSeries (Fin 3) K) :=
    hasSubst_of_constantCoeff_zero (cc2 hu hw)
  have hbs : HasSubst b := hasSubst_of_constantCoeff_zero hb
  rw [subst_comp_subst_apply ha hbs]
  have e : (fun s => subst b ((![u, w] : Fin 2 → MvPowerSeries (Fin 3) K) s)) = X := by
    funext s
    fin_cases s
    · simpa using hbu
    · simpa using hbw
  rw [e, subst_self]
  rfl

/- English proof (translation)
Establish `hu : constantCoeff (C a' * X 0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `hw : constantCoeff (C b' * X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `hX0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0` using `constantCoeff_X 0`. Establish `hX1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0` using `constantCoeff_X 1`. Establish `hu0 : pderiv K 0 (C a' * X 0 : MvPowerSeries (Fin 2) K) = C a'`.

Rewrite using `[Derivation.leibniz]`. Simplify using the standard rewrite rules. Establish `hu1 : pderiv K 1 (C a' * X 0 : MvPowerSeries (Fin 2) K) = 0`. Rewrite using `[Derivation.leibniz]; simp [pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]`. Establish `hw0 : pderiv K 0 (C b' * X 1 : MvPowerSeries (Fin 2) K) = 0`.

Rewrite using `[Derivation.leibniz]; simp [pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]`. Establish `hw1 : pderiv K 1 (C b' * X 1 : MvPowerSeries (Fin 2) K) = C b'`. Rewrite using `[Derivation.leibniz]`. Simplify using the standard rewrite rules. Establish `A1 : pderiv K 1 (subst ![C a' * X 0, X 1] be : MvPowerSeries (Fin 2) K) =`.

Substitute `![C a' * X 0, X 1] (pderiv K 1 be) := by` using the available equality. Rewrite using `[pd2 _ hu hX1, hu1, pderiv_X_self]`. Expand and normalize the polynomial expressions, which then agree. Establish `A0 : pderiv K 0 (subst ![C a' * X 0, X 1] (pderiv K 1 be) : MvPowerSeries (Fin 2) K) =`. Substitute `![C a' * X 0, X 1] (pderiv K 0 (pderiv K 1 be)) * C a' := by` using the available equality.

Rewrite using `[pd2 _ hu hX1, hu0, pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]; ring`. Establish `B1 : pderiv K 1 (subst ![X 0, C b' * X 1] be : MvPowerSeries (Fin 2) K) =`. Substitute `![X 0, C b' * X 1] (pderiv K 1 be) * C b' := by` using the available equality. Rewrite using `[pd2 _ hX0 hw, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide), hw1]; ring`. Establish `B0 : pderiv K 0 (subst ![X 0, C b' * X 1] (pderiv K 1 be) * C b' : MvPowerSeries (Fin 2) K) =`.

Substitute `![X 0, C b' * X 1] (pderiv K 0 (pderiv K 1 be)) * C b' := by` using the available equality. Rewrite using `[Derivation.leibniz, pd2 _ hX0 hw, pderiv_C, pderiv_X_self, hw0]`. Simplify using `[mul_comm]`. Rewrite using `[map_sub, map_sub, A1, A0, B1, B0, map_sub, map_mul, map_mul, cc_subst (cc2 hu hX1), cc_subst (cc2 hX0 hw), constantCoeff_C, constantCoeff_C]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_dd' (be : MvPowerSeries (Fin 2) K) (a' b' : K) :
    constantCoeff (pderiv K 0 (pderiv K 1 (subst ![C a' * X 0, X 1] be - subst ![X 0, C b' * X 1] be :
      MvPowerSeries (Fin 2) K))) =
      constantCoeff (pderiv K 0 (pderiv K 1 be)) * (a' - b') := by
  have hu : constantCoeff (C a' * X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hw : constantCoeff (C b' * X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 0
  have hX1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 1
  have hu0 : pderiv K 0 (C a' * X 0 : MvPowerSeries (Fin 2) K) = C a' := by
    rw [Derivation.leibniz]; simp
  have hu1 : pderiv K 1 (C a' * X 0 : MvPowerSeries (Fin 2) K) = 0 := by
    rw [Derivation.leibniz]; simp [pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  have hw0 : pderiv K 0 (C b' * X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    rw [Derivation.leibniz]; simp [pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  have hw1 : pderiv K 1 (C b' * X 1 : MvPowerSeries (Fin 2) K) = C b' := by
    rw [Derivation.leibniz]; simp
  have A1 : pderiv K 1 (subst ![C a' * X 0, X 1] be : MvPowerSeries (Fin 2) K) =
      subst ![C a' * X 0, X 1] (pderiv K 1 be) := by
    rw [pd2 _ hu hX1, hu1, pderiv_X_self]; ring
  have A0 : pderiv K 0 (subst ![C a' * X 0, X 1] (pderiv K 1 be) : MvPowerSeries (Fin 2) K) =
      subst ![C a' * X 0, X 1] (pderiv K 0 (pderiv K 1 be)) * C a' := by
    rw [pd2 _ hu hX1, hu0, pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]; ring
  have B1 : pderiv K 1 (subst ![X 0, C b' * X 1] be : MvPowerSeries (Fin 2) K) =
      subst ![X 0, C b' * X 1] (pderiv K 1 be) * C b' := by
    rw [pd2 _ hX0 hw, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide), hw1]; ring
  have B0 : pderiv K 0 (subst ![X 0, C b' * X 1] (pderiv K 1 be) * C b' : MvPowerSeries (Fin 2) K) =
      subst ![X 0, C b' * X 1] (pderiv K 0 (pderiv K 1 be)) * C b' := by
    rw [Derivation.leibniz, pd2 _ hX0 hw, pderiv_C, pderiv_X_self, hw0]; simp [mul_comm]
  rw [map_sub, map_sub, A1, A0, B1, B0, map_sub, map_mul, map_mul, cc_subst (cc2 hu hX1),
    cc_subst (cc2 hX0 hw), constantCoeff_C, constantCoeff_C]
  ring

end Deriv

end GlobalTheory.AddJet

namespace GlobalTheory.AddJet

open MvPowerSeries Formalism.L2.KerInert.Jet Formalism.L2.Th1.D.Pair
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 cob)
open Formalism.L2.Th1.D (expF IsMul addC)

section Main

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

omit [CharZero K] in
/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])`.
-/
theorem norm_sub_le_max'' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])

/- English proof (translation)
Establish `hq0 : l * 2 ≤ l * l` using `Nat.mul_le_mul_left l hl`. Establish `hpos : 0 < l ^ 2 - 1` using `by rw [sq]; omega`. Establish `hζ1 : ζ ^ (l ^ 2 - 1) = 1` using `hζ.pow_eq_one`. Establish `hnζ : ‖ζ‖ = 1` using `Formalism.L2.Th1.D.FormalExponential.norm_eq_one_of_pow hpos.ne' hζ1`. Establish `hN : ‖((l ^ 2 - 1 : ℕ) : K)‖ = 1`.

Rewrite using `[Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]`. Establish `hq : ‖(l : K) ^ 2‖ < 1`. Rewrite using `[norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hlt1 (by norm_num)`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `(norm_sub_le_max'' _ _).trans (max_le hq.le (by simp))`.

Assume the negation of the conclusion as `hc push_neg at hc`. Establish `h1 : ‖(1 : K)‖ ≤ max ‖(l : K) ^ 2‖ ‖(l : K) ^ 2 - 1‖`. Use `norm_sub_le_max'' ((l : K) ^ 2) ((l : K) ^ 2 - 1)` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[norm_one]`.

Conclude with `absurd h1 (not_le.2 (max_lt hq hc))`. Establish `hle : ‖ζ - ζ ^ l‖ ≤ 1` using `(norm_sub_le_max'' _ _).trans (max_le hnζ.le (by rw [norm_pow, hnζ, one_pow]))`. Use `le_antisymm hle (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Establish `hζl : (ζ ^ l) ^ (l ^ 2 - 1) = 1` using `by rw [← pow_mul, mul_comm, pow_mul, hζ1, one_pow]`. Establish `heq` using `Formalism.L2.Th1.D.FormalExponential.root_eq_of_norm_lt hN hζ1 hζl hlt`.

Establish `hz : ζ ≠ 0`. Introduce `h`. Rewrite `hnζ` using `[h, norm_zero]`. Conclude with `zero_ne_one hnζ`. Establish `hp : ζ ^ (l - 1) = 1`.

Establish `: ζ ^ (l - 1) * ζ = 1 * ζ`. Rewrite using `[← pow_succ, Nat.sub_add_cancel (by omega), one_mul, ← heq]`. Conclude with `mul_right_cancel₀ hz this`. Establish `hd` using `(hζ.pow_eq_one_iff_dvd (l - 1)).1 hp`. Establish `hle' : l ^ 2 - 1 ≤ l - 1` using `Nat.le_of_dvd (by omega) hd`.

Rewrite `hle'` using `[sq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem norm_root_sub_pow (l : ℕ) (hl : 2 ≤ l) (hlt1 : ‖(l : K)‖ < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1)) : ‖ζ - ζ ^ l‖ = 1 := by
  have hq0 : l * 2 ≤ l * l := Nat.mul_le_mul_left l hl
  have hpos : 0 < l ^ 2 - 1 := by rw [sq]; omega
  have hζ1 : ζ ^ (l ^ 2 - 1) = 1 := hζ.pow_eq_one
  have hnζ : ‖ζ‖ = 1 := Formalism.L2.Th1.D.FormalExponential.norm_eq_one_of_pow hpos.ne' hζ1
  have hN : ‖((l ^ 2 - 1 : ℕ) : K)‖ = 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
    have hq : ‖(l : K) ^ 2‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hlt1 (by norm_num)
    apply le_antisymm
    · exact (norm_sub_le_max'' _ _).trans (max_le hq.le (by simp))
    · by_contra hc
      push_neg at hc
      have h1 : ‖(1 : K)‖ ≤ max ‖(l : K) ^ 2‖ ‖(l : K) ^ 2 - 1‖ := by
        have := norm_sub_le_max'' ((l : K) ^ 2) ((l : K) ^ 2 - 1)
        simpa using this
      rw [norm_one] at h1
      exact absurd h1 (not_le.2 (max_lt hq hc))
  have hle : ‖ζ - ζ ^ l‖ ≤ 1 :=
    (norm_sub_le_max'' _ _).trans (max_le hnζ.le (by rw [norm_pow, hnζ, one_pow]))
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have hζl : (ζ ^ l) ^ (l ^ 2 - 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ1, one_pow]
  have heq := Formalism.L2.Th1.D.FormalExponential.root_eq_of_norm_lt hN hζ1 hζl hlt
  have hz : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnζ
    exact zero_ne_one hnζ
  have hp : ζ ^ (l - 1) = 1 := by
    have : ζ ^ (l - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, ← heq]
    exact mul_right_cancel₀ hz this
  have hd := (hζ.pow_eq_one_iff_dvd (l - 1)).1 hp
  have hle' : l ^ 2 - 1 ≤ l - 1 := Nat.le_of_dvd (by omega) hd
  rw [sq] at hle'
  omega

/- English proof (translation)
Establish `hl : 2 ≤ l` using `hU.1.two_le`. Take `⟨hF0, -, hcob⟩` from `hF`. Take `⟨hab, hd1, hd2⟩` from `h1`. Establish `h0` using `(Formalism.L2.Th1.D.exponential_specification K l hl).1`. Establish `e3 : (fun i : Fin 3 => (at1 i (expF K l) : MvPowerSeries (Fin 3) K)) = ![at1 0 (expF K l), at1 1 (expF K l), at1 2 (expF K l)]`.

Apply the tactic sequence `funext i; fin_cases i <;> rfl`. Establish `c3 : ∀ i : Fin 3, constantCoeff (at1 i (expF K l) : MvPowerSeries (Fin 3) K) = 0` using `fun i => constantCoeff_inVar_eq_zero i h0`. Establish `hlaw` using `law_at_exp l hl hF0 hcob`. Establish `hX01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) K) = 0` using `by simp`. Establish `hD1 : Hur (ball K) (subst ![(X 0 + X 1 : MvPowerSeries (Fin 3) K), X 2] (addC l be0) -`.

Substitute `![(X 0 : MvPowerSeries (Fin 3) K), X 2] (addC l be0) -` using the available equality. Substitute `![(X 1 : MvPowerSeries (Fin 3) K), X 2] (addC l be0)) := by` using the available equality. Establish `H` using `hur_of_simeq0 (τ := Fin 3) l hl hd1`. Rewrite `H` using `[e3, subst_first_coboundary_three hF0 (c3 0) (c3 1) (c3 2), hlaw]`. Rewrite using `[subst_addC l hl hX01 (constantCoeff_X_fin_three 2), subst_addC l hl (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2), subst_addC l hl (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]`.

Conclude with `H`. Establish `hD2 : Hur (ball K) (subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0 + X 1] (addC l be0) -`. Substitute `![(X 2 : MvPowerSeries (Fin 3) K), X 0] (addC l be0) -` using the available equality. Substitute `![(X 2 : MvPowerSeries (Fin 3) K), X 1] (addC l be0)) := by` using the available equality. Establish `H` using `hur_of_simeq0 (τ := Fin 3) l hl hd2`.

Rewrite `H` using `[e3, subst_first_coboundary_three hF0 (c3 0) (c3 1) (c3 2), hlaw, subst_swap2 (cc_ps hX01 h0) (c3 2), subst_swap2 (c3 0) (c3 2), subst_swap2 (c3 1) (c3 2)]`. Rewrite using `[subst_addC l hl (constantCoeff_X_fin_three 2) hX01, subst_addC l hl (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 0), subst_addC l hl (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 1)]`. Conclude with `H`. Establish `h00 : Hur (ball K) (pderiv K 0 (pderiv K 0 (addC l be0)))`. Establish `H` using `hur_pderiv _ (hur_pderiv _ hD1 1) 0`.

Rewrite `H` using `[dd_first]`. Establish `hb0 : ∀ j, constantCoeff ((![X 0, 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) K) j) = 0`. Apply the tactic sequence `intro j; fin_cases j <;> simp`. Establish `hb : HasSubst (![X 0, 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) K)` using `hasSubst_of_constantCoeff_zero hb0`. Apply the tactic sequence `have := hur_subst (ball K) hb0 (by intro j; fin_cases j <;> simp [hur_X, hur_zero]) H`.

Rewrite `this` using `[restr' _ _ _ _ (by simp) (by simp) hb0 (by rw [subst_add hb, subst_X hb, subst_X hb]; simp) (by rw [subst_X hb]; simp)]`. Then use the resulting hypothesis. Establish `h11 : Hur (ball K) (pderiv K 1 (pderiv K 1 (addC l be0)))`. Establish `H` using `hur_pderiv _ (hur_pderiv _ hD2 1) 0`. Rewrite `H` using `[dd_second]`. Establish `hb0 : ∀ j, constantCoeff ((![X 1, 0, X 0] : Fin 3 → MvPowerSeries (Fin 2) K) j) = 0`.

Apply the tactic sequence `intro j; fin_cases j <;> simp`. Establish `hb : HasSubst (![X 1, 0, X 0] : Fin 3 → MvPowerSeries (Fin 2) K)` using `hasSubst_of_constantCoeff_zero hb0`. Apply the tactic sequence `have := hur_subst (ball K) hb0 (by intro j; fin_cases j <;> simp [hur_X, hur_zero]) H`. Rewrite `this` using `[restr' _ _ _ _ (by simp) (by simp) hb0 (by rw [subst_X hb]; simp) (by rw [subst_add hb, subst_X hb, subst_X hb]; simp)]`. Then use the resulting hypothesis. Establish `hζ1 : ζ ^ (l ^ 2 - 1) = 1` using `hζ.pow_eq_one`.

Establish `hσζ : σ ζ = ζ ^ l` using `Formalism.L2.Th1.D.teichmuller_sigma K l 2 σ hU (by norm_num) ζ hζ1`. Establish `hζ'1 : (σ ζ) ^ (l ^ 2 - 1) = 1` using `by rw [hσζ, ← pow_mul, mul_comm, pow_mul, hζ1, one_pow]`. Establish `hq0 : l * 2 ≤ l * l` using `Nat.mul_le_mul_left l hl`. Establish `hnζ : ‖ζ‖ = 1` using `Formalism.L2.Th1.D.FormalExponential.norm_eq_one_of_pow (by rw [sq]; omega) hζ1`. Establish `hσσ : σ (σ ζ) = ζ`.

Rewrite using `[hσζ, map_pow, hσζ, ← pow_mul]`. Establish `: l * l = (l ^ 2 - 1) + 1` using `by rw [sq]; omega`. Rewrite using `[this, pow_succ, hζ1, one_mul]`. Establish `hC` using `h2 ζ hnζ.le hσσ _ _ (Formalism.L2.Th1.D.FormalExponential.isMul_root hl hζ1) (Formalism.L2.Th1.D.FormalExponential.isMul_root hl hζ'1)`. Rewrite `hC` using `[Formalism.L2.Th1.D.FormalExponential.at_variable_C_mul_X, Formalism.L2.Th1.D.FormalExponential.at_variable_C_mul_X]`.

Establish `hC' : Simeq (subst ![C ζ * X 0, X 1] be0 - subst ![X 0, C (σ ζ) * X 1] be0 : MvPowerSeries (Fin 2) K) 0`. Unfold `Simeq at hC ⊢`. Rewrite using `[sub_zero]` and apply the resulting hypothesis. Establish `H` using `hur_of_simeq0 (τ := Fin 2) l hl hC'`. Establish `e2 : (fun i : Fin 2 => (at1 i (expF K l) : MvPowerSeries (Fin 2) K)) = ![at1 0 (expF K l), at1 1 (expF K l)]`.

Apply the tactic sequence `funext i; fin_cases i <;> rfl`. Establish `hs2' : HasSubst ![(at1 0 (expF K l) : MvPowerSeries (Fin 2) K), at1 1 (expF K l)]` using `hs2 (constantCoeff_inVar_eq_zero _ h0) (constantCoeff_inVar_eq_zero _ h0)`. Rewrite `H` using `[e2, subst_sub hs2', subst2_comp hs2' (by simp) (by simp), subst2_comp hs2' (by simp) (by simp), subst_mul hs2', subst_mul hs2', subst_C, subst_C, subst_X hs2', subst_X hs2']`. Establish `hD3 : Hur (ball K) (subst ![C ζ * X 0, X 1] (addC l be0) -`. Substitute `![X 0, C (σ ζ) * X 1] (addC l be0) : MvPowerSeries (Fin 2) K) := by` using the available equality.

Rewrite using `[subst_addC l hl (by simp) (by simp), subst_addC l hl (by simp) (by simp), exp_mul_root l hl hζ1, exp_mul_root l hl hζ'1]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one] at H`. Conclude with `H`. Establish `hlt1 : ‖(l : K)‖ < 1`. Rewrite using `[hU.2.2.1]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hU.1.one_lt)`.

Establish `hsep : ‖ζ - σ ζ‖ = 1` using `by rw [hσζ]; exact norm_root_sub_pow l hl hlt1 hζ`. Establish `h01 : constantCoeff (pderiv K 0 (pderiv K 1 (addC l be0))) ∈ ball K`. Establish `hc` using `hur_cc _ (hur_pderiv _ (hur_pderiv _ hD3 1) 0)`. Rewrite `hc` using `[conj_dd', mem_ball, norm_mul, hsep, mul_one]`. Conclude with `hc`.

Establish `hDiv : DivAB (addC l be0)` using `Formalism.L2.Th1.D.TorusDerivation.divAB_addC l hab`. Introduce `n`. Distinguish the cases in `hz : n 0 = 0 ∨ n 1 = 0`. Rewrite using `[hDiv n hz, mul_zero]`. Conclude with `(ball K).zero_mem`.

Use `push_neg at hz`. Distinguish the cases in `h2' : 2 ≤ n 0`. Establish `e1` using `decomp n 0 hz.1`. Establish `hm : (n - Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 ≠ 0` using `by simp; omega`. Establish `e2` using `decomp (n - Finsupp.single 0 1) 0 hm`.

Rewrite using `[e1, ← fc_coeff_pderiv, e2, ← fc_coeff_pderiv]`. Conclude with `h00 _`. Distinguish the cases in `h2'' : 2 ≤ n 1`. Establish `e1` using `decomp n 1 hz.2`. Establish `hm : (n - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 ≠ 0` using `by simp; omega`.

Establish `e2` using `decomp (n - Finsupp.single 1 1) 1 hm`. Rewrite using `[e1, ← fc_coeff_pderiv, e2, ← fc_coeff_pderiv]`. Conclude with `h11 _`. Establish `en : n = (0 + Finsupp.single 0 1) + Finsupp.single 1 1`. Use extensionality with `x`.

Apply the tactic sequence `fin_cases x <;> simp <;> omega`. Rewrite using `[en, ← fc_coeff_pderiv, ← fc_coeff_pderiv, fc_zero, one_mul, coeff_zero_eq_constantCoeff_apply]`. Conclude with `h01`.
-/
theorem hur_addC (l : ℕ) (σ : K →+* K) (hU : Formalism.InvariantFactorPaths.G7.UnrOK K l σ) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1)) {F be0 : MvPowerSeries (Fin 2) K}
    (hF : Formalism.InvariantFactorPaths.G7.IsLawOfLog l F) (h1 : Formalism.L2.Th1.D.F1 F be0) (h2 : Formalism.L2.Th1.D.F2 l σ be0) :
    Hur (ball K) (addC l be0) := by
  have hl : 2 ≤ l := hU.1.two_le
  obtain ⟨hF0, -, hcob⟩ := hF
  obtain ⟨hab, hd1, hd2⟩ := h1
  have h0 := (Formalism.L2.Th1.D.exponential_specification K l hl).1
  have e3 : (fun i : Fin 3 => (at1 i (expF K l) : MvPowerSeries (Fin 3) K)) =
      ![at1 0 (expF K l), at1 1 (expF K l), at1 2 (expF K l)] := by
    funext i; fin_cases i <;> rfl
  have c3 : ∀ i : Fin 3, constantCoeff (at1 i (expF K l) : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => constantCoeff_inVar_eq_zero i h0
  have hlaw := law_at_exp l hl hF0 hcob
  have hX01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have hD1 : Hur (ball K) (subst ![(X 0 + X 1 : MvPowerSeries (Fin 3) K), X 2] (addC l be0) -
      subst ![(X 0 : MvPowerSeries (Fin 3) K), X 2] (addC l be0) -
      subst ![(X 1 : MvPowerSeries (Fin 3) K), X 2] (addC l be0)) := by
    have H := hur_of_simeq0 (τ := Fin 3) l hl hd1
    rw [e3, subst_first_coboundary_three hF0 (c3 0) (c3 1) (c3 2), hlaw] at H
    rw [subst_addC l hl hX01 (constantCoeff_X_fin_three 2), subst_addC l hl (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2),
      subst_addC l hl (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]
    exact H
  have hD2 : Hur (ball K) (subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0 + X 1] (addC l be0) -
      subst ![(X 2 : MvPowerSeries (Fin 3) K), X 0] (addC l be0) -
      subst ![(X 2 : MvPowerSeries (Fin 3) K), X 1] (addC l be0)) := by
    have H := hur_of_simeq0 (τ := Fin 3) l hl hd2
    rw [e3, subst_first_coboundary_three hF0 (c3 0) (c3 1) (c3 2), hlaw, subst_swap2 (cc_ps hX01 h0) (c3 2),
      subst_swap2 (c3 0) (c3 2), subst_swap2 (c3 1) (c3 2)] at H
    rw [subst_addC l hl (constantCoeff_X_fin_three 2) hX01, subst_addC l hl (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 0),
      subst_addC l hl (constantCoeff_X_fin_three 2) (constantCoeff_X_fin_three 1)]
    exact H
  have h00 : Hur (ball K) (pderiv K 0 (pderiv K 0 (addC l be0))) := by
    have H := hur_pderiv _ (hur_pderiv _ hD1 1) 0
    rw [dd_first] at H
    have hb0 : ∀ j, constantCoeff ((![X 0, 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) K) j) = 0 := by
      intro j; fin_cases j <;> simp
    have hb : HasSubst (![X 0, 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) K) :=
      hasSubst_of_constantCoeff_zero hb0
    have := hur_subst (ball K) hb0 (by intro j; fin_cases j <;> simp [hur_X, hur_zero]) H
    rwa [restr' _ _ _ _ (by simp) (by simp) hb0 (by rw [subst_add hb, subst_X hb, subst_X hb]; simp)
      (by rw [subst_X hb]; simp)] at this
  have h11 : Hur (ball K) (pderiv K 1 (pderiv K 1 (addC l be0))) := by
    have H := hur_pderiv _ (hur_pderiv _ hD2 1) 0
    rw [dd_second] at H
    have hb0 : ∀ j, constantCoeff ((![X 1, 0, X 0] : Fin 3 → MvPowerSeries (Fin 2) K) j) = 0 := by
      intro j; fin_cases j <;> simp
    have hb : HasSubst (![X 1, 0, X 0] : Fin 3 → MvPowerSeries (Fin 2) K) :=
      hasSubst_of_constantCoeff_zero hb0
    have := hur_subst (ball K) hb0 (by intro j; fin_cases j <;> simp [hur_X, hur_zero]) H
    rwa [restr' _ _ _ _ (by simp) (by simp) hb0 (by rw [subst_X hb]; simp)
      (by rw [subst_add hb, subst_X hb, subst_X hb]; simp)] at this
  have hζ1 : ζ ^ (l ^ 2 - 1) = 1 := hζ.pow_eq_one
  have hσζ : σ ζ = ζ ^ l := Formalism.L2.Th1.D.teichmuller_sigma K l 2 σ hU (by norm_num) ζ hζ1
  have hζ'1 : (σ ζ) ^ (l ^ 2 - 1) = 1 := by rw [hσζ, ← pow_mul, mul_comm, pow_mul, hζ1, one_pow]
  have hq0 : l * 2 ≤ l * l := Nat.mul_le_mul_left l hl
  have hnζ : ‖ζ‖ = 1 :=
    Formalism.L2.Th1.D.FormalExponential.norm_eq_one_of_pow (by rw [sq]; omega) hζ1
  have hσσ : σ (σ ζ) = ζ := by
    rw [hσζ, map_pow, hσζ, ← pow_mul]
    have : l * l = (l ^ 2 - 1) + 1 := by rw [sq]; omega
    rw [this, pow_succ, hζ1, one_mul]
  have hC := h2 ζ hnζ.le hσσ _ _ (Formalism.L2.Th1.D.FormalExponential.isMul_root hl hζ1)
    (Formalism.L2.Th1.D.FormalExponential.isMul_root hl hζ'1)
  rw [Formalism.L2.Th1.D.FormalExponential.at_variable_C_mul_X, Formalism.L2.Th1.D.FormalExponential.at_variable_C_mul_X] at hC
  have hC' : Simeq (subst ![C ζ * X 0, X 1] be0 - subst ![X 0, C (σ ζ) * X 1] be0 :
      MvPowerSeries (Fin 2) K) 0 := by
    unfold Simeq at hC ⊢
    rwa [sub_zero]
  have H := hur_of_simeq0 (τ := Fin 2) l hl hC'
  have e2 : (fun i : Fin 2 => (at1 i (expF K l) : MvPowerSeries (Fin 2) K)) =
      ![at1 0 (expF K l), at1 1 (expF K l)] := by
    funext i; fin_cases i <;> rfl
  have hs2' : HasSubst ![(at1 0 (expF K l) : MvPowerSeries (Fin 2) K), at1 1 (expF K l)] :=
    hs2 (constantCoeff_inVar_eq_zero _ h0) (constantCoeff_inVar_eq_zero _ h0)
  rw [e2, subst_sub hs2', subst2_comp hs2' (by simp) (by simp),
    subst2_comp hs2' (by simp) (by simp), subst_mul hs2', subst_mul hs2', subst_C, subst_C,
    subst_X hs2', subst_X hs2'] at H
  have hD3 : Hur (ball K) (subst ![C ζ * X 0, X 1] (addC l be0) -
      subst ![X 0, C (σ ζ) * X 1] (addC l be0) : MvPowerSeries (Fin 2) K) := by
    rw [subst_addC l hl (by simp) (by simp), subst_addC l hl (by simp) (by simp),
      exp_mul_root l hl hζ1, exp_mul_root l hl hζ'1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at H
    exact H
  have hlt1 : ‖(l : K)‖ < 1 := by
    rw [hU.2.2.1]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hU.1.one_lt)
  have hsep : ‖ζ - σ ζ‖ = 1 := by rw [hσζ]; exact norm_root_sub_pow l hl hlt1 hζ
  have h01 : constantCoeff (pderiv K 0 (pderiv K 1 (addC l be0))) ∈ ball K := by
    have hc := hur_cc _ (hur_pderiv _ (hur_pderiv _ hD3 1) 0)
    rw [conj_dd', mem_ball, norm_mul, hsep, mul_one] at hc
    exact hc
  have hDiv : DivAB (addC l be0) := Formalism.L2.Th1.D.TorusDerivation.divAB_addC l hab
  intro n
  by_cases hz : n 0 = 0 ∨ n 1 = 0
  · rw [hDiv n hz, mul_zero]
    exact (ball K).zero_mem
  · push_neg at hz
    by_cases h2' : 2 ≤ n 0
    · have e1 := decomp n 0 hz.1
      have hm : (n - Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 ≠ 0 := by simp; omega
      have e2 := decomp (n - Finsupp.single 0 1) 0 hm
      rw [e1, ← fc_coeff_pderiv, e2, ← fc_coeff_pderiv]
      exact h00 _
    · by_cases h2'' : 2 ≤ n 1
      · have e1 := decomp n 1 hz.2
        have hm : (n - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 ≠ 0 := by simp; omega
        have e2 := decomp (n - Finsupp.single 1 1) 1 hm
        rw [e1, ← fc_coeff_pderiv, e2, ← fc_coeff_pderiv]
        exact h11 _
      · have en : n = (0 + Finsupp.single 0 1) + Finsupp.single 1 1 := by
          ext x
          fin_cases x <;> simp <;> omega
        rw [en, ← fc_coeff_pderiv, ← fc_coeff_pderiv, fc_zero, one_mul,
          coeff_zero_eq_constantCoeff_apply]
        exact h01

end Main

end GlobalTheory.AddJet

namespace GlobalTheory.AddJet

open Formalism.L2.KerInert.Jet

/- English proof (translation)
Introduce `l _ σ F be0 hU hF h1 h2 n`. Establish `hl : 2 ≤ l` using `hU.1.two_le`. Establish `hq0 : l * 2 ≤ l * l` using `Nat.mul_le_mul_left l hl`. Establish `hpos : 0 < l ^ 2 - 1` using `by rw [sq]; omega`. Establish `hnd : ¬ l ∣ l ^ 2 - 1`.

Introduce `hd`. Establish `h' : l ∣ (l ^ 2 - 1) + 1`. Rewrite using `[Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]`. Conclude with `dvd_pow_self l (by norm_num)`. Establish `h1' : l ∣ 1` using `(Nat.dvd_add_right hd).1 h'`.

Conclude with `hU.1.one_lt.ne' (Nat.dvd_one.1 h1')`. Take `⟨ζ, hζ⟩` from `Formalism.L2.Th1.D.unramified_completion_roots l (l ^ 2 - 1) hpos hnd`. Establish `H` using `hur_addC l σ hU hζ hF h1 h2 n`. Establish `e : (fc n : MaximalUnramifiedExtension l) = (((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l)`. Rewrite using `[fc_of_subset (S := Finset.univ) (Finset.subset_univ _), Fin.prod_univ_two]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e]`. Conclude with `H`.
-/
theorem addC_integral_jets : ∀ (l : ℕ) [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)),
    UnrOK (MaximalUnramifiedExtension l) l σ → IsLawOfLog l F → F1 F be0 → F2 l σ be0 → ∀ n : Fin 2 →₀ ℕ,
      ‖(((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) * MvPowerSeries.coeff n (addC l be0)‖ ≤ 1 := by
  intro l _ σ F be0 hU hF h1 h2 n
  have hl : 2 ≤ l := hU.1.two_le
  have hq0 : l * 2 ≤ l * l := Nat.mul_le_mul_left l hl
  have hpos : 0 < l ^ 2 - 1 := by rw [sq]; omega
  have hnd : ¬ l ∣ l ^ 2 - 1 := by
    intro hd
    have h' : l ∣ (l ^ 2 - 1) + 1 := by
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]
      exact dvd_pow_self l (by norm_num)
    have h1' : l ∣ 1 := (Nat.dvd_add_right hd).1 h'
    exact hU.1.one_lt.ne' (Nat.dvd_one.1 h1')
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.unramified_completion_roots l (l ^ 2 - 1) hpos hnd
  have H := hur_addC l σ hU hζ hF h1 h2 n
  have e : (fc n : MaximalUnramifiedExtension l) = (((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) := by
    rw [fc_of_subset (S := Finset.univ) (Finset.subset_univ _), Fin.prod_univ_two]
    push_cast
    ring
  rw [← e]
  exact H

end GlobalTheory.AddJet
