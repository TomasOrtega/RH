import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
namespace GlobalTheory.BigTop.Fun.PolBound
end GlobalTheory.BigTop.Fun.PolBound
namespace GlobalTheory.BigTop.Fun.PolBound
open Formalism.BasicNotions Formalism.MainNotions NumberField
end GlobalTheory.BigTop.Fun.PolBound
namespace GlobalTheory.BigTop.Fun
open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.BigTop.Fun.PolBound
/- English proof (translation)
Use `⟨0, fun CF _ => ?_⟩` and prove the remaining obligations. Use `⟨1 / 52, by norm_num, fun eps _ _ => ⟨⟨0, fun _ => 0, fun l => 16 * ((⌈|l.getD 0 0|⌉₊ : ℝ) + 1 + 9) + 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩` and prove the remaining obligations. Introduce `_`. Establish `hCH : 16 * ((⌈|Fm.Ct|⌉₊ : ℝ) + 1 + 9) + 1 ≤ CH` using `hL.2.2.1 CH (by simp [FamP.cMid])`. Use `⟨1, fun C hC => ?_⟩` and prove the remaining obligations.

Use `⟨max (13000000000 * C ^ 4) 1, fun x hx hxle i p _ d _ => ?_⟩` and prove the remaining obligations. Use `set T : ℕ := ⌈|Fm.Ct|⌉₊ + 1 with hTdef`. Establish `hT : (Fm.L x i).Ct + 1 ≤ T`. Rewrite using `[Fm.Ct_eq, hTdef]`. Use `push_cast`.

Combine the linear relations using `[le_abs_self Fm.Ct, Nat.le_ceil |Fm.Ct|]`. Take `⟨h1, h2, h3, h4, h5, h6, h7⟩` from `factors_le (Fm.L x i) (Fm.sizes x hx i) T hT`. Use `set X := (Fm.L x i).sc.x with hXdef`. Establish `hX1 : 1 ≤ X` using `(Fm.L x i).sc.one_lt_alt.le`. Establish `hXA : 13000000000 * C ^ 4 ≤ X`.

Rewrite using `[hXdef, Fm.L_x x i hx]`. Conclude with `(le_max_left _ _).trans hxle`. Use `set D := Fm.D x i`. Establish `eN : ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1)` using `by push_cast; ring`. Establish `enr : ((D.R.k + D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m` using `by push_cast; ring`.

Establish `e : d.O.pol C p.Z.b = 100000 * C ^ 3 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) ^ 2 * (((D.R.k : ℝ) + D.R.m - 1) * ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) * Real.log (Fm.L x i).sc.b + C * (D.R.f : ℝ) ^ 2 * …` using `rfl`. Use `show d.O.pol C p.Z.b ≤ X ^ CH`. Rewrite using `[e, eN, enr]`. Rewrite `h7` using `[enr]`. Establish `key` using `pol_core hC (one_le_pow₀ hX1) (Nat.cast_nonneg _) h1 (Nat.cast_nonneg _) h2 (Nat.cast_nonneg _) h3 (Nat.cast_nonneg _) h4 h6 h5 h7`.

Use `key.trans ?_` and prove the remaining obligations. Establish `hp : (X ^ (T + 9)) ^ 16 = X ^ (16 * (T + 9))` using `by rw [← pow_mul, mul_comm]`. Establish `hC4 : 0 ≤ 13000000000 * C ^ 4` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hp]; exact mul_le_mul_of_nonneg_right hXA (by positivity)`.

Use `_ = X ^ ((16 * (T + 9) + 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_succ, mul_comm]`. Use `_ ≤ X ^ CH := by`. Use `rpow_mono hX1 ?_` and prove the remaining obligations. Rewrite `*` using `[hTdef]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem desPol_alt : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition := by
  refine ⟨0, fun CF _ => ?_⟩
  refine ⟨1 / 52, by norm_num, fun eps _ _ =>
    ⟨⟨0, fun _ => 0, fun l => 16 * ((⌈|l.getD 0 0|⌉₊ : ℝ) + 1 + 9) + 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩
  intro _
  have hCH : 16 * ((⌈|Fm.Ct|⌉₊ : ℝ) + 1 + 9) + 1 ≤ CH := hL.2.2.1 CH (by simp [FamP.cMid])
  refine ⟨1, fun C hC => ?_⟩
  refine ⟨max (13000000000 * C ^ 4) 1, fun x hx hxle i p _ d _ => ?_⟩
  set T : ℕ := ⌈|Fm.Ct|⌉₊ + 1 with hTdef
  have hT : (Fm.L x i).Ct + 1 ≤ T := by
    rw [Fm.Ct_eq, hTdef]; push_cast; linarith [le_abs_self Fm.Ct, Nat.le_ceil |Fm.Ct|]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := factors_le (Fm.L x i) (Fm.sizes x hx i) T hT
  set X := (Fm.L x i).sc.x with hXdef
  have hX1 : 1 ≤ X := (Fm.L x i).sc.one_lt_alt.le
  have hXA : 13000000000 * C ^ 4 ≤ X := by
    rw [hXdef, Fm.L_x x i hx]; exact (le_max_left _ _).trans hxle
  set D := Fm.D x i
  have eN : ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) =
      (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) := by push_cast; ring
  have enr : ((D.R.k + D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m := by push_cast; ring
  have e : d.O.pol C p.Z.b = 100000 * C ^ 3 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 *
      ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) ^ 2 *
      (((D.R.k : ℝ) + D.R.m - 1) * ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) *
        Real.log (Fm.L x i).sc.b + C * (D.R.f : ℝ) ^ 2 * ((D.R.k + D.R.m : ℕ) : ℝ) ^ 6 *
        Real.log ((Fm.L x i).sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) *
          (D.host.pde : ℝ) * (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|)) := rfl
  show d.O.pol C p.Z.b ≤ X ^ CH
  rw [e, eN, enr]
  rw [enr] at h7
  have key := pol_core hC (one_le_pow₀ hX1) (Nat.cast_nonneg _) h1 (Nat.cast_nonneg _) h2 (Nat.cast_nonneg _) h3
    (Nat.cast_nonneg _) h4 h6 h5 h7
  refine key.trans ?_
  have hp : (X ^ (T + 9)) ^ 16 = X ^ (16 * (T + 9)) := by rw [← pow_mul, mul_comm]
  have hC4 : 0 ≤ 13000000000 * C ^ 4 := by positivity
  calc 13000000000 * C ^ 4 * (X ^ (T + 9)) ^ 16 ≤ X * X ^ (16 * (T + 9)) := by
        rw [hp]; exact mul_le_mul_of_nonneg_right hXA (by positivity)
    _ = X ^ ((16 * (T + 9) + 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_succ, mul_comm]
    _ ≤ X ^ CH := by
        refine rpow_mono hX1 ?_
        rw [hTdef] at *
        push_cast
        linarith
end GlobalTheory.BigTop.Fun
end
