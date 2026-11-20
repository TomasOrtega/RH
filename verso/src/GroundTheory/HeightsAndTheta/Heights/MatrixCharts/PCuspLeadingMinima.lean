import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace CuspLeadingMinima

/- English proof (translation)
Use `⟨Pi.single (Fin.castLE h j) 1, fun k hk => ?_, ?_⟩` and prove the remaining obligations. Establish `hne : k ≠ Fin.castLE h j`. Introduce `e`. Use `j.isLt` as an intermediate fact. Rewrite `hk` using `[e]`.

Simplify using `at hk`. Use linear arithmetic over natural numbers and integers. Simplify using `[hne]`. Use extensionality with `k`. Distinguish the cases in `e : k = Fin.castLE h j`.

Substitute `e` using the available equality. Simplify using `[intVecC]`. Simplify using `[intVecC, e]`.
-/
theorem single_mem_leadingLattice {g r : ℕ} (h : r ≤ g) (j : Fin r) :
    Pi.single (Fin.castLE h j) (1 : ℂ) ∈ leadingLattice g r := by
  refine ⟨Pi.single (Fin.castLE h j) 1, fun k hk => ?_, ?_⟩
  · have hne : k ≠ Fin.castLE h j := by
      intro e
      have := j.isLt
      rw [e] at hk
      simp at hk
      omega
    simp [hne]
  · ext k
    by_cases e : k = Fin.castLE h j
    · subst e; simp [intVecC]
    · simp [intVecC, e]

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Use `congrFun hc (Fin.castLE h i)` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Pi.single_apply, (Fin.castLE_injective h).eq_iff] at this`. Simplify using `using this`.
-/
theorem single_linearIndependent {g r : ℕ} (h : r ≤ g) :
    LinearIndependent ℤ (fun j : Fin r => (Pi.single (Fin.castLE h j) (1 : ℂ) : Fin g → ℂ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have := congrFun hc (Fin.castLE h i)
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Pi.single_apply,
    (Fin.castLE_injective h).eq_iff] at this
  simpa using this

/- English proof (translation)
Rewrite using `[MCSchur.hermValue_eq_qf]`. Establish `hre : (fun l => ((Pi.single k (1 : ℂ) : ι → ℂ) l).re) = Pi.single k (1 : ℝ)`. Use extensionality with `l`. Distinguish the cases in `e : l = k`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[e]`. Establish `him : (fun l => ((Pi.single k (1 : ℂ) : ι → ℂ) l).im) = 0`. Use extensionality with `l`. Distinguish the cases in `e : l = k`.

Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[e]`. Rewrite using `[hre, him]`. Simplify using `[MCSchur.qf, mulVec_single]`.
-/
theorem hermValue_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (k : ι) :
    hermValue A (Pi.single k (1 : ℂ)) = A k k := by
  rw [MCSchur.hermValue_eq_qf]
  have hre : (fun l => ((Pi.single k (1 : ℂ) : ι → ℂ) l).re) = Pi.single k (1 : ℝ) := by
    ext l
    by_cases e : l = k
    · subst e; simp
    · simp [e]
  have him : (fun l => ((Pi.single k (1 : ℂ) : ι → ℂ) l).im) = 0 := by
    ext l
    by_cases e : l = k
    · subst e; simp
    · simp [e]
  rw [hre, him]
  simp [MCSchur.qf, mulVec_single]

end CuspLeadingMinima

/- English proof (translation)
Introduce `D T p _ hp ℓ hℓ`. Take `⟨hpd, hge⟩` from `hImPos D p.1 hp ℓ hℓ`. Use `set Y := (D.period p.1 ℓ).map Complex.im`. Use `⟨fun j => (Pi.single (Fin.castLE T.r_le j) (1 : ℂ) : Fin D.g → ℂ), fun j => CuspLeadingMinima.single_mem_leadingLattice T.r_le j, CuspLeadingMinima.single_linearIndependent T.r_le, fun j => ?_⟩` and prove the remaining obligations. Use `set k := Fin.castLE T.r_le j`.

Establish `hc` using `D.c_pos`. Establish `hdiag : Y⁻¹ k k ≤ 1 / D.c`. Use `MCCusp.inv_diag_le hpd k hc fun x => ?_` and prove the remaining obligations. Establish `h1 : x k ^ 2 ≤ ∑ l, x l ^ 2` using `Finset.single_le_sum (f := fun l => x l ^ 2) (fun l _ => sq_nonneg (x l)) (Finset.mem_univ k)`. Combine the equalities or inequalities in the displayed calculation.

Unfold `metricLength`. Rewrite using `[CuspLeadingMinima.hermValue_single]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_eq_rpow, Real.rpow_neg hc.le, one_div, Real.inv_rpow hc.le]`.
-/
theorem CuspLeadingMinima.proof (hImPos : ChartPeriodImPos.Statement) :
    CuspLeadingMinima.Statement := by
  intro D T p _ hp ℓ hℓ
  obtain ⟨hpd, hge⟩ := hImPos D p.1 hp ℓ hℓ
  set Y := (D.period p.1 ℓ).map Complex.im
  refine ⟨fun j => (Pi.single (Fin.castLE T.r_le j) (1 : ℂ) : Fin D.g → ℂ),
    fun j => CuspLeadingMinima.single_mem_leadingLattice T.r_le j,
    CuspLeadingMinima.single_linearIndependent T.r_le, fun j => ?_⟩
  set k := Fin.castLE T.r_le j
  have hc := D.c_pos
  have hdiag : Y⁻¹ k k ≤ 1 / D.c := by
    refine MCCusp.inv_diag_le hpd k hc fun x => ?_
    have h1 : x k ^ 2 ≤ ∑ l, x l ^ 2 :=
      Finset.single_le_sum (f := fun l => x l ^ 2) (fun l _ => sq_nonneg (x l))
        (Finset.mem_univ k)
    calc D.c * x k ^ 2 ≤ D.c * ∑ l, x l ^ 2 := mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ _ := hge x
  unfold metricLength
  rw [CuspLeadingMinima.hermValue_single]
  calc Real.sqrt (Y⁻¹ k k) ≤ Real.sqrt (1 / D.c) := Real.sqrt_le_sqrt hdiag
    _ = D.c ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hc.le, one_div, Real.inv_rpow hc.le]

end

end GroundTheory.Heights₂.Heights
