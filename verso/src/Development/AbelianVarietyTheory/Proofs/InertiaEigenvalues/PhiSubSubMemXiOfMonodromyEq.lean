import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyMemRangeOfInvariantVectorStatement
open PowerSeries GlobalTheory.BK

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, ∀ σ : Vec K a ι, D.conn σ = D.zeta y → ∃ d : D.D, D.phi σ - σ - D.phi y = D.xi d := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy σ hσ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hyl : y ∈ D.Yl := D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hy⟩
  obtain ⟨⟨s, -, -, hs, d, -, hd⟩, -⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι η H D y hyl
  have h0 : D.conn (σ - s) = 0 := by rw [map_sub, hσ, hs, sub_self]
  set w := D.xiExt.symm (σ - s) with hw
  have hder : derV w = 0 := by
    have h1 : D.conn (D.xiExt w) = 0 := by rw [hw, LinearEquiv.apply_symm_apply]; exact h0
    rw [PhiMod.conn_apply, PhiMod.nabla_xiExt] at h1
    have h2 : D.xiExt (derV w) = 0 :=
      smul_right_injective (Vec K a ι) (X_ne_zero (R := K)) (by simpa only [smul_zero] using h1)
    exact D.xiExt.map_eq_zero_iff.1 h2
  have hwc : w = cst (red w) := by
    ext τ i n
    have h3 := congrArg (coeff n) (congrFun (congrFun hder τ) i)
    rw [derV_apply, coeff_derivative] at h3
    rcases n with _ | n
    · simp [red_apply, red0]
    · have h4 := congrArg (coeff n) (congrFun (congrFun hder τ) i)
      rw [derV_apply, coeff_derivative] at h4
      simp only [Pi.zero_apply, map_zero, mul_eq_zero] at h4
      rw [cst_apply, coeff_C, if_neg (Nat.succ_ne_zero n)]
      rcases h4 with h4 | h4
      · exact h4
      · exact absurd h4 (by exact_mod_cast Nat.succ_ne_zero n)
  have hxi : σ - s = D.xi (red w) := by
    rw [PhiMod.xi_apply, ← hwc, hw, LinearEquiv.apply_symm_apply]
  refine ⟨d + D.phiD (red w) - red w, ?_⟩
  rw [map_sub, map_add, ← PhiMod.phi_xi, ← hxi, ← hd, map_sub]
  abel
