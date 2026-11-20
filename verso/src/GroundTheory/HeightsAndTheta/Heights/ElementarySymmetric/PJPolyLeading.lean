import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.JPolyLeading
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PJQExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PLevelOneQExpansion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial Filter Topology

noncomputable section

def JPolyLeading.homog (Q : ℤ[X]) (p : ℂ × ℂ) : ℂ :=
  ∑ i ∈ Finset.range (Q.natDegree + 1), (Q.coeff i : ℂ) * p.1 ^ i * p.2 ^ (Q.natDegree - i)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem JPolyLeading.continuous_homog (Q : ℤ[X]) : Continuous (JPolyLeading.homog Q) := by
  unfold JPolyLeading.homog
  fun_prop

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem JPolyLeading.homog_one_zero (Q : ℤ[X]) :
    JPolyLeading.homog Q (1, 0) = (Q.leadingCoeff : ℂ) := by
  unfold JPolyLeading.homog
  rw [Finset.sum_eq_single Q.natDegree]
  · simp only [one_pow, Nat.sub_self, pow_zero, mul_one]
    rfl
  · intro i hi hid
    have : Q.natDegree - i ≠ 0 := by
      have := Finset.mem_range.mp hi
      omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem JPolyLeading.pow_mul_aeval (Q : ℤ[X]) (q x : ℂ) :
    q ^ Q.natDegree * aeval x Q = JPolyLeading.homog Q (q * x, q) := by
  rw [aeval_eq_sum_range, Finset.mul_sum]
  unfold JPolyLeading.homog
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hd : Q.natDegree = i + (Q.natDegree - i) := (Nat.add_sub_cancel' hi').symm
  conv_lhs => rw [hd]
  rw [zsmul_eq_mul, pow_add, mul_pow]
  dsimp only
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem JPolyLeading.proof : JPolyLeading.Statement := by
  intro Q
  obtain ⟨c, hc0, hc⟩ := JQExpansion.proof
  have h1 : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ * modularJ τ) atImInfty (𝓝 1) := by
    have := LevelOneQExpansion.tendsto_of_hasSum (a := PowerSeries.mk c) (B := 0)
      (F := fun τ : ℍ ↦ Function.Periodic.qParam 1 τ * modularJ τ)
      (fun τ _ ↦ by
        have ht : LevelOneQExpansion.term (PowerSeries.mk c) (Function.Periodic.qParam 1 τ) =
            fun n ↦ (c n : ℂ) * Function.Periodic.qParam 1 τ ^ n :=
          funext fun n ↦ by simp [LevelOneQExpansion.term]
        rw [ht]
        exact hc τ)
    simpa [hc0] using this
  have h2 : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 (τ : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  have h := ((JPolyLeading.continuous_homog Q).tendsto (1, 0)).comp (h1.prodMk_nhds h2)
  rw [JPolyLeading.homog_one_zero] at h
  refine h.congr fun τ ↦ ?_
  simp only [Function.comp_apply]
  exact (JPolyLeading.pow_mul_aeval Q _ _).symm

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
