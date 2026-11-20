import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwB

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

variable {k r : ℕ}

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem RL_unrealify (Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    RL (k := k) (r := r) (Formalism.MainNotions.S.unrealify Y) = Y := by
  ext ⟨i, j, b⟩
  cases b <;> simp [RL, Formalism.MainNotions.S.realifyFun, Formalism.MainNotions.S.unrealify]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_RL (X : Mat k r) : ‖RL X‖ = ‖X‖ := by
  rw [EuclideanSpace.norm_eq, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [RL, Formalism.MainNotions.S.realifyFun, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs, sq_abs, if_true, Bool.false_eq_true,
    if_false]
  rw [Real.rpow_two, Complex.sq_norm, Complex.normSq_apply]
  simp [WithLp.equiv]
  unfold Formalism.MainNotions.S.realifyFun
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

def LongWeylElementSquare : Prop := ∀ k r : ℕ, w0B k r * w0B k r = 1

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem uh_mul {a b : Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  rw [mem_UH_iff] at *
  rw [adjH_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (adjH a), ha, Matrix.one_mul, hb]

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem approx {ι : Type*} (P : ι → Prop) (nm : ι → ℝ≥0) (R T : ℝ≥0∞)
    (h : (⨅ i, ⨅ (_ : P i), (nm i : ℝ≥0∞)) ^ 2 + R < T) : ∃ i, P i ∧ (nm i : ℝ≥0∞) ^ 2 + R < T := by
  set x := ⨅ i, ⨅ (_ : P i), (nm i : ℝ≥0∞) with hx
  have hxt : x < ⊤ := by
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h
    simp at h
  have hopen : IsOpen {t : ℝ≥0∞ | t ^ 2 + R < T} :=
    isOpen_lt ((ENNReal.continuous_pow 2).add continuous_const) continuous_const
  obtain ⟨u, hxu, hu⟩ := exists_Ico_subset_of_mem_nhds (hopen.mem_nhds h) ⟨⊤, hxt⟩
  have : x < u := hxu
  rw [hx, iInf_lt_iff] at this
  obtain ⟨i, hi⟩ := this
  rw [iInf_lt_iff] at hi
  obtain ⟨hPi, hlt⟩ := hi
  refine ⟨i, hPi, hu ⟨?_, hlt⟩⟩
  exact iInf₂_le i hPi

end Formalism.L2.SG.Pf.BH.Sw
