import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.FischerInvariance

open MvPolynomial GlobalTheory.DefLift.BilFischer

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem rowAct_eq_lin {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g =
      lin (fun v w : Fin n × Fin n => if w.2 = v.2 then g v.1 w.1 else 0) := by
  unfold Formalism.GradedWeylDivisibility.rowAct lin
  congr 1
  funext v
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single v.2]
  · simp [smul_eq_C_mul]
  · intro s _ hs
    simp [hs]
  · simp

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules.
-/
theorem rowAct_comp {n : ℕ} (g h : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) h) =
      Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (h * g) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, aeval_X, map_sum, map_mul, aeval_C,
    Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  simp [Algebra.algebraMap_eq_smul_one, mul_assoc]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem rowAct_inv_cancel {n : ℕ} (g : GL (Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ)
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) u) = u := by
  have h := congrArg (fun φ => φ u) (rowAct_comp (n := n) (g : Matrix (Fin n) (Fin n) ℂ)
    ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
  simp only [AlgHom.comp_apply] at h
  rw [h, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
  rw [this, AlgHom.id_apply]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_conj_self {σ : Type} [Fintype σ] (u : MvPolynomial σ ℂ) :
    pair (map (starRingEnd ℂ) u) u =
      ((∑ α ∈ u.support, (∏ i, ((α i).factorial : ℝ)) * Complex.normSq (coeff α u) : ℝ) : ℂ) := by
  have hv : map (starRingEnd ℂ) u = ∑ α ∈ u.support, monomial α (starRingEnd ℂ (coeff α u)) := by
    conv_lhs => rw [u.as_sum]
    rw [map_sum]
    simp only [map_monomial]
  rw [hv, map_sum, LinearMap.sum_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [pair_monomial, Complex.ofReal_mul, Complex.ofReal_prod, wt]
  push_cast
  rw [← Complex.mul_conj]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

A detailed English derivation is pending.
-/
theorem pair_conj_self_ne_zero {σ : Type} [Fintype σ] (u : MvPolynomial σ ℂ) (hu : u ≠ 0) :
    pair (map (starRingEnd ℂ) u) u ≠ 0 := by
  rw [pair_conj_self, Ne, Complex.ofReal_eq_zero]
  apply ne_of_gt
  apply Finset.sum_pos
  · intro α hα
    apply mul_pos
    · exact Finset.prod_pos fun i _ => Nat.cast_pos.2 (Nat.factorial_pos _)
    · exact Complex.normSq_pos.2 (mem_support_iff.1 hα)
  · exact support_nonempty.2 hu

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem fischer_dualWeyl_invariant (n : ℕ) (ν : Fin n → ℕ) :
    ∃ b : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      (∀ u ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, u ≠ 0 → ∃ v ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, b v u ≠ 0) ∧
      ∀ (g : GL (Fin n) ℂ) v u,
        b (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose v)
          (Formalism.UG.dwAct ℂ n n g u) = b v u := by
  refine ⟨pair, fun u hu hu0 => ⟨map (starRingEnd ℂ) u, GlobalTheory.SemilinTransport.map_mem _ hu,
    pair_conj_self_ne_zero u hu0⟩, fun g v u => ?_⟩
  rw [rowAct_eq_lin, pair_lin]
  have hT : (fun v w : Fin n × Fin n =>
      if v.2 = w.2 then (g : Matrix (Fin n) (Fin n) ℂ).transpose w.1 v.1 else 0) =
      fun v w => if w.2 = v.2 then (g : Matrix (Fin n) (Fin n) ℂ) v.1 w.1 else 0 := by
    funext v w
    by_cases h : v.2 = w.2
    · simp [h, Matrix.transpose_apply]
    · simp [h, Ne.symm h]
  rw [hT, ← rowAct_eq_lin]
  unfold Formalism.UG.dwAct
  rw [rowAct_inv_cancel]

end GlobalTheory.FischerInvariance

end
