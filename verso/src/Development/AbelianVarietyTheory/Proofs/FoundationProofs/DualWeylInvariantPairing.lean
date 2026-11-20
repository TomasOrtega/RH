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
Unfold `Formalism.GradedWeylDivisibility.rowAct lin`. Use `congr 1`. Use function extensionality and compare the values at `v`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single v.2]`. Simplify using `[smul_eq_C_mul]`. Introduce `s _ hs`. Simplify using `[hs]`. Simplify using the standard rewrite rules.
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
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, aeval_X, map_sum, map_mul, aeval_C, Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Simplify using `[Algebra.algebraMap_eq_smul_one, mul_assoc]`.
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
Establish `h` using `congrArg (fun φ => φ u) (rowAct_comp (n := n) (g : Matrix (Fin n) (Fin n) ℂ) ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))`. Simplify using `only [AlgHom.comp_apply] at h`. Rewrite using `[h, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `: Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `n) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `v`. Simplify using `[Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]`. Rewrite using `[this, AlgHom.id_apply]`.
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
Establish `hv : map (starRingEnd ℂ) u = ∑ α ∈ u.support, monomial α (starRingEnd ℂ (coeff α u))` using `by conv_lhs => rw [u.as_sum]`. Rewrite using `[map_sum]`. Simplify using `only [map_monomial]`. Rewrite using `[hv, map_sum, LinearMap.sum_apply, Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations.

Rewrite using `[pair_monomial, Complex.ofReal_mul, Complex.ofReal_prod, wt]`. Use `push_cast`. Rewrite using `[← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree.
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
Rewrite using `[pair_conj_self, Ne, Complex.ofReal_eq_zero]`. Apply `ne_of_gt` to reduce the goal to its premises. Apply `Finset.sum_pos` to reduce the goal to its premises. Introduce `α hα`. Apply `mul_pos` to reduce the goal to its premises.

Conclude with `Finset.prod_pos fun i _ => Nat.cast_pos.2 (Nat.factorial_pos _)`. Conclude with `Complex.normSq_pos.2 (mem_support_iff.1 hα)`. Conclude with `support_nonempty.2 hu`.
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
Use `⟨pair, fun u hu hu0 => ⟨map (starRingEnd ℂ) u, GlobalTheory.SemilinTransport.map_mem _ hu, pair_conj_self_ne_zero u hu0⟩, fun g v u => ?_⟩` and prove the remaining obligations. Rewrite using `[rowAct_eq_lin, pair_lin]`. Establish `hT : (fun v w : Fin n × Fin n => if v.2 = w.2 then (g : Matrix (Fin n) (Fin n) ℂ).transpose w.1 v.1 else 0) = fun v w => if w.2 = v.2 then (g : Matrix (Fin n) (Fin n) ℂ) v.1 w.1 else 0`. Use function extensionality and compare the values at `v w`. Distinguish the cases in `h : v.2 = w.2`.

Simplify using `[h, Matrix.transpose_apply]`. Simplify using `[h, Ne.symm h]`. Rewrite using `[hT, ← rowAct_eq_lin]`. Unfold `Formalism.UG.dwAct`. Rewrite using `[rowAct_inv_cancel]`.
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
