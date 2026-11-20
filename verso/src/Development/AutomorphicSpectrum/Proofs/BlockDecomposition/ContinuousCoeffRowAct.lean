import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.WInfCont

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuous_coeff_rowAct {r m : ℕ} (f : MvPolynomial (Fin r × Fin m) ℂ) :
    ∀ s : (Fin r × Fin m) →₀ ℕ, Continuous fun M : Matrix (Fin r) (Fin r) ℂ =>
      MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro s
    simpa [MvPolynomial.algebraMap_eq] using
      (continuous_const : Continuous fun _ : Matrix (Fin r) (Fin r) ℂ => MvPolynomial.coeff s (MvPolynomial.C a))
  | add p q hp hq =>
    intro s
    simp only [map_add, MvPolynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    have key : ∀ M : Matrix (Fin r) (Fin r) ℂ, MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M (p * MvPolynomial.X v)) =
        ∑ b : Fin r, M v.1 b * (if (b, v.2) ∈ s.support then
          MvPolynomial.coeff (s - Finsupp.single (b, v.2) 1) (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M p) else 0) := by
      intro M
      have hX : Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M (MvPolynomial.X v) =
          ∑ b : Fin r, MvPolynomial.C (M v.1 b) * MvPolynomial.X (b, v.2) := by
        simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, hX, Finset.mul_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']
    simp only [key]
    refine continuous_finset_sum _ fun b _ => ?_
    refine ((continuous_id.matrix_elem v.1 b)).mul ?_
    split_ifs
    · exact hp _
    · exact continuous_const

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem continuous_detPow (n : ℕ) (c : ℤ) : Continuous fun g : GL (Fin n) ℂ => detPow ℂ n g c := by
  have h0 : Continuous (Matrix.detMonoidHom : Matrix (Fin n) (Fin n) ℂ →* ℂ) := continuous_id.matrix_det
  have h1 : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ →* ℂˣ) :=
    Continuous.units_map _ h0
  exact Units.continuous_val.comp (h1.zpow c)

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_coeff_sqAct {n : ℕ} (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) ℂ)
    (s : (Fin n × Fin n) →₀ ℕ) :
    Continuous fun g : GL (Fin n) ℂ => MvPolynomial.coeff s (sqAct ℂ n lam g f) := by
  simp only [sqAct, MvPolynomial.coeff_smul, smul_eq_mul]
  exact (continuous_detPow n _).mul
    ((continuous_coeff_rowAct f s).comp Units.continuous_val.matrix_transpose)

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_finset_factor {σ : Type} (W : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) : ∃ (S : Finset (σ →₀ ℕ)) (c : S → ℂ),
      ∀ p : W, φ p = ∑ s : S, c s * MvPolynomial.coeff s.1 p.1 := by
  let b := Module.finBasis ℂ W
  let S : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun i => (b i : MvPolynomial σ ℂ).support
  let L : W →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun p s => MvPolynomial.coeff s.1 p.1
      map_add' := fun p q => by funext s; simp
      map_smul' := fun a p => by funext s; simp }
  have hL : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun p hp => ?_
    apply Subtype.ext
    refine MvPolynomial.ext _ _ fun s => ?_
    by_cases hs : s ∈ S
    · simpa [L] using congrFun hp ⟨s, hs⟩
    · have h0 : ∀ i, MvPolynomial.coeff s (b i : MvPolynomial σ ℂ) = 0 := fun i => by
        by_contra h
        exact hs (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, MvPolynomial.mem_support_iff.2 h⟩)
      have hp' : (p : MvPolynomial σ ℂ) = ∑ i, b.repr p i • (b i : MvPolynomial σ ℂ) := by
        have h := congrArg Subtype.val (b.sum_repr p)
        rw [AddSubmonoidClass.coe_finset_sum] at h
        exact h.symm
      rw [hp']
      simp [MvPolynomial.coeff_sum, h0]
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective L hL
  refine ⟨S, fun s => (φ ∘ₗ ψ) fun j => if s = j then 1 else 0, fun p => ?_⟩
  have e : φ p = (φ ∘ₗ ψ) (L p) := by
    have h := LinearMap.congr_fun hψ p
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h ⊢
    rw [h]
  rw [e, LinearMap.pi_apply_eq_sum_univ (φ ∘ₗ ψ) (L p)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_eq_mul, mul_comm]
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_sqRep_coeff {n : ℕ} (lam : DomWeight n) (f : nablaSq ℂ n lam)
    (φ : Module.Dual ℂ (nablaSq ℂ n lam)) :
    Continuous fun g : GL (Fin n) ℂ => φ (GlobalTheory.Branching.sqRep ℂ n lam g f) := by
  obtain ⟨S, c, h⟩ := exists_finset_factor (nablaSq ℂ n lam) φ
  simp only [h]
  exact continuous_finset_sum _ fun s _ => continuous_const.mul (continuous_coeff_sqAct lam f.1 s.1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.CompanionTheory.WInfCont
