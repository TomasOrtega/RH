import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualExistence.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.AlgWtDualEx

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conjEmb : ConjEmb L := by
  intro τ x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact IsCMField.complexEmbedding_complexConj L τ x

variable {L n}

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem match_inv (γ : GQ L n) (γ₀ : GL (Fin n) L) (h : Match L n γ γ₀) : Match L n γ⁻¹ γ₀⁻¹ := by
  have hm : ((γ : GAf L n) : GL (Fin n) (AL L)) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀ :=
    Units.ext h
  unfold Match
  have : (((γ⁻¹ : GQ L n) : GAf L n) : GL (Fin n) (AL L)) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀⁻¹ := by
    rw [map_inv, ← hm]
    rfl
  rw [this]
  rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem inv_entry (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) (k l : Fin n) :
    ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k l =
      (IsCMField.complexConj L : L →+* L) ((γ₀ : Matrix (Fin n) (Fin n) L) l k) := by
  have h1 : ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
    Units.inv_eq_of_mul_eq_one_right hγ
  rw [h1]
  rfl

variable (L n)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem algDualCore : AlgDualCore L n := by
  intro hu hce a
  obtain ⟨hfd, ι, _, _, b, P, hP⟩ := a.alg
  refine ⟨inferInstance, ι, inferInstance, inferInstance, b.dualBasis,
    fun i j => MvPolynomial.rename
      (fun p : (L →+* ℂ) × Fin n × Fin n => (ComplexEmbedding.conjugate p.1, p.2.2, p.2.1)) (P j i), ?_⟩
  intro γ γ₀ h
  have hinv := hP γ⁻¹ γ₀⁻¹ (match_inv γ γ₀ h)
  have hγ := hu γ γ₀ h
  have e : LinearMap.toMatrix b.dualBasis b.dualBasis (a.ρ.dual γ) =
      Matrix.transpose (LinearMap.toMatrix b b (a.ρ γ⁻¹)) := by
    rw [Representation.dual_apply, LinearMap.toMatrix_transpose]
  rw [e, hinv]
  ext i j
  change MvPolynomial.eval (fun p : (L →+* ℂ) × Fin n × Fin n =>
      p.1 (((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (P j i) =
    MvPolynomial.eval (fun p : (L →+* ℂ) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2))
      (MvPolynomial.rename (fun p : (L →+* ℂ) × Fin n × Fin n =>
        (ComplexEmbedding.conjugate p.1, p.2.2, p.2.1)) (P j i))
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun f => MvPolynomial.eval f (P j i)) (funext fun p => ?_)
  simp only [Function.comp_apply]
  rw [inv_entry γ₀ hγ, hce]

end PI.UnitaryGroupMassFormula.AlgWtDualEx
