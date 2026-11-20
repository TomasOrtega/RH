import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualExistence.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.AlgWtDualEx

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

/- English proof (translation)
Introduce `τ x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `IsCMField.complexEmbedding_complexConj L τ x`.
-/
theorem conjEmb : ConjEmb L := by
  intro τ x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact IsCMField.complexEmbedding_complexConj L τ x

variable {L n}

/- English proof (translation)
Establish `hm : ((γ : GAf L n) : GL (Fin n) (AL L)) = Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀` using `Units.ext h`. Unfold `Match`. Establish `: (((γ⁻¹ : GQ L n) : GAf L n) : GL (Fin n) (AL L)) = Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀⁻¹`. Rewrite using `[map_inv, ← hm]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Both sides reduce to the same expression.
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
Establish `h1 : ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L)` using `Units.inv_eq_of_mul_eq_one_right hγ`. Rewrite using `[h1]`. Both sides reduce to the same expression.
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
Introduce `hu hce a`. Take `⟨hfd, ι, _, _, b, P, hP⟩` from `a.alg`. Use `⟨inferInstance, ι, inferInstance, inferInstance, b.dualBasis, fun i j => MvPolynomial.rename (fun p : (L →+* ℂ) × Fin n × Fin n => (ComplexEmbedding.conjugate p.1, p.2.2, p.2.1)) (P j i), ?_⟩` and prove the remaining obligations. Introduce `γ γ₀ h`. Establish `hinv` using `hP γ⁻¹ γ₀⁻¹ (match_inv γ γ₀ h)`.

Establish `hγ` using `hu γ γ₀ h`. Establish `e : LinearMap.toMatrix b.dualBasis b.dualBasis (a.ρ.dual γ) = Matrix.transpose (LinearMap.toMatrix b b (a.ρ γ⁻¹))`. Rewrite using `[Representation.dual_apply, LinearMap.toMatrix_transpose]`. Rewrite using `[e, hinv]`. Use extensionality with `i j`.

Express the relevant statement in the definitionally equal form `MvPolynomial.eval (fun p : (L →+* ℂ) × Fin n × Fin n => p.1 (((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (P j i) = MvPolynomial.eval (fun p : (L →+* ℂ) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (MvPolynomial.rename (fun p : (L →+* …`. Rewrite using `[MvPolynomial.eval_rename]`. Use `congrArg (fun f => MvPolynomial.eval f (P j i)) (funext fun p => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Apply the tactic sequence `rw [inv_entry γ₀ hγ, hce]`.
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
