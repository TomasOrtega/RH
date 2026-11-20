import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcPerm

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem rowAct_permMatrix (k : Type) [Field k] (N : ℕ) (σ : Equiv.Perm (Fin N))
    (f : MvPolynomial (Fin N × Fin N) k) :
    Formalism.GradedWeylDivisibility.rowAct k (n := N) (σ.permMatrix k) f = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f := by
  have : Formalism.GradedWeylDivisibility.rowAct k (n := N) (σ.permMatrix k) = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, rename_X]
    rw [Finset.sum_eq_single (σ v.1)]
    · simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    · intro b _ hb
      simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Ne.symm hb]
    · simp
  rw [this]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem perm_stable : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M → ∀ σ : Equiv.Perm (Fin N), ∀ f ∈ M, rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f ∈ M := by
  intro k _ N lam M hM σ f hf
  have hdet : ((σ⁻¹).permMatrix k).det ≠ 0 := by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> simp [h]
  set g : GL (Fin N) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hg
  have h1 := hM k g f hf
  have hid : (map (algebraMap k k) : MvPolynomial (Fin N × Fin N) k →+* _) = RingHom.id _ := by
    rw [Algebra.algebraMap_self]; exact RingHom.ext fun p => map_id p
  have hspan : Submodule.span k (map (algebraMap k k) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) = M := by
    rw [hid]; simp
  rw [hspan, hid, RingHom.id_apply] at h1
  have hgT : (g : Matrix (Fin N) (Fin N) k).transpose = σ.permMatrix k := by
    rw [hg]
    show ((σ⁻¹).permMatrix k).transpose = _
    rw [Matrix.transpose_permMatrix, inv_inv]
  unfold sqAct at h1
  rw [hgT, rowAct_permMatrix] at h1
  have hu : IsUnit (detPow k N g lam.detShift) := by
    unfold detPow; exact Units.isUnit _
  rcases hu with ⟨u, hu⟩
  rw [← hu] at h1
  have := M.smul_mem ((u⁻¹ : kˣ) : k) h1
  rwa [smul_smul, Units.inv_mul, one_smul] at this

end GlobalTheory.AlcPerm
