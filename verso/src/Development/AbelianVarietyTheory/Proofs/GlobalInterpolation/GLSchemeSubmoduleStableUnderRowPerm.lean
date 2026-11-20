import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcPerm

/- English proof (translation)
Establish `: Formalism.GradedWeylDivisibility.rowAct k (n` using `N) (σ.permMatrix k) = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, rename_X]`. Rewrite using `[Finset.sum_eq_single (σ v.1)]`.

Simplify using `[PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]`. Introduce `b _ hb`. Simplify using `[PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Ne.symm hb]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.
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
Introduce `k _ N lam M hM σ f hf`. Establish `hdet : ((σ⁻¹).permMatrix k).det ≠ 0`. Rewrite using `[Matrix.det_permutation]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> simp [h]`. Use `set g : GL (Fin N) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hg`.

Establish `h1` using `hM k g f hf`. Establish `hid : (map (algebraMap k k) : MvPolynomial (Fin N × Fin N) k →+* _) = RingHom.id _`. Rewrite using `[Algebra.algebraMap_self]`. Conclude with `RingHom.ext fun p => map_id p`. Establish `hspan : Submodule.span k (map (algebraMap k k) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) = M`.

Rewrite using `[hid]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[hspan, hid, RingHom.id_apply]`. Establish `hgT : (g : Matrix (Fin N) (Fin N) k).transpose = σ.permMatrix k`. Rewrite using `[hg]`.

Use `show ((σ⁻¹).permMatrix k).transpose = _`. Rewrite using `[Matrix.transpose_permMatrix, inv_inv]`. Unfold `sqAct at h1`. Rewrite `h1` using `[hgT, rowAct_permMatrix]`. Establish `hu : IsUnit (detPow k N g lam.detShift)`.

Unfold `detPow`. Conclude with `Units.isUnit _`. Break down `hu with ⟨u, hu⟩` into its components or cases. Rewrite `h1` using `[← hu]`. Use `M.smul_mem ((u⁻¹ : kˣ) : k) h1` as an intermediate fact.

Rewrite `this` using `[smul_smul, Units.inv_mul, one_smul]`. Then use the resulting hypothesis.
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
