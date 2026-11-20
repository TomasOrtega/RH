import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

/- English proof (translation)
Introduce `l _ P AI T d s v v₀ t p hv h lam`. Substitute `hv` using the available equality. Set `Λ : OB P →ₗ[↥(MaximalUnramifiedExtension l)] Bst P` to `(TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P)).toLinearMap ∘ₗ lam.rTensor (Bst P)`. Establish `hΛ : ∀ (x : Om l) (b : Bst P), Λ (x ⊗ₜ b) = lam x • b`. Introduce `x b`.

Express the relevant statement in the definitionally equal form `TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P) (lam.rTensor (Bst P) (x ⊗ₜ b)) = lam x • b`. Rewrite using `[LinearMap.rTensor_tmul, TensorProduct.lid_tmul]`. Establish `h1` using `congrArg Λ h`. Rewrite `h1` using `[map_sum, hΛ]`. Simplify using `only [hΛ] at h1`.

Establish `hc : lam p • (1 : Bst P) = Polynomial.C (lam p • (1 : P.R.B))`. Rewrite using `[← Polynomial.smul_C, map_one]`. Establish `h2 : (∑ i, lam (t i) • T.eB.symm (v₀ i)) = lam p • (1 : P.R.B)`. Apply `Polynomial.C_injective` to reduce the goal to its premises. Rewrite using `[map_sum, ← hc, ← h1]`.

Simplify using `only [Polynomial.smul_C]`. Simplify using `only [Algebra.smul_def] at h2`. Establish `h3` using `congrArg T.eB h2`. Simplify using `only [map_sum, map_mul, map_one, mul_one, RingEquiv.apply_symm_apply] at h3`. Establish `h4 : ∑ i, uB T (lam (t i)) * v₀ i = uB T (lam p)` using `h3`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← h4, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.testTr_holds :
    TestTr := by
  intro l _ P AI T d s v v₀ t p hv h lam
  subst hv
  let Λ : OB P →ₗ[↥(MaximalUnramifiedExtension l)] Bst P :=
    (TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P)).toLinearMap ∘ₗ lam.rTensor (Bst P)
  have hΛ : ∀ (x : Om l) (b : Bst P), Λ (x ⊗ₜ b) = lam x • b := by
    intro x b
    change TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P) (lam.rTensor (Bst P) (x ⊗ₜ b)) = lam x • b
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  have h1 := congrArg Λ h
  rw [map_sum, hΛ] at h1
  simp only [hΛ] at h1
  have hc : lam p • (1 : Bst P) = Polynomial.C (lam p • (1 : P.R.B)) := by
    rw [← Polynomial.smul_C, map_one]
  have h2 : (∑ i, lam (t i) • T.eB.symm (v₀ i)) = lam p • (1 : P.R.B) := by
    apply Polynomial.C_injective
    rw [map_sum, ← hc, ← h1]
    simp only [Polynomial.smul_C]
  simp only [Algebra.smul_def] at h2
  have h3 := congrArg T.eB h2
  simp only [map_sum, map_mul, map_one, mul_one, RingEquiv.apply_symm_apply] at h3
  have h4 : ∑ i, uB T (lam (t i)) * v₀ i = uB T (lam p) := h3
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h4, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
