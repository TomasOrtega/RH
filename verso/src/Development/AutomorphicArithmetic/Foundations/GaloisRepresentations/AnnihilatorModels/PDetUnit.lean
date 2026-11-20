import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `S _ a v hv`. Establish `hmem : ∀ i : Fin a, ∃ c : Fin a → S, ∑ k, c k • v k = Pi.single i 1` using `fun i => by`. Establish `h : (Pi.single i 1 : Fin a → S) ∈ Submodule.span S (Set.range v)`. Rewrite using `[hv]`. Discharge the goal by the elementary cases of `trivial`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun S).1 h`. Use `choose c hc using hmem`. Establish `hQN : (Matrix.of fun i k => v k i) * (Matrix.of fun k i => c i k) = (1 : Matrix (Fin a) (Fin a) S)`. Use extensionality with `i j`. Establish `h` using `congrFun (hc j) i`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.of_apply]`. Simplify using `only [mul_comm (v _ i)]`. Rewrite using `[h, Pi.single_apply]`.

Conclude with `Matrix.isUnit_det_of_right_inverse hQN`.
-/
theorem UpperTheory.Gal.crystallineComparison.detUnit_of :
    UnitOfSpan := by
  intro S _ a v hv
  have hmem : ∀ i : Fin a, ∃ c : Fin a → S, ∑ k, c k • v k = Pi.single i 1 := fun i => by
    have h : (Pi.single i 1 : Fin a → S) ∈ Submodule.span S (Set.range v) := by
      rw [hv]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun S).1 h
  choose c hc using hmem
  have hQN : (Matrix.of fun i k => v k i) * (Matrix.of fun k i => c i k) =
      (1 : Matrix (Fin a) (Fin a) S) := by
    ext i j
    have h := congrFun (hc j) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    simp only [mul_comm (v _ i)]
    rw [h, Pi.single_apply]
  exact Matrix.isUnit_det_of_right_inverse hQN
