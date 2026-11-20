import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Introduce `z hz`. Establish `hind : AlgebraicIndepOn ℚ id ({z} : Set ℂ)` using `by show AlgebraicIndependent ℚ _`. Conclude with `algebraicIndependent_unique_type_iff.2 hz`. Take `⟨t, hzt, ht⟩` from `exists_isTranscendenceBasis_superset hind`. Set `v : t → ℂ` to `(↑)`.

Set `i0 : t` to `⟨z, hzt rfl⟩`. Set `` to `IsAlgClosed.isAlgClosure_of_transcendence_basis v ht`. Set `f : t → MvPolynomial t ℚ` to `fun i => if i = i0 then -MvPolynomial.X i else MvPolynomial.X i`. Establish `hcomp : (MvPolynomial.aeval f).comp (MvPolynomial.aeval f) = AlgHom.id ℚ (MvPolynomial t ℚ)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `i`. Apply the tactic sequence `by_cases h : i = i0 <;> simp [f, h]`. Set `neg` to `AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f) hcomp hcomp`. Set `e : Algebra.adjoin ℚ (Set.range v) ≃+* Algebra.adjoin ℚ (Set.range v)` to `ht.1.aevalEquiv.symm.toRingEquiv.trans (neg.toRingEquiv.trans ht.1.aevalEquiv.toRingEquiv)`. Use `⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, ?_⟩` and prove the remaining obligations.

Establish `h1 : algebraMap (Algebra.adjoin ℚ (Set.range v)) ℂ (ht.1.aevalEquiv (MvPolynomial.X i0)) = z`. Rewrite using `[AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X]`. Establish `key : IsAlgClosure.equivOfEquiv ℂ ℂ e z = -z` using `by conv_lhs => rw [← h1]`. Rewrite using `[IsAlgClosure.equivOfEquiv_algebraMap]`. Simplify using `only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_apply]`.

Rewrite using `[AlgebraicIndependent.algebraMap_aevalEquiv]`. Simplify using `[neg, f, v, i0]`. Rewrite using `[key]`. Introduce `h`. Establish `h0 : z = 0` using `by linear_combination (-1 / 2 : ℂ) * h`.

Rewrite `hz` using `[h0]`. Conclude with `hz isAlgebraic_zero`.
-/
theorem exists_ringEquiv_ne_of_transcendental :
    ∀ z : ℂ, Transcendental ℚ z → ∃ σ : ℂ ≃+* ℂ, σ z ≠ z := by
  intro z hz
  have hind : AlgebraicIndepOn ℚ id ({z} : Set ℂ) := by
    show AlgebraicIndependent ℚ _
    exact algebraicIndependent_unique_type_iff.2 hz
  obtain ⟨t, hzt, ht⟩ := exists_isTranscendenceBasis_superset hind
  let v : t → ℂ := (↑)
  let i0 : t := ⟨z, hzt rfl⟩
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis v ht
  let f : t → MvPolynomial t ℚ := fun i => if i = i0 then -MvPolynomial.X i else MvPolynomial.X i
  have hcomp : (MvPolynomial.aeval f).comp (MvPolynomial.aeval f) =
      AlgHom.id ℚ (MvPolynomial t ℚ) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases h : i = i0 <;> simp [f, h]
  let neg := AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f) hcomp hcomp
  let e : Algebra.adjoin ℚ (Set.range v) ≃+* Algebra.adjoin ℚ (Set.range v) :=
    ht.1.aevalEquiv.symm.toRingEquiv.trans (neg.toRingEquiv.trans ht.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, ?_⟩
  have h1 : algebraMap (Algebra.adjoin ℚ (Set.range v)) ℂ (ht.1.aevalEquiv (MvPolynomial.X i0)) = z := by
    rw [AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  have key : IsAlgClosure.equivOfEquiv ℂ ℂ e z = -z := by
    conv_lhs => rw [← h1]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.symm_apply_apply]
    rw [AlgebraicIndependent.algebraMap_aevalEquiv]
    simp [neg, f, v, i0]
  rw [key]
  intro h
  have h0 : z = 0 := by linear_combination (-1 / 2 : ℂ) * h
  rw [h0] at hz
  exact hz isAlgebraic_zero

end GlobalTheory.ClassFin
