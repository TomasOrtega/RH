import Mathlib

namespace GlobalTheory.SepPoint

noncomputable def adjoinEquiv (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    MvPolynomial s k ≃ₐ[k] Algebra.adjoin k (s : Set F) :=
  hs.aevalEquiv.trans (Subalgebra.equivOfEq _ _ (by rw [Subtype.range_coe]))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isIntegrallyClosed_adjoin (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := by
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k (s : Set F)) :=
    (adjoinEquiv k F s hs).toMulEquiv.uniqueFactorizationMonoid inferInstance
  infer_instance

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem infinite_of_isSepClosed (Ω : Type) [Field Ω] [IsSepClosed Ω] : Infinite Ω := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  haveI : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  exact h.false.elim

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem exists_ev (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) (H : Algebra.adjoin k (s : Set F)) (hH : H ≠ 0) :
    ∃ ev : Algebra.adjoin k (s : Set F) →ₐ[k] SeparableClosure k, ev H ≠ 0 := by
  haveI := infinite_of_isSepClosed (SeparableClosure k)
  let e := adjoinEquiv k F s hs
  have hP : e.symm H ≠ 0 := by simpa using hH
  obtain ⟨a, ha⟩ : ∃ a : s → SeparableClosure k,
      MvPolynomial.eval a ((e.symm H).map (algebraMap k (SeparableClosure k))) ≠ 0 := by
    by_contra! h
    apply hP
    have := MvPolynomial.funext (p := (e.symm H).map (algebraMap k (SeparableClosure k)))
      (q := 0) (fun x => by simp [h x])
    exact MvPolynomial.map_injective _ (algebraMap k (SeparableClosure k)).injective
      (by simpa using this)
  refine ⟨(MvPolynomial.aeval a).comp e.symm.toAlgHom, ?_⟩
  simpa [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval_map] using ha

end GlobalTheory.SepPoint
