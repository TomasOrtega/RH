import Mathlib

namespace GlobalTheory.SepPoint

noncomputable def adjoinEquiv (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    MvPolynomial s k ≃ₐ[k] Algebra.adjoin k (s : Set F) :=
  hs.aevalEquiv.trans (Subalgebra.equivOfEq _ _ (by rw [Subtype.range_coe]))

/- English proof (translation)
Use `haveI : UniqueFactorizationMonoid (Algebra.adjoin k (s : Set F)) := (adjoinEquiv k F s hs).toMulEquiv.uniqueFactorizationMonoid inferInstance`. Use `infer_instance`.
-/
theorem isIntegrallyClosed_adjoin (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := by
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k (s : Set F)) :=
    (adjoinEquiv k F s hs).toMulEquiv.uniqueFactorizationMonoid inferInstance
  infer_instance

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_infinite_iff_finite]`. Use `haveI : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω`. Conclude with `h.false.elim`.
-/
theorem infinite_of_isSepClosed (Ω : Type) [Field Ω] [IsSepClosed Ω] : Infinite Ω := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  haveI : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  exact h.false.elim

/- English proof (translation)
Use `haveI := infinite_of_isSepClosed (SeparableClosure k)`. Set `e` to `adjoinEquiv k F s hs`. Establish `hP : e.symm H ≠ 0` using `by simpa using hH`. Take `⟨a, ha⟩ : ∃ a : s → SeparableClosure k, MvPolynomial.eval a ((e.symm H).map (algebraMap k (SeparableClosure k))) ≠ 0` from `by by_contra! h`. Apply `hP` to reduce the goal to its premises.

Use `MvPolynomial.funext (p := (e.symm H).map (algebraMap k (SeparableClosure k))) (q := 0) (fun x => by simp [h x])` as an intermediate fact. Conclude with `MvPolynomial.map_injective _ (algebraMap k (SeparableClosure k)).injective (by simpa using this)`. Use `⟨(MvPolynomial.aeval a).comp e.symm.toAlgHom, ?_⟩` and prove the remaining obligations. Simplify `ha` using `[MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval_map]`.
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
