import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf

open NumberField GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.TotallyComplexOfOdd

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure.

Establish an intermediate fact. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem isTotallyComplex_of_odd (L' L : FiniteSubfield) [Fact (L' ≤ L)]
    (hodd : Odd (Module.finrank L'.1 L.1)) (htc : NumberField.IsTotallyComplex L.1) :
    NumberField.IsTotallyComplex L'.1 := by
  refine ⟨fun v => ?_⟩
  by_contra hv
  have hvr : v.IsReal := InfinitePlace.not_isComplex_iff_isReal.1 hv
  have hσ : ComplexEmbedding.IsReal v.embedding := InfinitePlace.isReal_iff.1 hvr
  letI : Algebra L'.1 ℂ := v.embedding.toAlgebra
  haveI : FiniteDimensional L'.1 L.1 := Module.Finite.of_restrictScalars_finite ℚ L'.1 L.1
  have hreal : ∀ x : L'.1, starRingEnd ℂ (v.embedding x) = v.embedding x := fun x =>
    (ComplexEmbedding.conjugate_coe_eq _ x).symm.trans
      (RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hσ) x)
  let c : (L.1 →ₐ[L'.1] ℂ) → (L.1 →ₐ[L'.1] ℂ) := fun τ =>
    { ((starRingEnd ℂ).comp τ.toRingHom) with
      commutes' := fun x => by
        show starRingEnd ℂ (τ (algebraMap L'.1 L.1 x)) = algebraMap L'.1 ℂ x
        rw [τ.commutes]
        exact hreal x }
  have hinv : Function.Involutive c := fun τ => by
    ext x
    show starRingEnd ℂ (starRingEnd ℂ (τ x)) = τ x
    simp
  have hcard : Fintype.card (L.1 →ₐ[L'.1] ℂ) = Module.finrank L'.1 L.1 := AlgHom.card L'.1 L.1 ℂ
  obtain ⟨τ, hτ⟩ : ∃ τ, c τ = τ := by
    by_contra hno
    push Not at hno
    have hev : Even (Fintype.card (L.1 →ₐ[L'.1] ℂ)) := by
      classical
      let σ : Equiv.Perm (L.1 →ₐ[L'.1] ℂ) := Function.Involutive.toPerm c hinv
      have hσ2 : σ ^ 2 = 1 := by
        ext1 τ
        show c (c τ) = τ
        exact hinv τ
      have hsupp : σ.support = Finset.univ :=
        Finset.eq_univ_iff_forall.2 fun τ => Equiv.Perm.mem_support.2 (hno τ)
      have h2 := Equiv.Perm.two_dvd_card_support hσ2
      rw [hsupp, Finset.card_univ] at h2
      exact even_iff_two_dvd.2 h2
    rw [hcard] at hev
    exact (Nat.not_even_iff_odd.2 hodd) hev
  have hτr : ComplexEmbedding.IsReal τ.toRingHom := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact congrArg (fun f : L.1 →ₐ[L'.1] ℂ => f x) hτ
  have := htc.isComplex (InfinitePlace.mk τ.toRingHom)
  exact InfinitePlace.not_isComplex_iff_isReal.2 ⟨τ.toRingHom, hτr, rfl⟩ this

end PositivityTheory.Lit1.GEN.TotallyComplexOfOdd
