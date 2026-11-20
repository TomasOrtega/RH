import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries

noncomputable section

namespace GlobalTheory.MonomialRangeMembership

open MvPolynomial

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem monomial_mem_range_glue {D : Formalism.BasicNotions.D7} {a b : ℕ}
    (m : Formalism.IndefR.Datum.FVar D b a →₀ ℕ) :
    (monomial m (1 : ℂ) : Formalism.IndefR.Links.PolF D b a) ∈
      Set.range (GlobalTheory.Chain.RealIt.glue (D := D) (a := a) (b := b)) := by
  refine ⟨fun τ => ∏ s : Fin b × Fin a, X s ^ m (τ, s), ?_⟩
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  unfold GlobalTheory.Chain.RealIt.glue
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [map_prod, map_pow, rename_X]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem span_range_glue : ∀ {D : Formalism.BasicNotions.D7} {a b : Nat}, @Eq (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.span Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing) (@Set.range (Formalism.IndefR.Links.PolF D b a) (@Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.what₂ D) → GlobalTheory.Chain.RealIt.LPol b a) (@GlobalTheory.Chain.RealIt.glue D a b))) (@Top.top (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.instTop Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing))) := by
  intro D a b
  rw [eq_top_iff, ← (basisMonomials (Formalism.IndefR.Datum.FVar D b a) ℂ).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  rw [coe_basisMonomials]
  exact monomial_mem_range_glue m

end GlobalTheory.MonomialRangeMembership
