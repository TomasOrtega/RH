import Formalism.GradedWeylDivisibility.StatementC

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

/- English proof (translation)
Introduce `R _ _ r n K sz hsz I hI`. Establish `hm : ∀ k ∈ (Finset.univ : Finset (Fin K)), (colLex r n).leadingCoeff (initMinor R (I k) (hsz k)) = 1` using `fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).2`. Establish `hreg : ∀ k ∈ (Finset.univ : Finset (Fin K)), IsRegular ((colLex r n).leadingCoeff (initMinor R (I k) (hsz k)))`. Introduce `k hk`. Rewrite using `[hm k hk]`.

Conclude with `isRegular_one`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `bideterminant bidetExp`. Rewrite using `[MonomialOrder.degree_prod_of_regular hreg]`. Conclude with `Finset.sum_congr rfl fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).1`.

Unfold `bideterminant`. Rewrite using `[MonomialOrder.leadingCoeff_prod_of_regular hreg]`. Conclude with `Finset.prod_eq_one hm`.
-/
theorem columnLexBideterminant_of_initialMinor (h : ColLexInitMinor) : ColumnLexBideterminant := by
  intro R _ _ r n K sz hsz I hI
  have hm : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      (colLex r n).leadingCoeff (initMinor R (I k) (hsz k)) = 1 :=
    fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).2
  have hreg : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      IsRegular ((colLex r n).leadingCoeff (initMinor R (I k) (hsz k))) := by
    intro k hk
    rw [hm k hk]
    exact isRegular_one
  refine ⟨?_, ?_⟩
  · unfold bideterminant bidetExp
    rw [MonomialOrder.degree_prod_of_regular hreg]
    exact Finset.sum_congr rfl fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).1
  · unfold bideterminant
    rw [MonomialOrder.leadingCoeff_prod_of_regular hreg]
    exact Finset.prod_eq_one hm

end Formalism.GradedWeylDivisibility
