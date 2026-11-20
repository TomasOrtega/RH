import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.MonicSplit

open Polynomial

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Proceed by induction. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_multiset_of_natDegree_eq {S : Type} [CommRing S] (hS : Aic S) (d : ℕ) :
    ∀ P : Polynomial S, P.Monic → P.natDegree = d →
      ∃ s : Multiset S, P = (s.map fun b => X - C b).prod := by
  rcases subsingleton_or_nontrivial S with hS' | hS'
  · intro P _ _
    exact ⟨0, Subsingleton.elim _ _⟩
  · induction d with
    | zero =>
      intro P hP hd
      refine ⟨0, ?_⟩
      rw [Multiset.map_zero, Multiset.prod_zero]
      exact Polynomial.eq_one_of_monic_natDegree_zero hP hd
    | succ d ih =>
      intro P hP hd
      obtain ⟨x, hx⟩ := hS P hP (by omega)
      have hmul : (X - C x) * (P /ₘ (X - C x)) = P := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hx
      have hQ : (P /ₘ (X - C x)).Monic :=
        Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C x) (by rw [hmul]; exact hP)
      have hQd : (P /ₘ (X - C x)).natDegree = d := by
        have h := (Polynomial.monic_X_sub_C x).natDegree_mul hQ
        rw [hmul, Polynomial.natDegree_X_sub_C, hd] at h
        omega
      obtain ⟨s, hs⟩ := ih _ hQ hQd
      refine ⟨x ::ₘ s, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem monic_splits : ∀ {S : Type} [CommRing S], Aic S → ∀ P : Polynomial S, P.Monic →
    ∃ s : Multiset S, P = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro S _ hS P hP
  exact exists_multiset_of_natDegree_eq hS _ P hP rfl

end GlobalTheory.CompanionTheory.MonicSplit
