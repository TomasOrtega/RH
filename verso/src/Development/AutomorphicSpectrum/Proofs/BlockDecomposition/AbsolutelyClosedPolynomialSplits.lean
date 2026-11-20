import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.MonicSplit

open Polynomial

/- English proof (translation)
Break down `subsingleton_or_nontrivial S with hS' | hS'` into its components or cases. Introduce `P _ _`. Conclude with `⟨0, Subsingleton.elim _ _⟩`. Proceed by induction on `d with`. Consider the case `zero`.

Introduce `P hP hd`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.map_zero, Multiset.prod_zero]`. Conclude with `Polynomial.eq_one_of_monic_natDegree_zero hP hd`. Consider the case `succ d ih`.

Introduce `P hP hd`. Take `⟨x, hx⟩` from `hS P hP (by omega)`. Establish `hmul : (X - C x) * (P /ₘ (X - C x)) = P` using `Polynomial.mul_divByMonic_eq_iff_isRoot.2 hx`. Establish `hQ : (P /ₘ (X - C x)).Monic` using `Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C x) (by rw [hmul]; exact hP)`. Establish `hQd : (P /ₘ (X - C x)).natDegree = d`.

Establish `h` using `(Polynomial.monic_X_sub_C x).natDegree_mul hQ`. Rewrite `h` using `[hmul, Polynomial.natDegree_X_sub_C, hd]`. Use linear arithmetic over natural numbers and integers. Take `⟨s, hs⟩` from `ih _ hQ hQd`. Use `⟨x ::ₘ s, ?_⟩` and prove the remaining obligations.

Rewrite using `[Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]`.
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
Introduce `S _ hS P hP`. Conclude with `exists_multiset_of_natDegree_eq hS _ P hP rfl`.
-/
theorem monic_splits : ∀ {S : Type} [CommRing S], Aic S → ∀ P : Polynomial S, P.Monic →
    ∃ s : Multiset S, P = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro S _ hS P hP
  exact exists_multiset_of_natDegree_eq hS _ P hP rfl

end GlobalTheory.CompanionTheory.MonicSplit
