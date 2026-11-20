import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedPolynomialSplitsStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.UnitRoot

open Polynomial

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => intro k hk`. Simplify using `at hk`. Consider the case `cons a s ih`. Introduce `k hk`.

Establish `ha : a ∈ m` using `h a (Multiset.mem_cons_self a s)`. Establish `ih'` using `ih fun b hb => h b (Multiset.mem_cons_of_mem hb)`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, sub_mul]`. Rewrite `hk` using `[Multiset.card_cons]`. Consider the cases of `k with`.

Consider the case `zero`. Simplify using `only [coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]`. Conclude with `m.neg_mem (m.mul_mem_right _ ha)`. Consider the case `succ k`. Simplify using `only [coeff_sub, coeff_X_mul, coeff_C_mul]`.

Conclude with `m.sub_mem (ih' k (by omega)) (m.mul_mem_right _ ha)`.
-/
theorem coeff_prod_mem {S : Type} [CommRing S] (m : Ideal S) (s : Multiset S)
    (h : ∀ b ∈ s, b ∈ m) :
    ∀ k < Multiset.card s, ((s.map fun b => (X : S[X]) - C b).prod).coeff k ∈ m := by
  induction s using Multiset.induction_on with
  | empty => intro k hk; simp at hk
  | cons a s ih =>
    intro k hk
    have ha : a ∈ m := h a (Multiset.mem_cons_self a s)
    have ih' := ih fun b hb => h b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.map_cons, Multiset.prod_cons, sub_mul]
    rw [Multiset.card_cons] at hk
    cases k with
    | zero =>
      simp only [coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]
      exact m.neg_mem (m.mul_mem_right _ ha)
    | succ k =>
      simp only [coeff_sub, coeff_X_mul, coeff_C_mul]
      exact m.sub_mem (ih' k (by omega)) (m.mul_mem_right _ ha)

/- English proof (translation)
Introduce `S _ hA hL Q i h0 hi hu`. Break down `subsingleton_or_nontrivial S with hs | hn` into its components or cases. Conclude with `⟨0, Subsingleton.elim _ _⟩`. Use `haveI : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add hL`. Establish `htd : Q.natTrailingDegree = 0` using `Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [h0]; exact one_ne_zero))`.

Establish `hmon : Q.reverse.Monic`. Rewrite using `[Monic, reverse_leadingCoeff, trailingCoeff, htd, h0]`. Establish `hdeg : Q.reverse.natDegree = Q.natDegree`. Rewrite using `[reverse_natDegree, htd]`. Both sides reduce to the same expression.

Establish `hid : i ≤ Q.natDegree` using `le_natDegree_of_ne_zero hu.ne_zero`. Take `⟨s, hs⟩` from `GlobalTheory.T.absolutely_closed_polynomial_splits hA _ hmon`. Establish `hcard : Multiset.card s = Q.natDegree`. Rewrite using `[← hdeg, hs, natDegree_multiset_prod_X_sub_C_eq_card]`. Establish `hcoeff : Q.reverse.coeff (Q.natDegree - i) = Q.coeff i`.

Rewrite using `[coeff_reverse, revAt_le (Nat.sub_le _ _)]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hex : ∃ b ∈ s, IsUnit b`. Take `⟨b, hbs, hb⟩` from `hex`.

Establish `hroot : Q.reverse.eval b = 0`. Establish `hdvd : (X : S[X]) - C b ∣ Q.reverse`. Rewrite using `[hs]`. Conclude with `Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)`. Conclude with `dvd_iff_isRoot.mp hdvd`.

Take `⟨u, rfl⟩` from `hb`. Use `⟨((u⁻¹ : Sˣ) : S), ?_⟩` and prove the remaining obligations. Use `letI : Invertible ((u⁻¹ : Sˣ) : S) := (u⁻¹).invertible`. Establish `key` using `eval₂_reverse_mul_pow (RingHom.id S) ((u⁻¹ : Sˣ) : S) Q`. Establish `hinv : ⅟((u⁻¹ : Sˣ) : S) = (u : S)` using `by simp`.

Rewrite `key` using `[hinv, eval₂_id, eval₂_id, hroot, zero_mul]`. Conclude with `key.symm`. It suffices to derive a contradiction. Establish `hall : ∀ b ∈ s, b ∈ IsLocalRing.maximalIdeal S` using `fun b hb => (IsLocalRing.mem_maximalIdeal b).mpr fun hbu => hex ⟨b, hb, hbu⟩`. Establish `hmem` using `coeff_prod_mem (IsLocalRing.maximalIdeal S) s hall (Q.natDegree - i) (by omega)`.

Rewrite `hmem` using `[← hs, hcoeff]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hmem hu`.
-/
theorem exists_root : ∀ {S : Type} [CommRing S] , Aic S →
    (∀ a b : S, IsUnit (a + b) → IsUnit a ∨ IsUnit b) →
    ∀ (Q : Polynomial S) (i : ℕ), Q.coeff 0 = 1 → 0 < i → IsUnit (Q.coeff i) →
      ∃ y, Q.eval y = 0 := by
  intro S _ hA hL Q i h0 hi hu
  rcases subsingleton_or_nontrivial S with hs | hn
  · exact ⟨0, Subsingleton.elim _ _⟩
  haveI : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add hL
  have htd : Q.natTrailingDegree = 0 :=
    Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [h0]; exact one_ne_zero))
  have hmon : Q.reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, h0]
  have hdeg : Q.reverse.natDegree = Q.natDegree := by
    rw [reverse_natDegree, htd]; rfl
  have hid : i ≤ Q.natDegree := le_natDegree_of_ne_zero hu.ne_zero
  obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA _ hmon
  have hcard : Multiset.card s = Q.natDegree := by
    rw [← hdeg, hs, natDegree_multiset_prod_X_sub_C_eq_card]
  have hcoeff : Q.reverse.coeff (Q.natDegree - i) = Q.coeff i := by
    rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
    congr 1
    omega
  by_cases hex : ∃ b ∈ s, IsUnit b
  · obtain ⟨b, hbs, hb⟩ := hex
    have hroot : Q.reverse.eval b = 0 := by
      have hdvd : (X : S[X]) - C b ∣ Q.reverse := by
        rw [hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
      exact dvd_iff_isRoot.mp hdvd
    obtain ⟨u, rfl⟩ := hb
    refine ⟨((u⁻¹ : Sˣ) : S), ?_⟩
    letI : Invertible ((u⁻¹ : Sˣ) : S) := (u⁻¹).invertible
    have key := eval₂_reverse_mul_pow (RingHom.id S) ((u⁻¹ : Sˣ) : S) Q
    have hinv : ⅟((u⁻¹ : Sˣ) : S) = (u : S) := by simp
    rw [hinv, eval₂_id, eval₂_id, hroot, zero_mul] at key
    exact key.symm
  · exfalso
    have hall : ∀ b ∈ s, b ∈ IsLocalRing.maximalIdeal S := fun b hb =>
      (IsLocalRing.mem_maximalIdeal b).mpr fun hbu => hex ⟨b, hb, hbu⟩
    have hmem := coeff_prod_mem (IsLocalRing.maximalIdeal S) s hall (Q.natDegree - i)
      (by omega)
    rw [← hs, hcoeff] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu

end GlobalTheory.CompanionTheory.UnitRoot
