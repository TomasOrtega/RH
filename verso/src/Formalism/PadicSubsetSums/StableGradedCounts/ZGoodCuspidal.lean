import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

/- English proof (translation)
Introduce `k _ P _ r f I _ n d h hdeg hsq hprod hhdeg hn hd hno`. Take `⟨v0⟩` from `‹Nonempty P›`. Establish `hdvd : ∀ v i, h v i ∣ f v`. Introduce `v i`. Rewrite using `[hprod v]`.

Conclude with `(dvd_pow_self (h v i) (by have := hd i; omega)).trans (Finset.dvd_prod_of_mem (fun j => h v j ^ d j) (Finset.mem_univ i))`. Establish `hd1 : ∀ i, d i = 1`. Introduce `i`. Assume the negation of the conclusion as `hne`. Establish `h2 : 2 ≤ d i` using `by have := hd i; omega`.

Establish `hsq' : h v0 i * h v0 i ∣ f v0`. Rewrite using `[hprod v0]`. Use `(?_ : h v0 i * h v0 i ∣ h v0 i ^ d i).trans (Finset.dvd_prod_of_mem (fun j => h v0 j ^ d j) (Finset.mem_univ i))` and prove the remaining obligations. Rewrite using `[← pow_two]`. Conclude with `pow_dvd_pow _ h2`.

Establish `hu` using `hsq v0 _ hsq'`. Establish `e1` using `Polynomial.natDegree_eq_zero_of_isUnit hu`. Establish `e2` using `hhdeg v0 i`. Establish `e3` using `hn i`. Use linear arithmetic over natural numbers and integers.

Use `⟨hd1, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcard`. Use `push_neg at hcard`. Use `haveI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp hcard`. Take `⟨i, j, hij⟩` from `exists_pair_ne I`.

Establish `hf0 : f v0 ≠ 0` using `(hsq v0).ne_zero`. Establish `hne : ∀ l, h v0 l ≠ 0`. Introduce `l hl`. Use `hdvd v0 l` as an intermediate fact. Rewrite `this` using `[hl, zero_dvd_iff]`.

Conclude with `hf0 this`. Establish `hr : r = ∑ l, n l`. Rewrite using `[← hdeg v0, hprod v0, Polynomial.natDegree_prod _ _ (fun l _ => pow_ne_zero _ (hne l))]`. Simplify using `[Polynomial.natDegree_pow, hd1, hhdeg]`. Establish `hle : n i + n j ≤ ∑ l, n l` using `by classical`.

Rewrite using `[← Finset.sum_pair hij]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`. Break down `le_total (n i) (n j) with hij' | hji'` into its components or cases. Conclude with `hno ⟨n i, hn i, by omega, fun v => ⟨h v i, hdvd v i, hhdeg v i⟩⟩`. Conclude with `hno ⟨n j, hn j, by omega, fun v => ⟨h v j, hdvd v j, hhdeg v j⟩⟩`.
-/
theorem goodCuspidal_holds : GoodCuspidal := by
  intro k _ P _ r f I _ n d h hdeg hsq hprod hhdeg hn hd hno
  obtain ⟨v0⟩ := ‹Nonempty P›

  have hdvd : ∀ v i, h v i ∣ f v := by
    intro v i
    rw [hprod v]
    exact (dvd_pow_self (h v i) (by have := hd i; omega)).trans
      (Finset.dvd_prod_of_mem (fun j => h v j ^ d j) (Finset.mem_univ i))

  have hd1 : ∀ i, d i = 1 := by
    intro i
    by_contra hne
    have h2 : 2 ≤ d i := by have := hd i; omega
    have hsq' : h v0 i * h v0 i ∣ f v0 := by
      rw [hprod v0]
      refine (?_ : h v0 i * h v0 i ∣ h v0 i ^ d i).trans
        (Finset.dvd_prod_of_mem (fun j => h v0 j ^ d j) (Finset.mem_univ i))
      rw [← pow_two]
      exact pow_dvd_pow _ h2
    have hu := hsq v0 _ hsq'
    have e1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have e2 := hhdeg v0 i
    have e3 := hn i
    omega
  refine ⟨hd1, ?_⟩
  by_contra hcard
  push_neg at hcard
  haveI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  have hf0 : f v0 ≠ 0 := (hsq v0).ne_zero
  have hne : ∀ l, h v0 l ≠ 0 := by
    intro l hl
    have := hdvd v0 l
    rw [hl, zero_dvd_iff] at this
    exact hf0 this

  have hr : r = ∑ l, n l := by
    rw [← hdeg v0, hprod v0, Polynomial.natDegree_prod _ _ (fun l _ => pow_ne_zero _ (hne l))]
    simp [Polynomial.natDegree_pow, hd1, hhdeg]
  have hle : n i + n j ≤ ∑ l, n l := by
    classical
    rw [← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rcases le_total (n i) (n j) with hij' | hji'
  · exact hno ⟨n i, hn i, by omega, fun v => ⟨h v i, hdvd v i, hhdeg v i⟩⟩
  · exact hno ⟨n j, hn j, by omega, fun v => ⟨h v j, hdvd v j, hhdeg v j⟩⟩

end Formalism.IrreducibleCountingLemmas.Z
