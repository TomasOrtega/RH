import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `ι _ _ R _ s n v hv`. Rewrite using `[linearIndependent_iff']`. Introduce `T g hg j hj`. Set `k : ℕ` to `T.sup fun a => Finset.univ.sup fun i => (a.1 i).natAbs`. Set `m : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} → (ι →₀ ℕ)` to `fun a => Finsupp.equivFunOnFinite.symm fun i => (a.1 i + if i ∈ s then (k : ℤ) else 0).toNat`.

Establish `hm : ∀ a ∈ T, ∀ i, (m a i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0`. Introduce `a ha i`. Establish `hk : (a.1 i).natAbs ≤ k` using `(Finset.le_sup (f := fun i => (a.1 i).natAbs) (Finset.mem_univ i)).trans (Finset.le_sup (f := fun a : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} => Finset.univ.sup fun i => (a.1 i).natAbs) ha)`. Use `Int.toNat_of_nonneg ?_` and prove the remaining obligations. Use `split_ifs with hi`.

Use linear arithmetic over natural numbers and integers. Simplify using `using a.2.2 i hi`. Establish `hinj : ∀ a ∈ T, m a = m j → a = j`. Introduce `a ha e`. Use `Subtype.ext (funext fun i => ?_)` and prove the remaining obligations.

Establish `h1` using `hm a ha i`. Establish `h2` using `hm j hj i`. Rewrite `h1` using `[e, h2]`. Conclude with `(add_right_cancel h1).symm`. Establish `h0 : awayFrac (MvPolynomial ι R) (xProd R s) k (∑ a ∈ T, g a • monomial (m a) (1 : R)) = 0`.

Rewrite using `[map_sum, ← hg]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[hv a k (m a) (hm a ha), LinearMap.map_smul_of_tower]`. Establish `h1` using `congrArg (coeff (m j)) ((map_eq_zero_iff _ (awayFrac_injective (xProd_smul_injective s) k)).1 h0)`. Rewrite `h1` using `[coeff_sum, Finset.sum_eq_single j, coeff_smul, coeff_monomial, if_pos rfl, coeff_zero, smul_eq_mul, mul_one]`.

Conclude with `h1`. Introduce `a ha hne`. Rewrite using `[coeff_smul, coeff_monomial, if_neg fun e => hne (hinj a ha e), smul_zero]`. Conclude with `fun h => absurd hj h`.
-/
theorem linearIndependent_laurentMonomial :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (s : Finset ι) (n : ℤ) (v : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} → LocalizedModule.Away (xProd R s) (MvPolynomial ι R)), (∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0) → v a = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1)) → LinearIndependent R v := by
  intro ι _ _ R _ s n v hv
  rw [linearIndependent_iff']
  intro T g hg j hj
  let k : ℕ := T.sup fun a => Finset.univ.sup fun i => (a.1 i).natAbs
  let m : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} → (ι →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm fun i => (a.1 i + if i ∈ s then (k : ℤ) else 0).toNat
  have hm : ∀ a ∈ T, ∀ i, (m a i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0 := by
    intro a ha i
    have hk : (a.1 i).natAbs ≤ k :=
      (Finset.le_sup (f := fun i => (a.1 i).natAbs) (Finset.mem_univ i)).trans
        (Finset.le_sup (f := fun a : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} =>
          Finset.univ.sup fun i => (a.1 i).natAbs) ha)
    refine Int.toNat_of_nonneg ?_
    split_ifs with hi
    · omega
    · simpa using a.2.2 i hi
  have hinj : ∀ a ∈ T, m a = m j → a = j := by
    intro a ha e
    refine Subtype.ext (funext fun i => ?_)
    have h1 := hm a ha i
    have h2 := hm j hj i
    rw [e, h2] at h1
    exact (add_right_cancel h1).symm
  have h0 : awayFrac (MvPolynomial ι R) (xProd R s) k
      (∑ a ∈ T, g a • monomial (m a) (1 : R)) = 0 := by
    rw [map_sum, ← hg]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hv a k (m a) (hm a ha), LinearMap.map_smul_of_tower]
  have h1 := congrArg (coeff (m j))
    ((map_eq_zero_iff _ (awayFrac_injective (xProd_smul_injective s) k)).1 h0)
  rw [coeff_sum, Finset.sum_eq_single j, coeff_smul, coeff_monomial, if_pos rfl, coeff_zero,
    smul_eq_mul, mul_one] at h1
  · exact h1
  · intro a ha hne
    rw [coeff_smul, coeff_monomial, if_neg fun e => hne (hinj a ha e), smul_zero]
  · exact fun h => absurd hj h

end GlobalTheory
