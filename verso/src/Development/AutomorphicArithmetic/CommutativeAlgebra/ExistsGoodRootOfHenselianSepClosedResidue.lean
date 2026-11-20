import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot

noncomputable section
open IsLocalRing UpperTheory.Et

open Polynomial in
/- English proof (translation)
Establish `hmon : ∀ a ∈ Finset.range q, (X - C (ζ ^ a) : A[X]).Monic` using `fun a _ => monic_X_sub_C _`. Establish `hdvd : (∏ a ∈ Finset.range q, (X - C (ζ ^ a))) ∣ (X ^ q - 1 : A[X])`. Use `Finset.prod_dvd_of_coprime ?_ ?_` and prove the remaining obligations. Introduce `i hi j hj hij`. Conclude with `isCoprime_X_sub_C_of_isUnit_sub (hu i hi j hj hij)`.

Introduce `a _`. Rewrite using `[dvd_iff_isRoot]`. Use `show eval (ζ ^ a) (X ^ q - 1 : A[X]) = 0`. Rewrite using `[eval_sub, eval_pow, eval_X, eval_one, ← pow_mul, mul_comm, pow_mul, h1, one_pow, sub_self]`. Establish `hm1 : (X ^ q - 1 : A[X]).Monic`.

Establish `h` using `monic_X_pow_sub_C (1 : A) hq`. Rewrite `h` using `[map_one]`. Then use the resulting hypothesis. Use `eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic _ _ hmon) hm1 hdvd ?_` and prove the remaining obligations. Rewrite using `[natDegree_prod_of_monic _ _ hmon]`. Simplify using `only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]`.

Rewrite using `[← map_one C, natDegree_X_pow_sub_C]`.
-/
private lemma split_of_units {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) (ζ : A) (hq : q ≠ 0) (h1 : ζ ^ q = 1)
    (hu : ∀ i ∈ Finset.range q, ∀ j ∈ Finset.range q, i ≠ j → IsUnit (ζ ^ i - ζ ^ j)) :
    (X ^ q - 1 : A[X]) = ∏ a ∈ Finset.range q, (X - C (ζ ^ a)) := by
  have hmon : ∀ a ∈ Finset.range q, (X - C (ζ ^ a) : A[X]).Monic := fun a _ => monic_X_sub_C _
  have hdvd : (∏ a ∈ Finset.range q, (X - C (ζ ^ a))) ∣ (X ^ q - 1 : A[X]) := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub (hu i hi j hj hij)
    · intro a _
      rw [dvd_iff_isRoot]
      show eval (ζ ^ a) (X ^ q - 1 : A[X]) = 0
      rw [eval_sub, eval_pow, eval_X, eval_one, ← pow_mul, mul_comm, pow_mul, h1, one_pow, sub_self]
  have hm1 : (X ^ q - 1 : A[X]).Monic := by
    have h := monic_X_pow_sub_C (1 : A) hq
    rwa [map_one] at h
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic _ _ hmon) hm1 hdvd ?_
  rw [natDegree_prod_of_monic _ _ hmon]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rw [← map_one C, natDegree_X_pow_sub_C]

/- English proof (translation)
Introduce `A _ _ _ q hqu`. Establish `hqk : ((q : ResidueField A)) ≠ 0`. Rewrite using `[← map_natCast (residue A)]`. Conclude with `(residue_ne_zero_iff_isUnit _).2 hqu`. Use `haveI : NeZero (q : ResidueField A) := ⟨hqk⟩`.

Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`. Conclude with `hqk (by simp)`. Use `haveI : NeZero q := ⟨hq0⟩`. Take `⟨z, hz⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField A) q`.

Take `⟨a0, rfl⟩` from `residue_surjective z`. Establish `ha0 : IsUnit a0` using `(residue_ne_zero_iff_isUnit _).1 (hz.ne_zero hq0)`. Establish `hmon : (Polynomial.X ^ q - 1 : Polynomial A).Monic`. Establish `h` using `Polynomial.monic_X_pow_sub_C (1 : A) hq0`. Rewrite `h` using `[map_one]`. Then use the resulting hypothesis.

Take `⟨ζ, hroot, hζ⟩` from `HenselianLocalRing.is_henselian (Polynomial.X ^ q - 1 : Polynomial A) hmon a0 (by`. Rewrite using `[← residue_eq_zero_iff]`. Simplify using `[hz.pow_eq_one])`. Use the proof step `(by`. Simplify using `only [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero, Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X]`.

Conclude with `hqu.mul (ha0.pow _))`. Establish `hζq : ζ ^ q = 1`. Establish `h` using `hroot.eq_zero`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at h`. Conclude with `sub_eq_zero.1 h`.

Establish `hres : residue A ζ = residue A a0`. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`. Conclude with `hζ`. Establish `hunits : ∀ i < q, ∀ j < q, i ≠ j → IsUnit (ζ ^ i - ζ ^ j)`. Introduce `i hi j hj hij`.

Rewrite using `[← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_pow, hres]`. Introduce `h`. Conclude with `hij (hz.pow_inj hi hj (sub_eq_zero.1 h))`. Use `⟨ζ, hζq, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`.

Conclude with `hunits a.val (ZMod.val_lt a) b.val (ZMod.val_lt b) (fun h => hab (ZMod.val_injective q h))`. Introduce `S' _ φ x`. Establish `key` using `split_of_units q ζ hq0 hζq (fun i hi j hj hij => hunits i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij)`. Establish `h` using `congrArg (Polynomial.eval₂ φ x) key`. Simplify `h` using `[Polynomial.eval₂_finset_prod, Polynomial.eval₂_pow, Polynomial.eval₂_C]`.
-/
theorem UpperTheory.exists_goodRoot_of_henselian_sepClosed_residue :
    ∀ (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)] (q : ℕ), IsUnit (q : A) → ∃ ζ : A, GoodRoot q ζ := by
  intro A _ _ _ q hqu
  have hqk : ((q : ResidueField A)) ≠ 0 := by
    rw [← map_natCast (residue A)]
    exact (residue_ne_zero_iff_isUnit _).2 hqu
  haveI : NeZero (q : ResidueField A) := ⟨hqk⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hqk (by simp)
  haveI : NeZero q := ⟨hq0⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField A) q
  obtain ⟨a0, rfl⟩ := residue_surjective z
  have ha0 : IsUnit a0 := (residue_ne_zero_iff_isUnit _).1 (hz.ne_zero hq0)
  have hmon : (Polynomial.X ^ q - 1 : Polynomial A).Monic := by
    have h := Polynomial.monic_X_pow_sub_C (1 : A) hq0
    rwa [map_one] at h
  obtain ⟨ζ, hroot, hζ⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ q - 1 : Polynomial A) hmon a0
    (by
      rw [← residue_eq_zero_iff]
      simp [hz.pow_eq_one])
    (by
      simp only [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
        Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_natCast,
        Polynomial.eval_pow, Polynomial.eval_X]
      exact hqu.mul (ha0.pow _))
  have hζq : ζ ^ q = 1 := by
    have h := hroot.eq_zero
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at h
    exact sub_eq_zero.1 h
  have hres : residue A ζ = residue A a0 := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hζ
  have hunits : ∀ i < q, ∀ j < q, i ≠ j → IsUnit (ζ ^ i - ζ ^ j) := by
    intro i hi j hj hij
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_pow, hres]
    intro h
    exact hij (hz.pow_inj hi hj (sub_eq_zero.1 h))
  refine ⟨ζ, hζq, ?_, ?_⟩
  · intro a b hab
    exact hunits a.val (ZMod.val_lt a) b.val (ZMod.val_lt b) (fun h => hab (ZMod.val_injective q h))
  · intro S' _ φ x
    have key := split_of_units q ζ hq0 hζq
      (fun i hi j hj hij => hunits i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij)
    have h := congrArg (Polynomial.eval₂ φ x) key
    simpa [Polynomial.eval₂_finset_prod, Polynomial.eval₂_pow, Polynomial.eval₂_C] using h

end
