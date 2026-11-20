import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.BridgeDefs

namespace KStar.Ram

open NumberField

/- English proof (translation)
Rewrite using `[← charpoly_leftMulMatrix, Matrix.eval_charpoly, Algebra.norm_eq_matrix_det pb.basis, map_sub, map_one, map_one]`.
-/
private theorem rootNorm_powerBasis {F : Type*} [Field F] [Algebra ℚ F] (pb : PowerBasis ℚ F) :
    Algebra.norm ℚ (1 - pb.gen) = (minpoly ℚ pb.gen).eval 1 := by
  classical
  rw [← charpoly_leftMulMatrix, Matrix.eval_charpoly, Algebra.norm_eq_matrix_det pb.basis,
    map_sub, map_one, map_one]

/- English proof (translation)
Establish `hx : IsIntegral ℚ x` using `.of_finite ℚ x`. Use `⟨Module.finrank (IntermediateField.adjoin ℚ {x}) K, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← IntermediateField.adjoin.finrank hx, Module.finrank_mul_finrank]`. Establish `h1 : (1 - x : K) = algebraMap (IntermediateField.adjoin ℚ {x}) K (1 - IntermediateField.AdjoinSimple.gen ℚ x)`. Simplify using the standard rewrite rules.

Establish `h2` using `rootNorm_powerBasis (IntermediateField.adjoin.powerBasis hx)`. Rewrite `h2` using `[IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]`. Rewrite using `[h1, ← Algebra.norm_norm (S := IntermediateField.adjoin ℚ {x}), Algebra.norm_algebraMap, map_pow]`. Conclude with `congrArg (· ^ Module.finrank (IntermediateField.adjoin ℚ {x}) K) h2`.
-/
private theorem rootNorm_field {K : Type*} [Field K] [NumberField K] (x : K) :
    ∃ k : ℕ, Module.finrank ℚ K = (minpoly ℚ x).natDegree * k ∧
      Algebra.norm ℚ (1 - x) = ((minpoly ℚ x).eval 1) ^ k := by
  have hx : IsIntegral ℚ x := .of_finite ℚ x
  refine ⟨Module.finrank (IntermediateField.adjoin ℚ {x}) K, ?_, ?_⟩
  · rw [← IntermediateField.adjoin.finrank hx, Module.finrank_mul_finrank]
  · have h1 : (1 - x : K) = algebraMap (IntermediateField.adjoin ℚ {x}) K
        (1 - IntermediateField.AdjoinSimple.gen ℚ x) := by
      simp
    have h2 := rootNorm_powerBasis (IntermediateField.adjoin.powerBasis hx)
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h2
    rw [h1, ← Algebra.norm_norm (S := IntermediateField.adjoin ℚ {x}), Algebra.norm_algebraMap, map_pow]
    exact congrArg (· ^ Module.finrank (IntermediateField.adjoin ℚ {x}) K) h2

/- English proof (translation)
Use `haveI : NeZero m := ⟨by omega⟩`. Establish `hηK : IsPrimitiveRoot (η : K) m` using `hη.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)`. Take `⟨k, hk, hnorm⟩` from `rootNorm_field (η : K)`. Rewrite `hk` using `[← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega), Polynomial.natDegree_cyclotomic]`. Rewrite `hnorm` using `[← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega)]`.

Establish `hcQ : (Polynomial.cyclotomic m ℚ).eval 1 = (((Polynomial.cyclotomic m ℤ).eval 1 : ℤ) : ℚ)`. Rewrite using `[← Polynomial.map_cyclotomic_int, ← Int.cast_one, Polynomial.eval_intCast_map, eq_intCast, Int.cast_one]`. Establish `hnormZ : Algebra.norm ℤ (1 - η) = ((Polynomial.cyclotomic m ℤ).eval 1) ^ k`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Rewrite using `[Algebra.coe_norm_int, Int.cast_pow, ← hcQ, ← hnorm]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hv : (padicValNat l ((Polynomial.cyclotomic m ℤ).eval 1).natAbs : ℚ) = m.totient * rootWeight l m`. Distinguish the cases in `hpp : ∃ p j, p.Prime ∧ m = p ^ (j + 1)`. Take `⟨p, j, hp, rfl⟩` from `hpp haveI := Fact.mk hp`.

Rewrite using `[Polynomial.eval_one_cyclotomic_prime_pow, Int.natAbs_natCast]`. Establish `hne : p ^ (j + 1) ≠ 1` using `fun h => by rw [h] at hm; norm_num at hm`. Distinguish the cases in `hpl : p = l`. Substitute `hpl` using the available equality. Rewrite using `[padicValNat_self, rootWeight, if_pos ⟨hne, j + 1, rfl⟩]`.

Establish `ht : ((p ^ (j + 1)).totient : ℚ) ≠ 0`. Conclude with `(Nat.totient_pos.mpr (by positivity)).ne'` after adjusting the coercions. Rewrite using `[Nat.cast_one, mul_one_div, div_self ht]`. Rewrite using `[padicValNat_primes (Ne.symm hpl), rootWeight, if_neg]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨-, s, hs⟩`. Apply `hpl` to reduce the goal to its premises. Break down `s with _ | s` into its components or cases. Rewrite `hs` using `[pow_zero]`. Conclude with `absurd hs hne`.

Establish `hd : p ∣ l ^ (s + 1)`. Rewrite using `[← hs]`. Conclude with `dvd_pow_self p (Nat.succ_ne_zero j)`. Conclude with `(Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).mp (hp.dvd_of_dvd_pow hd)`. Establish `h1 : Polynomial.eval 1 (Polynomial.cyclotomic m ℤ) = 1`.

Apply `Polynomial.eval_one_cyclotomic_not_prime_pow` to reduce the goal to its premises. Introduce `p hp j hj`. Break down `j with _ | j` into its components or cases. Rewrite `hj` using `[pow_zero]`. Use linear arithmetic over natural numbers and integers.

Conclude with `hpp ⟨p, j, hp, hj.symm⟩`. Rewrite using `[h1, rootWeight, if_neg]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨-, s, hs⟩`. Break down `s with _ | s` into its components or cases.

Rewrite `hs` using `[pow_zero]`. Use linear arithmetic over natural numbers and integers. Conclude with `hpp ⟨l, s, Fact.out, hs⟩`. Rewrite using `[Ideal.absNorm_span_singleton, hnormZ, Int.natAbs_pow, padicValNat.pow, hk]`. Use `push_cast`.

Rewrite using `[hv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem padicValNat_absNorm_one_sub {K : Type*} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime]
    {m : ℕ} (hm : 2 ≤ m) {η : 𝓞 K} (hη : IsPrimitiveRoot η m) :
    (padicValNat l (Ideal.absNorm (Ideal.span {1 - η})) : ℚ) =
      Module.finrank ℚ K * rootWeight l m := by
  haveI : NeZero m := ⟨by omega⟩
  have hηK : IsPrimitiveRoot (η : K) m :=
    hη.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  obtain ⟨k, hk, hnorm⟩ := rootNorm_field (η : K)
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega), Polynomial.natDegree_cyclotomic] at hk
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega)] at hnorm
  have hcQ : (Polynomial.cyclotomic m ℚ).eval 1 = (((Polynomial.cyclotomic m ℤ).eval 1 : ℤ) : ℚ) := by
    rw [← Polynomial.map_cyclotomic_int, ← Int.cast_one, Polynomial.eval_intCast_map, eq_intCast,
      Int.cast_one]
  have hnormZ : Algebra.norm ℤ (1 - η) = ((Polynomial.cyclotomic m ℤ).eval 1) ^ k := by
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, Int.cast_pow, ← hcQ, ← hnorm]
    push_cast
    rfl
  have hv : (padicValNat l ((Polynomial.cyclotomic m ℤ).eval 1).natAbs : ℚ) =
      m.totient * rootWeight l m := by
    by_cases hpp : ∃ p j, p.Prime ∧ m = p ^ (j + 1)
    · obtain ⟨p, j, hp, rfl⟩ := hpp
      haveI := Fact.mk hp
      rw [Polynomial.eval_one_cyclotomic_prime_pow, Int.natAbs_natCast]
      have hne : p ^ (j + 1) ≠ 1 := fun h => by rw [h] at hm; norm_num at hm
      by_cases hpl : p = l
      · subst hpl
        rw [padicValNat_self, rootWeight, if_pos ⟨hne, j + 1, rfl⟩]
        have ht : ((p ^ (j + 1)).totient : ℚ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr (by positivity)).ne'
        rw [Nat.cast_one, mul_one_div, div_self ht]
      · rw [padicValNat_primes (Ne.symm hpl), rootWeight, if_neg]
        · simp
        · rintro ⟨-, s, hs⟩
          apply hpl
          rcases s with _ | s
          · rw [pow_zero] at hs
            exact absurd hs hne
          · have hd : p ∣ l ^ (s + 1) := by
              rw [← hs]
              exact dvd_pow_self p (Nat.succ_ne_zero j)
            exact (Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).mp (hp.dvd_of_dvd_pow hd)
    · have h1 : Polynomial.eval 1 (Polynomial.cyclotomic m ℤ) = 1 := by
        apply Polynomial.eval_one_cyclotomic_not_prime_pow
        intro p hp j hj
        rcases j with _ | j
        · rw [pow_zero] at hj
          omega
        · exact hpp ⟨p, j, hp, hj.symm⟩
      rw [h1, rootWeight, if_neg]
      · simp
      · rintro ⟨-, s, hs⟩
        rcases s with _ | s
        · rw [pow_zero] at hs
          omega
        · exact hpp ⟨l, s, Fact.out, hs⟩
  rw [Ideal.absNorm_span_singleton, hnormZ, Int.natAbs_pow, padicValNat.pow, hk]
  push_cast
  rw [hv]
  ring

end KStar.Ram
