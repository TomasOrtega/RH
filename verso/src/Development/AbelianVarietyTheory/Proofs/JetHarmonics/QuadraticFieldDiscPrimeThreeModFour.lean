import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
open NumberField IntermediateField Polynomial

namespace GlobalTheory

open NumberField IntermediateField Polynomial in

/- English proof (translation)
Introduce and unpack `⟨r, rfl⟩`. Establish `hr : r ^ 2 = -(q : ℚ)`. Apply `(algebraMap ℚ K).injective` to reduce the goal to its premises. Rewrite using `[map_pow, map_neg, map_natCast]`. Conclude with `hx`.

Establish `hq' : (0 : ℚ) < q` using `by exact_mod_cast hq`. Use polynomial arithmetic with `[sq_nonneg r]`.
-/
theorem _root_.GlobalTheory.sqrtNeg_not_mem_range {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (q : ℕ) (hq : 0 < q) (x : K) (hx : x ^ 2 = -(q : K)) : x ∉ (algebraMap ℚ K).range := by
  rintro ⟨r, rfl⟩
  have hr : r ^ 2 = -(q : ℚ) := by
    apply (algebraMap ℚ K).injective
    rw [map_pow, map_neg, map_natCast]
    exact hx
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  nlinarith [sq_nonneg r]

open NumberField IntermediateField Polynomial in

/- English proof (translation)
Establish `hint : IsIntegral ℚ x` using `⟨p, hm, by rwa [aeval_def] at hx⟩`. Establish `hdvd : minpoly ℚ x ∣ p` using `minpoly.dvd ℚ x hx`. Establish `hpos` using `minpoly.natDegree_pos hint`. Establish `hne : (minpoly ℚ x).natDegree ≠ 1` using `fun h => hr (minpoly.natDegree_eq_one_iff.1 h)`. Conclude with `Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hm hdvd (by omega)`.
-/
theorem _root_.GlobalTheory.minpoly_eq_of_quadratic_irrational {K : Type*} [Field K] [Algebra ℚ K]
    (p : ℚ[X]) (hm : p.Monic) (hd : p.natDegree = 2) (x : K) (hx : aeval x p = 0)
    (hr : x ∉ (algebraMap ℚ K).range) : p = minpoly ℚ x := by
  have hint : IsIntegral ℚ x := ⟨p, hm, by rwa [aeval_def] at hx⟩
  have hdvd : minpoly ℚ x ∣ p := minpoly.dvd ℚ x hx
  have hpos := minpoly.natDegree_pos hint
  have hne : (minpoly ℚ x).natDegree ≠ 1 := fun h => hr (minpoly.natDegree_eq_one_iff.1 h)
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hm hdvd (by omega)

open NumberField IntermediateField Polynomial in

/- English proof (translation)
Take `⟨B, t, n, h0, h1, hd⟩` from `_root_.GlobalTheory.QuadraticZeta.exists_basis hK`. Take `⟨m, hm⟩ : ∃ m : ℕ, q + 1 = 4 * m` from `⟨(q + 1) / 4, by omega⟩`. Establish `hxi : IsIntegral ℤ x` using `⟨X ^ 2 + C (q : ℤ), monic_X_pow_add_C _ two_ne_zero, by simp [hx]⟩`. Establish `hyi : IsIntegral ℤ ((1 + x) / 2)`. Use `⟨X ^ 2 - X + C (m : ℤ), by monicity!, ?_⟩` and prove the remaining obligations.

Establish `hmK : (4 : K) * m = q + 1` using `by exact_mod_cast hm.symm`. Simplify using the standard rewrite rules. Take the linear combination `(1 / 4 : K) * hx + (1 / 4 : K) * hmK`. Take `⟨X0, hX0⟩ : ∃ X0 : 𝓞 K, algebraMap (𝓞 K) K X0 = x` from `⟨⟨x, hxi⟩, rfl⟩`. Take `⟨Y0, hY0⟩ : ∃ Y0 : 𝓞 K, algebraMap (𝓞 K) K Y0 = (1 + x) / 2` from `⟨⟨(1 + x) / 2, hyi⟩, rfl⟩`.

Establish `hXY : X0 = (2 : ℤ) • Y0 - B 0`. Rewrite using `[h0, zsmul_eq_mul]`. Apply `FaithfulSMul.algebraMap_injective (𝓞 K) K` to reduce the goal to its premises. Simplify using `only [map_sub, map_mul, map_intCast, map_one, Int.cast_ofNat, map_ofNat]`. Rewrite using `[hX0, hY0]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsq : X0 ^ 2 = -(q : 𝓞 K)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `only [map_pow, map_neg, map_natCast]`. Rewrite using `[hX0, hx]`.

Establish `hb : B.repr X0 1 = 2 * B.repr Y0 1`. Rewrite using `[hXY, map_sub, map_zsmul, Finsupp.sub_apply, Finsupp.smul_apply, B.repr_self, smul_eq_mul]`. Simplify using the standard rewrite rules. Establish `hX` using `B.sum_repr X0`. Rewrite `hX` using `[Fin.sum_univ_two]`.

Generalize the expression as in `B.repr X0 0 = a at hX`. Generalize the expression as in `B.repr X0 1 = c at hX hb`. Generalize the expression as in `B.repr Y0 1 = e at hb`. Substitute `hb` using the available equality. Establish `hli : LinearIndependent ℤ ![B 0, B 1]`.

Use `B.linearIndependent` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Take `⟨k1, k2⟩` from `LinearIndependent.pair_iff.1 hli (a ^ 2 - (2 * e) ^ 2 * n + q) (2 * a * (2 * e) + (2 * e) ^ 2 * t) (by`. Simplify using `only [zsmul_eq_mul] at hX ⊢`.

Rewrite `hX`, the goal using `[h0]`. Move the coercions through the operations in `at hX ⊢`. Take the linear combination `((a : 𝓞 K) * 1 + 2 * (e : 𝓞 K) * B 1 + X0) * hX + hsq + (-(2 * (e : 𝓞 K)) ^ 2) * h1)`. Establish `he : e ≠ 0`. Introduce and unpack `rfl`.

Apply `_root_.GlobalTheory.sqrtNeg_not_mem_range q hq.pos x hx` to reduce the goal to its premises. Use `⟨(a : ℚ), ?_⟩` and prove the remaining obligations. Establish `hc` using `congrArg (algebraMap (𝓞 K) K) hX`. Simplify using `only [zero_smul, add_zero, zsmul_eq_mul, h0, mul_one, map_intCast] at hc`. Rewrite `hc` using `[hX0]`.

Simplify using `using hc`. Establish `h2 : 2 * a + 2 * e * t = 0`. Establish `h' : (2 * e) * (2 * a + 2 * e * t) = 0` using `by linear_combination k2`. Break down `mul_eq_zero.1 h' with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Establish `h3 : a + e * t = 0` using `by linarith`. Establish `hD : e ^ 2 * discr K = -q`. Rewrite using `[hd]`. Take the linear combination `(e * t - a) * h3 + k1`.

Establish `hN` using `congrArg Int.natAbs hD`. Rewrite `hN` using `[Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast]`. Establish `hdvd : e.natAbs ^ 2 ∣ q` using `⟨_, hN.symm⟩`. Break down `hq.eq_one_or_self_of_dvd _ hdvd with h | h` into its components or cases. Rewrite `hN` using `[h, one_mul]`.

Conclude with `hN`. It suffices to derive a contradiction. Establish `hp : (e.natAbs * e.natAbs).Prime` using `by rw [← sq, h]; exact hq`. Apply the tactic sequence `rcases Nat.prime_mul_iff.1 hp with ⟨hp', he1⟩ | ⟨hp', he1⟩ <;>`. Simplify using `[he1, Nat.not_prime_one] at hp'`.
-/
theorem _root_.GlobalTheory.natAbs_discr_of_sq_eq_neg_prime (K : Type*) [Field K] [NumberField K] (q : ℕ)
    (hq : q.Prime) (h4 : q % 4 = 3) (x : K) (hx : x ^ 2 = -(q : K))
    (hK : Module.finrank ℚ K = 2) : (NumberField.discr K).natAbs = q := by
  obtain ⟨B, t, n, h0, h1, hd⟩ := _root_.GlobalTheory.QuadraticZeta.exists_basis hK
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q + 1 = 4 * m := ⟨(q + 1) / 4, by omega⟩
  have hxi : IsIntegral ℤ x :=
    ⟨X ^ 2 + C (q : ℤ), monic_X_pow_add_C _ two_ne_zero, by simp [hx]⟩
  have hyi : IsIntegral ℤ ((1 + x) / 2) := by
    refine ⟨X ^ 2 - X + C (m : ℤ), by monicity!, ?_⟩
    have hmK : (4 : K) * m = q + 1 := by exact_mod_cast hm.symm
    simp
    linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hmK
  obtain ⟨X0, hX0⟩ : ∃ X0 : 𝓞 K, algebraMap (𝓞 K) K X0 = x := ⟨⟨x, hxi⟩, rfl⟩
  obtain ⟨Y0, hY0⟩ : ∃ Y0 : 𝓞 K, algebraMap (𝓞 K) K Y0 = (1 + x) / 2 :=
    ⟨⟨(1 + x) / 2, hyi⟩, rfl⟩
  have hXY : X0 = (2 : ℤ) • Y0 - B 0 := by
    rw [h0, zsmul_eq_mul]
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    simp only [map_sub, map_mul, map_intCast, map_one, Int.cast_ofNat, map_ofNat]
    rw [hX0, hY0]
    ring
  have hsq : X0 ^ 2 = -(q : 𝓞 K) := by
    apply RingOfIntegers.ext
    simp only [map_pow, map_neg, map_natCast]
    rw [hX0, hx]
  have hb : B.repr X0 1 = 2 * B.repr Y0 1 := by
    rw [hXY, map_sub, map_zsmul, Finsupp.sub_apply, Finsupp.smul_apply, B.repr_self,
      smul_eq_mul]
    simp
  have hX := B.sum_repr X0
  rw [Fin.sum_univ_two] at hX
  generalize B.repr X0 0 = a at hX
  generalize B.repr X0 1 = c at hX hb
  generalize B.repr Y0 1 = e at hb
  subst hb
  have hli : LinearIndependent ℤ ![B 0, B 1] := by
    convert B.linearIndependent
    ext i
    fin_cases i <;> rfl
  obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.1 hli (a ^ 2 - (2 * e) ^ 2 * n + q)
    (2 * a * (2 * e) + (2 * e) ^ 2 * t) (by
      simp only [zsmul_eq_mul] at hX ⊢
      rw [h0] at hX ⊢
      push_cast at hX ⊢
      linear_combination ((a : 𝓞 K) * 1 + 2 * (e : 𝓞 K) * B 1 + X0) * hX + hsq
        + (-(2 * (e : 𝓞 K)) ^ 2) * h1)
  have he : e ≠ 0 := by
    rintro rfl
    apply _root_.GlobalTheory.sqrtNeg_not_mem_range q hq.pos x hx
    refine ⟨(a : ℚ), ?_⟩
    have hc := congrArg (algebraMap (𝓞 K) K) hX
    simp only [zero_smul, add_zero, zsmul_eq_mul, h0, mul_one, map_intCast] at hc
    rw [hX0] at hc
    simpa using hc
  have h2 : 2 * a + 2 * e * t = 0 := by
    have h' : (2 * e) * (2 * a + 2 * e * t) = 0 := by linear_combination k2
    rcases mul_eq_zero.1 h' with h | h
    · omega
    · exact h
  have h3 : a + e * t = 0 := by linarith
  have hD : e ^ 2 * discr K = -q := by
    rw [hd]
    linear_combination (e * t - a) * h3 + k1
  have hN := congrArg Int.natAbs hD
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast] at hN
  have hdvd : e.natAbs ^ 2 ∣ q := ⟨_, hN.symm⟩
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h | h
  · rw [h, one_mul] at hN
    exact hN
  · exfalso
    have hp : (e.natAbs * e.natAbs).Prime := by rw [← sq, h]; exact hq
    rcases Nat.prime_mul_iff.1 hp with ⟨hp', he1⟩ | ⟨hp', he1⟩ <;>
      simp [he1, Nat.not_prime_one] at hp'

/- English proof (translation)
Introduce `q x hq h4 hx _`. Establish `hpm : (X ^ 2 + C (q : ℚ)).Monic` using `by monicity!`. Establish `hpd : (X ^ 2 + C (q : ℚ)).natDegree = 2` using `by compute_degree!`. Establish `h0 : aeval x (X ^ 2 + C (q : ℚ)) = 0` using `by simp [hx]`. Establish `hmin` using `minpoly_eq_of_quadratic_irrational _ hpm hpd x h0 (sqrtNeg_not_mem_range q hq.pos x hx)`.

Establish `hfin : Module.finrank ℚ ℚ⟮x⟯ = 2`. Use `IntermediateField.adjoin.finrank (K := ℚ) (x := x) ⟨_, hpm, h0⟩` as an intermediate fact. Rewrite `this` using `[← hmin, hpd]`. Conclude with `this`. Establish `: Algebra.IsQuadraticExtension ℚ ℚ⟮x⟯` using `⟨hfin⟩`.

Use `⟨Algebra.IsQuadraticExtension.isGalois _ _, hfin, ?_⟩` and prove the remaining obligations. Use `natAbs_discr_of_sq_eq_neg_prime ℚ⟮x⟯ q hq h4 (AdjoinSimple.gen ℚ x) ?_ hfin` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hx`.
-/
theorem isGalois_finrank_discr_adjoin_sqrt_neg_prime :
    ∀ (q : ℕ) (x : ℂ), q.Prime → q % 4 = 3 → x ^ 2 = -(q : ℂ) → ∀ [NumberField ℚ⟮x⟯],
      IsGalois ℚ ℚ⟮x⟯ ∧ Module.finrank ℚ ℚ⟮x⟯ = 2 ∧ (NumberField.discr ℚ⟮x⟯).natAbs = q := by
  intro q x hq h4 hx _
  have hpm : (X ^ 2 + C (q : ℚ)).Monic := by monicity!
  have hpd : (X ^ 2 + C (q : ℚ)).natDegree = 2 := by compute_degree!
  have h0 : aeval x (X ^ 2 + C (q : ℚ)) = 0 := by simp [hx]
  have hmin := minpoly_eq_of_quadratic_irrational _ hpm hpd x h0
    (sqrtNeg_not_mem_range q hq.pos x hx)
  have hfin : Module.finrank ℚ ℚ⟮x⟯ = 2 := by
    have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) ⟨_, hpm, h0⟩
    rw [← hmin, hpd] at this
    exact this
  have : Algebra.IsQuadraticExtension ℚ ℚ⟮x⟯ := ⟨hfin⟩
  refine ⟨Algebra.IsQuadraticExtension.isGalois _ _, hfin, ?_⟩
  refine natAbs_discr_of_sq_eq_neg_prime ℚ⟮x⟯ q hq h4 (AdjoinSimple.gen ℚ x) ?_ hfin
  apply Subtype.ext
  simpa using hx

end GlobalTheory
