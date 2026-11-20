import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
noncomputable section
open IsLocalRing UpperTheory.Et

/- English proof (translation)
Introduce `A D _ _ _ _ T hI q hq w hw`. Set `τ : Dˣ` to `⟨T.t, T.s, T.ts, by rw [mul_comm]; exact T.ts⟩`. Set `φ0 : LaurentPolynomial A →+* D` to `LaurentPolynomial.eval₂ (algebraMap A D) τ`. Establish `hcomm : ∀ a : A, φ0 (algebraMap A (LaurentPolynomial A) a) = algebraMap A D a`. Introduce `a`.

Simplify using `[φ0, LaurentPolynomial.algebraMap_apply]`. Set `φ : LaurentPolynomial A →ₐ[A] D` to `{ φ0 with commutes' := hcomm }`. Establish `ht : φ (LaurentPolynomial.T 1) = T.t`. Express the relevant statement in the definitionally equal form `φ0 _ = _`. Simplify using `[φ0, τ]`.

Establish `hs : φ (LaurentPolynomial.T (-1)) = T.s`. Express the relevant statement in the definitionally equal form `φ0 _ = _`. Simplify using `[φ0, τ, zpow_neg]`. Use `letI : Algebra (LaurentPolynomial A) D := φ.toRingHom.toAlgebra`. Establish `hmap : ∀ r, algebraMap (LaurentPolynomial A) D r = φ r` using `fun _ => rfl`.

Establish `hadj : Algebra.adjoin A {T.t} ≤ φ.range`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ rfl`. Conclude with `⟨_, ht⟩`. Establish `hB : ∀ b ∈ T.B, IsIntegral (LaurentPolynomial A) b`.

Introduce `b hb`. Take `⟨p, hpm, hp0⟩` from `hI.1 b hb`. Establish `hl : p.map (algebraMap (Algebra.adjoin A {T.t}) D) ∈ Polynomial.lifts (algebraMap (LaurentPolynomial A) D)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`.

Rewrite using `[Polynomial.coeff_map]`. Take `⟨r, hr⟩` from `hadj (p.coeff n).2`. Conclude with `⟨r, hr⟩`. Take `⟨Q, hQ, -, hQm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl (hpm.map _)`. Use `⟨Q, hQm, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Polynomial.eval_map, hQ, Polynomial.eval_map]`. Conclude with `hp0`. Establish `hint : Algebra.IsIntegral (LaurentPolynomial A) D`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `T.locB x`.

Establish `hsI : IsIntegral (LaurentPolynomial A) T.s`. Rewrite using `[← hs]`. Conclude with `isIntegral_algebraMap`. Establish `: x = T.s ^ k * (T.t ^ k * x)`. Rewrite using `[← mul_assoc, ← mul_pow, mul_comm T.s, T.ts, one_pow, one_mul]`.

Rewrite using `[this]`. Conclude with `(hsI.pow k).mul (hB _ hk)`. Establish `hu : w ^ q - 1 ∈ Ideal.map (algebraMap (LaurentPolynomial A) D) ((maximalIdeal A).map (algebraMap A (LaurentPolynomial A)))`. Use `Submodule.smul_induction_on hw ?_ ?_` and prove the remaining obligations. Introduce `a ha d _`.

Rewrite using `[Algebra.smul_def]`. Use `Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Establish `: algebraMap A D a = algebraMap (LaurentPolynomial A) D (algebraMap A (LaurentPolynomial A) a)`. Rewrite using `[hmap]`. Conclude with `(hcomm a).symm`.

Rewrite using `[this]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)`. Introduce `x y hx hy`. Conclude with `Ideal.add_mem _ hx hy`. Take `⟨Q, hQm, hQ0, hQc⟩` from `Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hu`.

Use `set I := (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) with hIdef`. Establish `hmon : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).Monic`. Simplify using `using Polynomial.monic_X_pow_sub_C (1 : LaurentPolynomial A) hq.ne'`. Establish `hdeg : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).natDegree ≠ 0`. Use `Polynomial.natDegree_X_pow_sub_C (n := q) (r := (1 : LaurentPolynomial A))` as an intermediate fact.

Rewrite `this` using `[map_one]`. Rewrite using `[this]`. Conclude with `hq.ne'`. Use `⟨φ, Q.comp (Polynomial.X ^ q - 1), Q.natDegree, ht, hs, hQm.comp hmon hdeg, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_comp]`.

Establish `: Polynomial.eval₂ φ.toRingHom w (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)) = w ^ q - 1`. Simplify using `[Polynomial.eval₂_sub, Polynomial.eval₂_pow]`. Rewrite using `[this]`. Conclude with `hQ0`. Introduce `i`.

Establish `hcoef : ∀ j, (Q - Polynomial.X ^ Q.natDegree).coeff j ∈ I`. Introduce `j`. Distinguish the cases in `hj : j = Q.natDegree`. Substitute `hj` using the available equality. Establish `: Q.coeff Q.natDegree = 1` using `hQm`.

Simplify using `[this]`. Simplify `hQc j hj` using `[Polynomial.coeff_X_pow, hj]`. Establish `heq : Q.comp (Polynomial.X ^ q - 1) - (Polynomial.X ^ q - 1) ^ Q.natDegree = (Q - Polynomial.X ^ Q.natDegree).comp (Polynomial.X ^ q - 1)`. Simplify using `[Polynomial.sub_comp]`. Rewrite using `[heq, ← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_comp]`.

Establish `: (Q - Polynomial.X ^ Q.natDegree).map (Ideal.Quotient.mk I) = 0`. Use extensionality with `j`. Rewrite using `[Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hcoef j`. Rewrite using `[this]`.

Simplify using the standard rewrite rules.
-/
theorem UpperTheory.exists_monic_laurent_polynomial_near_root_of_unity :
    ∀ (A D : Type) [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Int → ∀ (q : ℕ), 0 < q → ∀ w : D, w ^ q - 1 ∈ mm (⊤ : Subalgebra A D) →
      ∃ (φ : LaurentPolynomial A →ₐ[A] D) (P : Polynomial (LaurentPolynomial A)) (n : ℕ), φ (LaurentPolynomial.T 1) = T.t ∧ φ (LaurentPolynomial.T (-1)) = T.s ∧ P.Monic ∧ P.eval₂ φ.toRingHom w = 0 ∧
        ∀ i, (P - (Polynomial.X ^ q - 1) ^ n).coeff i ∈ (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) := by
  intro A D _ _ _ _ T hI q hq w hw
  classical
  let τ : Dˣ := ⟨T.t, T.s, T.ts, by rw [mul_comm]; exact T.ts⟩
  let φ0 : LaurentPolynomial A →+* D := LaurentPolynomial.eval₂ (algebraMap A D) τ
  have hcomm : ∀ a : A, φ0 (algebraMap A (LaurentPolynomial A) a) = algebraMap A D a := by
    intro a
    simp [φ0, LaurentPolynomial.algebraMap_apply]
  let φ : LaurentPolynomial A →ₐ[A] D := { φ0 with commutes' := hcomm }
  have ht : φ (LaurentPolynomial.T 1) = T.t := by
    change φ0 _ = _
    simp [φ0, τ]
  have hs : φ (LaurentPolynomial.T (-1)) = T.s := by
    change φ0 _ = _
    simp [φ0, τ, zpow_neg]
  letI : Algebra (LaurentPolynomial A) D := φ.toRingHom.toAlgebra
  have hmap : ∀ r, algebraMap (LaurentPolynomial A) D r = φ r := fun _ => rfl
  have hadj : Algebra.adjoin A {T.t} ≤ φ.range := by
    refine Algebra.adjoin_le ?_
    rintro _ rfl
    exact ⟨_, ht⟩
  have hB : ∀ b ∈ T.B, IsIntegral (LaurentPolynomial A) b := by
    intro b hb
    obtain ⟨p, hpm, hp0⟩ := hI.1 b hb
    have hl : p.map (algebraMap (Algebra.adjoin A {T.t}) D) ∈
        Polynomial.lifts (algebraMap (LaurentPolynomial A) D) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨r, hr⟩ := hadj (p.coeff n).2
      exact ⟨r, hr⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hpm.map _)
    refine ⟨Q, hQm, ?_⟩
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map]
    exact hp0
  have hint : Algebra.IsIntegral (LaurentPolynomial A) D := by
    refine ⟨fun x => ?_⟩
    obtain ⟨k, hk⟩ := T.locB x
    have hsI : IsIntegral (LaurentPolynomial A) T.s := by
      rw [← hs]
      exact isIntegral_algebraMap
    have : x = T.s ^ k * (T.t ^ k * x) := by
      rw [← mul_assoc, ← mul_pow, mul_comm T.s, T.ts, one_pow, one_mul]
    rw [this]
    exact (hsI.pow k).mul (hB _ hk)
  have hu : w ^ q - 1 ∈ Ideal.map (algebraMap (LaurentPolynomial A) D)
      ((maximalIdeal A).map (algebraMap A (LaurentPolynomial A))) := by
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro a ha d _
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have : algebraMap A D a = algebraMap (LaurentPolynomial A) D (algebraMap A (LaurentPolynomial A) a) := by
        rw [hmap]
        exact (hcomm a).symm
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    · intro x y hx hy
      exact Ideal.add_mem _ hx hy
  obtain ⟨Q, hQm, hQ0, hQc⟩ := Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hu
  set I := (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) with hIdef
  have hmon : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : LaurentPolynomial A) hq.ne'
  have hdeg : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).natDegree ≠ 0 := by
    have := Polynomial.natDegree_X_pow_sub_C (n := q) (r := (1 : LaurentPolynomial A))
    rw [map_one] at this
    rw [this]
    exact hq.ne'
  refine ⟨φ, Q.comp (Polynomial.X ^ q - 1), Q.natDegree, ht, hs, hQm.comp hmon hdeg, ?_, ?_⟩
  · rw [Polynomial.eval₂_comp]
    have : Polynomial.eval₂ φ.toRingHom w (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)) = w ^ q - 1 := by
      simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow]
    rw [this]
    exact hQ0
  · intro i
    have hcoef : ∀ j, (Q - Polynomial.X ^ Q.natDegree).coeff j ∈ I := by
      intro j
      by_cases hj : j = Q.natDegree
      · subst hj
        have : Q.coeff Q.natDegree = 1 := hQm
        simp [this]
      · simpa [Polynomial.coeff_X_pow, hj] using hQc j hj
    have heq : Q.comp (Polynomial.X ^ q - 1) - (Polynomial.X ^ q - 1) ^ Q.natDegree =
        (Q - Polynomial.X ^ Q.natDegree).comp (Polynomial.X ^ q - 1) := by
      simp [Polynomial.sub_comp]
    rw [heq, ← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_comp]
    have : (Q - Polynomial.X ^ Q.natDegree).map (Ideal.Quotient.mk I) = 0 := by
      ext j
      rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hcoef j
    rw [this]
    simp

end
