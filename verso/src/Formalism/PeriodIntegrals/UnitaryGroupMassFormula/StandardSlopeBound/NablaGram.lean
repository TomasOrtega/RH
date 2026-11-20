import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.MonomialFactorizationLower
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.StdSlopeLowOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.GramMatrixDuality

noncomputable section

namespace PI.SlopeSteps

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV Matrix

/- English proof (translation)
Simplify using `only [det_apply, mul_apply, Fintype.prod_sum, Finset.smul_sum, submatrix_apply, id]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Simplify using `only [Units.smul_def, zsmul_eq_mul, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_mul_rect' {R : Type*} [CommRing R] {k : ℕ} {n : Type*} [Fintype n]
    (A : Matrix (Fin k) n R) (B : Matrix n (Fin k) R) :
    (A * B).det = ∑ f : Fin k → n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [det_apply, mul_apply, Fintype.prod_sum, Finset.smul_sum, submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
The claim follows from `Equiv.sum_comp (Equiv.arrowCongr τ.symm (Equiv.refl n)) F`.
-/
theorem sum_comp_perm' {M : Type*} [AddCommMonoid M] {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (F : (Fin k → n) → M) (τ : Equiv.Perm (Fin k)) : ∑ f : Fin k → n, F (fun i => f (τ i)) = ∑ f, F f :=
  Equiv.sum_comp (Equiv.arrowCongr τ.symm (Equiv.refl n)) F

/- English proof (translation)
Establish `hexp : (Vᵀ * diagonal q * V).det = ∑ f : Fin k → n, (∏ i, q (f i)) * ((∏ i, V (f i) i) * (Vᵀ.submatrix id f).det)`. Rewrite using `[Matrix.mul_assoc, det_mul_rect']`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Simplify using `only [diagonal_mul, Finset.prod_mul_distrib, mul_assoc]`. Establish `hk : (k.factorial : R) = ∑ _τ : Equiv.Perm (Fin k), (1 : R)`.

Simplify using `[Fintype.card_perm]`. Establish `step : ∀ τ : Equiv.Perm (Fin k), (1 : R) * ∑ f : Fin k → n, (∏ i, q (f i)) * ((∏ i, V (f i) i) * (Vᵀ.submatrix id f).det) = ∑ f : Fin k → n, (∏ i, q (f i)) * ((∏ i, V (f (τ i)) i) * ((Vᵀ.submatrix id f).submatrix id τ).det)`. Introduce `τ`. Rewrite using `[one_mul, ← sum_comp_perm' _ τ]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations.

Rewrite using `[Equiv.prod_comp τ (fun i => q (f i))]`. Both sides reduce to the same expression. Rewrite using `[hexp, hk, Finset.sum_mul, Finset.sum_congr rfl fun τ _ => step τ, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`.

Use `congr 1`. Rewrite using `[det_apply (V.submatrix f id), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[det_permute']`. Simplify using `only [submatrix_apply, id, Units.smul_def, zsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem factorial_mul_det_gram_cauchy_binet {R : Type*} [CommRing R] (k : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (q : n → R) (V : Matrix n (Fin k) R) :
    (k.factorial : R) * (Vᵀ * diagonal q * V).det =
      ∑ f : Fin k → n, (∏ i, q (f i)) * ((V.submatrix f id).det * (Vᵀ.submatrix id f).det) := by
  have hexp : (Vᵀ * diagonal q * V).det = ∑ f : Fin k → n, (∏ i, q (f i)) *
      ((∏ i, V (f i) i) * (Vᵀ.submatrix id f).det) := by
    rw [Matrix.mul_assoc, det_mul_rect']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [diagonal_mul, Finset.prod_mul_distrib, mul_assoc]
  have hk : (k.factorial : R) = ∑ _τ : Equiv.Perm (Fin k), (1 : R) := by
    simp [Fintype.card_perm]
  have step : ∀ τ : Equiv.Perm (Fin k),
      (1 : R) * ∑ f : Fin k → n, (∏ i, q (f i)) * ((∏ i, V (f i) i) * (Vᵀ.submatrix id f).det)
        = ∑ f : Fin k → n, (∏ i, q (f i)) *
            ((∏ i, V (f (τ i)) i) * ((Vᵀ.submatrix id f).submatrix id τ).det) := by
    intro τ
    rw [one_mul, ← sum_comp_perm' _ τ]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Equiv.prod_comp τ (fun i => q (f i))]
    rfl
  rw [hexp, hk, Finset.sum_mul, Finset.sum_congr rfl fun τ _ => step τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [det_apply (V.submatrix f id), Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [det_permute']
  simp only [submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[factorial_mul_det_gram_cauchy_binet]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[← transpose_submatrix, det_transpose]`.
-/
theorem factorial_mul_det_sq {R : Type*} [CommRing R] (k : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (q : n → R) (V : Matrix n (Fin k) R) :
    (k.factorial : R) * (Vᵀ * diagonal q * V).det =
      ∑ f : Fin k → n, (∏ i, q (f i)) * ((V.submatrix f id).det * (V.submatrix f id).det) := by
  rw [factorial_mul_det_gram_cauchy_binet]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← transpose_submatrix, det_transpose]

/- English proof (translation)
Unfold `fockQ`. Use `Finset.sum_subset hS fun m _ hm => ?_` and prove the remaining obligations. Rewrite `hm` using `[MvPolynomial.mem_support_iff, not_not]`. Rewrite using `[hm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockQ_eq_sum {σ : Type} (P Q : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    fockQ P Q = ∑ m ∈ S, P.coeff m * Q.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm]
  ring

/- English proof (translation)
Introduce `N ν r e hν`. Establish `hpos` using `hwNormPos ν`. Use `set h := fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) with hh`. Establish `hNpow` using `natPowPos N (∑ s, ν s) (sumNuZero ν)`. Use `set A : ℚ := ((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * h) with hA`.

Establish `hA0 : 0 ≤ A` using `div_nonneg (Nat.cast_nonneg _) (mul_pos hNpow hpos).le`. Use `set S : Finset (Fin N × Fin N →₀ ℕ) := Finset.univ.biUnion fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ).support with hS`. Use `set Vz : Matrix S (Fin r) ℤ := Matrix.of fun m i => (e i : MvPolynomial (Fin N × Fin N) ℤ).coeff m.1 with hVz`. Use `set V : Matrix S (Fin r) ℚ := Vz.map (Int.castRingHom ℚ) with hV`. Use `set q : S → ℚ := fun m => ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) / h with hq`.

Establish `hG : gramOf ν (fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)) = Vᵀ * diagonal q * V`. Use extensionality with `i j`. Establish `hsub : (map (Int.castRingHom ℚ) (e i : MvPolynomial (Fin N × Fin N) ℤ)).support ⊆ S` using `(MvPolynomial.support_map_subset _ _).trans (by`. Rewrite using `[hS]`. Conclude with `Finset.subset_biUnion_of_mem (fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ).support) (Finset.mem_univ i))`.

Simplify using `only [gramOf, Matrix.of_apply]`. Rewrite using `[fockQ_eq_sum _ _ S hsub, Finset.sum_div, ← Finset.sum_coe_sort S]`. Rewrite using `[mul_apply]`. Simplify using `only [mul_diagonal, transpose_apply, hV, hVz, map_apply, of_apply, hq, coeff_map, eq_intCast]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[← hh]`. Expand and normalize the polynomial expressions, which then agree. Establish `hqA : ∀ m : S, A ≤ q m`. Introduce `m`. Take `⟨i, -, hm⟩` from `Finset.mem_biUnion.mp m.2`.

Establish `hcol` using `colSums ℤ N N ν _ (e i).2 m.1 hm`. Establish `hT1` using `monomial_factorization_lower N ν m.1 hcol`. Establish `hT1q : ((∏ s, (ν s).factorial : ℕ) : ℚ) ≤ (N : ℚ) ^ (∑ s, ν s) * ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ)`. Conclude with `hT1` after adjusting the coercions. Rewrite using `[hA, hq]`.

Rewrite using `[div_le_div_iff₀ (mul_pos hNpow hpos) hpos]`. Combine the equalities or inequalities in the displayed calculation. Establish `hid1` using `factorial_mul_det_sq r (fun _ => (1 : ℚ)) V`. Rewrite `hid1` using `[diagonal_one, Matrix.mul_one]`. Simplify using `only [Finset.prod_const_one, one_mul] at hid1`.

Establish `hfac : (0 : ℚ) < r.factorial` using `by exact_mod_cast Nat.factorial_pos r`. Establish `hVVnn : 0 ≤ (Vᵀ * V).det`. Establish `h0 : 0 ≤ (r.factorial : ℚ) * (Vᵀ * V).det`. Rewrite using `[hid1]`. Conclude with `Finset.sum_nonneg fun f _ => mul_self_nonneg _`.

Conclude with `nonneg_of_mul_nonneg_right (by linarith) hfac`. Establish `hind` using `linIndep_Q e`. Establish `hVVne : (Vᵀ * V).det ≠ 0`. Introduce `h0`. Take `⟨v, hv0, hv⟩` from `exists_mulVec_eq_zero_iff.mpr h0`.

Establish `h1 : dotProduct (V *ᵥ v) (V *ᵥ v) = 0`. Establish `h1'` using `congrArg (fun x => dotProduct v x) hv`. Simplify using `only [dotProduct_zero] at h1'`. Rewrite `h1'` using `[← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]`. Then use the resulting hypothesis. Establish `h2 : V *ᵥ v = 0`.

Use function extensionality and compare the values at `m`. Establish `h3` using `(Finset.sum_eq_zero_iff_of_nonneg (fun m _ => mul_self_nonneg ((V *ᵥ v) m))).mp h1 m (Finset.mem_univ _)`. Conclude with `mul_self_eq_zero.mp h3`. Establish `h3 : ∑ i, v i • intQ N N (e i : MvPolynomial (Fin N × Fin N) ℤ) = 0`. Use extensionality with `m`.

Rewrite using `[MvPolynomial.coeff_sum, MvPolynomial.coeff_zero]`. Simplify using `only [MvPolynomial.coeff_smul, smul_eq_mul, we_intQ_apply, MvPolynomial.coeff_map, eq_intCast]`. Distinguish the cases in `hm : m ∈ S`. Establish `h4` using `congrFun h2 ⟨m, hm⟩`. Simplify using `only [mulVec, dotProduct, hV, hVz, map_apply, of_apply, Pi.zero_apply, eq_intCast] at h4`.

Rewrite using `[← h4]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `h5 : (e i : MvPolynomial (Fin N × Fin N) ℤ).coeff m = 0`. Assume the negation of the conclusion as `hc`.

Conclude with `hm (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, MvPolynomial.mem_support_iff.mpr hc⟩)`. Rewrite using `[h5, Int.cast_zero, mul_zero]`. Conclude with `hv0 (funext (Fintype.linearIndependent_iff.mp hind v h3))`. Establish `hVVint : (Vᵀ * V).det = (((Vzᵀ * Vz).det : ℤ) : ℚ)`. Establish `h6` using `RingHom.map_det (Int.castRingHom ℚ) (Vzᵀ * Vz)`.

Rewrite `h6` using `[eq_intCast]`. Rewrite using `[h6, RingHom.mapMatrix_apply, Matrix.map_mul, transpose_map]`. Establish `hVV1 : 1 ≤ (Vᵀ * V).det`. Rewrite `hVVnn`, `hVVne`, the goal using `[hVVint]`. Establish `hz : 0 < (Vzᵀ * Vz).det`.

Use `lt_of_le_of_ne hVVnn (Ne.symm hVVne)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Conclude with `hz` after adjusting the coercions. Establish `hid` using `factorial_mul_det_sq r q V`. Establish `hprod : ∀ f : Fin r → S, A ^ r ≤ ∏ i, q (f i)`.

Introduce `f`. Combine the equalities or inequalities in the displayed calculation. Establish `hmain : A ^ r * ((r.factorial : ℚ) * (Vᵀ * V).det) ≤ (r.factorial : ℚ) * (Vᵀ * diagonal q * V).det`. Rewrite using `[hid1, hid, Finset.mul_sum]`. Conclude with `Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hprod f) (mul_self_nonneg _)`.

Rewrite using `[hG]`. Establish `hAr : 0 ≤ A ^ r` using `pow_nonneg hA0 r`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hVV1 (mul_nonneg hAr hfac.le)]`.
-/
theorem nabla_gram_lower_bound : NablaGramLow := by
  intro N ν r e hν
  classical
  have hpos := hwNormPos ν
  set h := fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) with hh
  have hNpow := natPowPos N (∑ s, ν s) (sumNuZero ν)
  set A : ℚ := ((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * h) with hA
  have hA0 : 0 ≤ A := div_nonneg (Nat.cast_nonneg _) (mul_pos hNpow hpos).le
  set S : Finset (Fin N × Fin N →₀ ℕ) :=
    Finset.univ.biUnion fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ).support with hS
  set Vz : Matrix S (Fin r) ℤ := Matrix.of fun m i => (e i : MvPolynomial (Fin N × Fin N) ℤ).coeff m.1 with hVz
  set V : Matrix S (Fin r) ℚ := Vz.map (Int.castRingHom ℚ) with hV
  set q : S → ℚ := fun m => ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) / h with hq

  have hG : gramOf ν (fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)) = Vᵀ * diagonal q * V := by
    ext i j
    have hsub : (map (Int.castRingHom ℚ) (e i : MvPolynomial (Fin N × Fin N) ℤ)).support ⊆ S :=
      (MvPolynomial.support_map_subset _ _).trans (by
        rw [hS]
        exact Finset.subset_biUnion_of_mem (fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ).support)
          (Finset.mem_univ i))
    simp only [gramOf, Matrix.of_apply]
    rw [fockQ_eq_sum _ _ S hsub, Finset.sum_div, ← Finset.sum_coe_sort S]
    rw [mul_apply]
    simp only [mul_diagonal, transpose_apply, hV, hVz, map_apply, of_apply, hq, coeff_map, eq_intCast]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hh]
    ring

  have hqA : ∀ m : S, A ≤ q m := by
    intro m
    obtain ⟨i, -, hm⟩ := Finset.mem_biUnion.mp m.2
    have hcol := colSums ℤ N N ν _ (e i).2 m.1 hm
    have hT1 := monomial_factorization_lower N ν m.1 hcol
    have hT1q : ((∏ s, (ν s).factorial : ℕ) : ℚ) ≤
        (N : ℚ) ^ (∑ s, ν s) * ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) := by
      exact_mod_cast hT1
    rw [hA, hq]
    rw [div_le_div_iff₀ (mul_pos hNpow hpos) hpos]
    calc ((∏ s, (ν s).factorial : ℕ) : ℚ) * h
        ≤ (N : ℚ) ^ (∑ s, ν s) * ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) * h :=
          mul_le_mul_of_nonneg_right hT1q hpos.le
      _ = ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) * ((N : ℚ) ^ (∑ s, ν s) * h) := by ring

  have hid1 := factorial_mul_det_sq r (fun _ => (1 : ℚ)) V
  rw [diagonal_one, Matrix.mul_one] at hid1
  simp only [Finset.prod_const_one, one_mul] at hid1
  have hfac : (0 : ℚ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hVVnn : 0 ≤ (Vᵀ * V).det := by
    have h0 : 0 ≤ (r.factorial : ℚ) * (Vᵀ * V).det := by
      rw [hid1]; exact Finset.sum_nonneg fun f _ => mul_self_nonneg _
    exact nonneg_of_mul_nonneg_right (by linarith) hfac
  have hind := linIndep_Q e
  have hVVne : (Vᵀ * V).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have h1 : dotProduct (V *ᵥ v) (V *ᵥ v) = 0 := by
      have h1' := congrArg (fun x => dotProduct v x) hv
      simp only [dotProduct_zero] at h1'
      rwa [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at h1'
    have h2 : V *ᵥ v = 0 := by
      funext m
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => mul_self_nonneg ((V *ᵥ v) m))).mp h1 m
        (Finset.mem_univ _)
      exact mul_self_eq_zero.mp h3
    have h3 : ∑ i, v i • intQ N N (e i : MvPolynomial (Fin N × Fin N) ℤ) = 0 := by
      ext m
      rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero]
      simp only [MvPolynomial.coeff_smul, smul_eq_mul, we_intQ_apply, MvPolynomial.coeff_map, eq_intCast]
      by_cases hm : m ∈ S
      · have h4 := congrFun h2 ⟨m, hm⟩
        simp only [mulVec, dotProduct, hV, hVz, map_apply, of_apply, Pi.zero_apply, eq_intCast] at h4
        rw [← h4]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      · refine Finset.sum_eq_zero fun i _ => ?_
        have h5 : (e i : MvPolynomial (Fin N × Fin N) ℤ).coeff m = 0 := by
          by_contra hc
          exact hm (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, MvPolynomial.mem_support_iff.mpr hc⟩)
        rw [h5, Int.cast_zero, mul_zero]
    exact hv0 (funext (Fintype.linearIndependent_iff.mp hind v h3))
  have hVVint : (Vᵀ * V).det = (((Vzᵀ * Vz).det : ℤ) : ℚ) := by
    have h6 := RingHom.map_det (Int.castRingHom ℚ) (Vzᵀ * Vz)
    rw [eq_intCast] at h6
    rw [h6, RingHom.mapMatrix_apply, Matrix.map_mul, transpose_map]
  have hVV1 : 1 ≤ (Vᵀ * V).det := by
    rw [hVVint] at hVVnn hVVne ⊢
    have hz : 0 < (Vzᵀ * Vz).det := by
      have := lt_of_le_of_ne hVVnn (Ne.symm hVVne)
      exact_mod_cast this
    exact_mod_cast hz

  have hid := factorial_mul_det_sq r q V
  have hprod : ∀ f : Fin r → S, A ^ r ≤ ∏ i, q (f i) := by
    intro f
    calc A ^ r = ∏ _i : Fin r, A := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i, q (f i) := Finset.prod_le_prod (fun _ _ => hA0) (fun i _ => hqA (f i))
  have hmain : A ^ r * ((r.factorial : ℚ) * (Vᵀ * V).det) ≤
      (r.factorial : ℚ) * (Vᵀ * diagonal q * V).det := by
    rw [hid1, hid, Finset.mul_sum]
    exact Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hprod f) (mul_self_nonneg _)
  rw [hG]
  have hAr : 0 ≤ A ^ r := pow_nonneg hA0 r
  nlinarith [mul_le_mul_of_nonneg_left hVV1 (mul_nonneg hAr hfac.le)]

end PI.SlopeSteps
