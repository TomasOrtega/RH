import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemIffConjugateNotMem

open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HermSign

/- English proof (translation)
Establish `hd' : ∀ a, d a ≠ 1 → d a = -1` using `fun a h => (mul_self_eq_one_iff.1 (hd a)).resolve_left h`. Establish `h1 : ∑ a, d a = ∑ a, (2 * (if d a = 1 then (1 : ℂ) else 0) - 1)`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[h]`.

Evaluate the numerical expressions. Rewrite using `[hd' a h]`. Evaluate the numerical expressions. Rewrite `h1` using `[Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, hs]`. Establish `h2 : ((Finset.univ.filter fun a => d a = 1).card : ℂ) = m`.

Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1`. Establish `: (r : ℂ) = m + n` using `by exact_mod_cast hr`. Take the linear combination `(-1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * this`. Establish `h3 : Fintype.card {a : Fin r // (a : ℕ) < m} = Fintype.card {a // d a = 1}`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt]`.

Establish `: (Finset.univ.filter fun a => d a = 1).card = m` using `by exact_mod_cast h2`. Rewrite using `[this]`. Use linear arithmetic over natural numbers and integers. Set `e` to `Fintype.equivOfCardEq h3`. Use `⟨e.extendSubtype, fun a => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `ha : (a : ℕ) < m`. Use `e.extendSubtype_mem a ha` as an intermediate fact. Simplify using `[FD.sgn, ha, this]`. Use `hd' _ (e.extendSubtype_not_mem a ha)` as an intermediate fact. Simplify using `[FD.sgn, ha, this]`.
-/
theorem exists_perm_sgn {r m n : ℕ} (hr : r = m + n) (d : Fin r → ℂ) (hd : ∀ a, d a * d a = 1)
    (hs : ∑ a, d a = (m : ℂ) - n) :
    ∃ σ : Equiv.Perm (Fin r), ∀ a, d (σ a) = ((FD.sgn m (a : ℕ) : ℝ) : ℂ) := by
  classical
  have hd' : ∀ a, d a ≠ 1 → d a = -1 := fun a h => (mul_self_eq_one_iff.1 (hd a)).resolve_left h
  have h1 : ∑ a, d a = ∑ a, (2 * (if d a = 1 then (1 : ℂ) else 0) - 1) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rw [h]; norm_num
    · rw [hd' a h]; norm_num
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, hs] at h1
  have h2 : ((Finset.univ.filter fun a => d a = 1).card : ℂ) = m := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1
    have : (r : ℂ) = m + n := by exact_mod_cast hr
    linear_combination (-1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * this
  have h3 : Fintype.card {a : Fin r // (a : ℕ) < m} = Fintype.card {a // d a = 1} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt]
    have : (Finset.univ.filter fun a => d a = 1).card = m := by exact_mod_cast h2
    rw [this]; omega
  let e := Fintype.equivOfCardEq h3
  refine ⟨e.extendSubtype, fun a => ?_⟩
  by_cases ha : (a : ℕ) < m
  · have := e.extendSubtype_mem a ha
    simp [FD.sgn, ha, this]
  · have := hd' _ (e.extendSubtype_not_mem a ha)
    simp [FD.sgn, ha, this]

/- English proof (translation)
Take `⟨P, hP⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.posSemidef.nonneg`. Rewrite `hP` using `[star_eq_conjTranspose]`. Establish `hPd : IsUnit P.det`. Use `hB.det_pos.ne'` as an intermediate fact. Rewrite `this` using `[hP, det_mul]`.

Conclude with `isUnit_iff_ne_zero.2 (right_ne_zero_of_mul this)`. Establish `hPi : P * P⁻¹ = 1` using `mul_nonsing_inv _ hPd`. Establish `hPi' : P⁻¹ * P = 1` using `nonsing_inv_mul _ hPd`. Establish `hPh : Pᴴ * P⁻¹ᴴ = 1` using `by rw [← conjTranspose_mul, hPi', conjTranspose_one]`. Establish `hPh' : P⁻¹ᴴ * Pᴴ = 1` using `by rw [← conjTranspose_mul, hPi, conjTranspose_one]`.

Use `set T := P⁻¹ᴴ * G * P⁻¹ with hT`. Establish `hTh : T.IsHermitian` using `isHermitian_conjTranspose_mul_mul _ hG`. Establish `hGK : G = K * (Pᴴ * P)` using `by rw [← hP, ← mul_assoc, hK, one_mul]`. Establish `hT2 : T = P⁻¹ᴴ * K * Pᴴ`. Rewrite using `[hT, hGK]`.

Simplify using `only [mul_assoc, hPi, mul_one]`. Establish `hTT : T * T = 1`. Rewrite using `[hT2]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`.

Use `_ = 1 := by rw [hPh, mul_one, hK, mul_one, hPh']`. Establish `hTt : T.trace = (m : ℂ) - n`. Rewrite using `[hT2, trace_mul_comm, ← mul_assoc, hPh, one_mul, ht]`. Use `set U : Matrix (Fin r) (Fin r) ℂ := hTh.eigenvectorUnitary.1 with hU`. Use `set d : Fin r → ℂ := RCLike.ofReal ∘ hTh.eigenvalues with hd`.

Establish `hUU : U * Uᴴ = 1`. Rewrite using `[← star_eq_conjTranspose]`. Conclude with `Unitary.coe_mul_star_self _`. Establish `hUU' : Uᴴ * U = 1`. Rewrite using `[← star_eq_conjTranspose]`.

Conclude with `Unitary.coe_star_mul_self _`. Establish `hD : Uᴴ * T * U = diagonal d`. Use `hTh.conjStarAlgAut_star_eigenvectorUnitary` as an intermediate fact. Rewrite `this` using `[Unitary.conjStarAlgAut_star_apply]`. Conclude with `this`.

Establish `hdd : ∀ a, d a * d a = 1`. Establish `: diagonal d * diagonal d = 1`. Rewrite using `[← hD]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `this` using `[diagonal_mul_diagonal, ← diagonal_one]`.

Conclude with `fun a => congrFun (diagonal_injective this) a`. Establish `hds : ∑ a, d a = (m : ℂ) - n`. Rewrite using `[← trace_diagonal, ← hD, trace_mul_comm, ← mul_assoc, hUU, one_mul, hTt]`. Take `⟨σ, hσ⟩` from `exists_perm_sgn hr d hdd hds`. Use `⟨(P⁻¹ * U).submatrix id σ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[det_permute', det_mul]`. Use `mul_ne_zero ?_ (mul_ne_zero ?_ ?_)` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`. Conclude with `left_ne_zero_of_mul_eq_one (b := P.det) (by rw [← det_mul, hPi', det_one])`. Conclude with `left_ne_zero_of_mul_eq_one (b := Uᴴ.det) (by rw [← det_mul, hUU, det_one])`.

Establish `: ((P⁻¹ * U).submatrix id σ)ᴴ * G * (P⁻¹ * U).submatrix id σ = (Uᴴ * T * U).submatrix σ σ`. Establish `e : Uᴴ * T * U = (P⁻¹ * U)ᴴ * G * (P⁻¹ * U)`. Rewrite using `[hT, conjTranspose_mul]`. Simplify using `only [mul_assoc]`. Rewrite using `[e]`.

Use extensionality with `a b`. Simplify using `[mul_apply]`. Rewrite using `[this, hD, submatrix_diagonal_equiv]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Conclude with `hσ a`.
-/
theorem exists_diag_of_involution {r m n : ℕ} (hr : r = m + n) (G K : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.IsHermitian) (hK : K * K = 1) (hB : (K * G).PosDef) (ht : K.trace = (m : ℂ) - n) :
    ∃ N : Matrix (Fin r) (Fin r) ℂ, N.det ≠ 0 ∧
      Nᴴ * G * N = diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ) := by
  classical
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hP
  have hPd : IsUnit P.det := by
    have := hB.det_pos.ne'
    rw [hP, det_mul] at this
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul this)
  have hPi : P * P⁻¹ = 1 := mul_nonsing_inv _ hPd
  have hPi' : P⁻¹ * P = 1 := nonsing_inv_mul _ hPd
  have hPh : Pᴴ * P⁻¹ᴴ = 1 := by rw [← conjTranspose_mul, hPi', conjTranspose_one]
  have hPh' : P⁻¹ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPi, conjTranspose_one]
  set T := P⁻¹ᴴ * G * P⁻¹ with hT
  have hTh : T.IsHermitian := isHermitian_conjTranspose_mul_mul _ hG
  have hGK : G = K * (Pᴴ * P) := by rw [← hP, ← mul_assoc, hK, one_mul]
  have hT2 : T = P⁻¹ᴴ * K * Pᴴ := by
    rw [hT, hGK]; simp only [mul_assoc, hPi, mul_one]
  have hTT : T * T = 1 := by
    rw [hT2]
    calc P⁻¹ᴴ * K * Pᴴ * (P⁻¹ᴴ * K * Pᴴ) = P⁻¹ᴴ * (K * (Pᴴ * P⁻¹ᴴ) * K) * Pᴴ := by
          simp only [mul_assoc]
      _ = 1 := by rw [hPh, mul_one, hK, mul_one, hPh']
  have hTt : T.trace = (m : ℂ) - n := by
    rw [hT2, trace_mul_comm, ← mul_assoc, hPh, one_mul, ht]
  set U : Matrix (Fin r) (Fin r) ℂ := hTh.eigenvectorUnitary.1 with hU
  set d : Fin r → ℂ := RCLike.ofReal ∘ hTh.eigenvalues with hd
  have hUU : U * Uᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  have hUU' : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hD : Uᴴ * T * U = diagonal d := by
    have := hTh.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this
  have hdd : ∀ a, d a * d a = 1 := by
    have : diagonal d * diagonal d = 1 := by
      rw [← hD]
      calc Uᴴ * T * U * (Uᴴ * T * U) = Uᴴ * (T * (U * Uᴴ) * T) * U := by simp only [mul_assoc]
        _ = 1 := by rw [hUU, mul_one, hTT, mul_one, hUU']
    rw [diagonal_mul_diagonal, ← diagonal_one] at this
    exact fun a => congrFun (diagonal_injective this) a
  have hds : ∑ a, d a = (m : ℂ) - n := by
    rw [← trace_diagonal, ← hD, trace_mul_comm, ← mul_assoc, hUU, one_mul, hTt]
  obtain ⟨σ, hσ⟩ := exists_perm_sgn hr d hdd hds
  refine ⟨(P⁻¹ * U).submatrix id σ, ?_, ?_⟩
  · rw [det_permute', det_mul]
    refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · exact left_ne_zero_of_mul_eq_one (b := P.det) (by rw [← det_mul, hPi', det_one])
    · exact left_ne_zero_of_mul_eq_one (b := Uᴴ.det) (by rw [← det_mul, hUU, det_one])
  · have : ((P⁻¹ * U).submatrix id σ)ᴴ * G * (P⁻¹ * U).submatrix id σ =
        (Uᴴ * T * U).submatrix σ σ := by
      have e : Uᴴ * T * U = (P⁻¹ * U)ᴴ * G * (P⁻¹ * U) := by
        rw [hT, conjTranspose_mul]; simp only [mul_assoc]
      rw [e]; ext a b; simp [mul_apply]
    rw [this, hD, submatrix_diagonal_equiv]
    congr 1; funext a; exact hσ a

/- English proof (translation)
Use extensionality with `a b`. Establish `h1` using `h (Pi.single a 1) (Pi.single b 1)`. Establish `h2` using `h (Pi.single a Complex.I) (Pi.single b 1)`. Simplify using `only [Pi.star_single, star_one, mulVec_single_one, single_dotProduct, one_mul, col_apply] at h1 h2`. Use `mul_left_cancel₀ hz (Complex.ext h1 ?_)` and prove the remaining obligations.

Simplify using `at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_of_re_form {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) (z : ℂ) (hz : z ≠ 0)
    (h : ∀ u v : Fin r → ℂ, (z * (u ⬝ᵥ A *ᵥ star v)).re = (z * (u ⬝ᵥ B *ᵥ star v)).re) : A = B := by
  classical
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  have h2 := h (Pi.single a Complex.I) (Pi.single b 1)
  simp only [Pi.star_single, star_one, mulVec_single_one, single_dotProduct, one_mul, col_apply] at h1 h2
  refine mul_left_cancel₀ hz (Complex.ext h1 ?_)
  simp at h2 ⊢
  linarith

/- English proof (translation)
Establish `hs0 : (s : ℂ) ≠ 0`. Introduce `h`. Rewrite `h` using `[Complex.ofReal_eq_zero]`. Simplify using `[h] at hs`. Establish `hεc : (ε : ℂ) * ε = 1` using `by exact_mod_cast hε`.

Establish `hMt : Mᵀ * Mᵀ = -1` using `by rw [← transpose_mul, hM, transpose_neg, transpose_one]`. Establish `hform : ∀ u w : Fin r → ℂ, (M *ᵥ u) ⬝ᵥ G *ᵥ w = u ⬝ᵥ (Mᵀ * G) *ᵥ w`. Introduce `u w`. Rewrite using `[← mulVec_mulVec, dotProduct_mulVec u Mᵀ, vecMul_transpose]`. Establish `hI : Mᵀ * G * Mᵀᴴ = G`.

Use `eq_of_re_form _ _ (s * Complex.I) (mul_ne_zero hs0 Complex.I_ne_zero) fun u v => ?_` and prove the remaining obligations. Rewrite using `[← hinv u v, hform, star_mulVec, ← mulVec_mulVec _ _ Mᵀᴴ]`. Use `congr 4`. Rewrite using `[← mulVec_transpose]`. Both sides reduce to the same expression.

Establish `hI2 : G * Mᵀᴴ = -(Mᵀ * G)`. Combine the equalities or inequalities in the displayed calculation. Use `exists_diag_of_involution hr G ((ε * Complex.I : ℂ) • Mᵀ) hG ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm, hMt, show (ε * Complex.I : ℂ) * (ε * Complex.I) = -1 by`. Take the linear combination `(Complex.I * Complex.I) * hεc + Complex.I_mul_I]`.

Simplify using the standard rewrite rules. Establish `hH : (((ε * Complex.I : ℂ) • Mᵀ) * G).IsHermitian`. Unfold `IsHermitian`. Rewrite using `[smul_mul_assoc, conjTranspose_smul, conjTranspose_mul, hG.eq, hI2]`. Simplify using the standard rewrite rules.

Use `PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_` and prove the remaining obligations. Establish `h1` using `hpos (star x) (by simpa using hx)`. Rewrite `h1` using `[hform, star_star]`. Rewrite using `[Complex.lt_def]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_mul_assoc, smul_mulVec, dotProduct_smul, smul_eq_mul]`. Simplify using `only [mul_assoc, Complex.re_ofReal_mul] at h1 ⊢`. Rewrite using `[Complex.zero_re]`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Use `mul_nonpos_of_nonneg_of_nonpos hs.le hc` as an intermediate fact. Establish `e : ε * s * (ε * (Complex.I * star x ⬝ᵥ (Mᵀ * G) *ᵥ x).re) = (ε * ε) * (s * (Complex.I * star x ⬝ᵥ (Mᵀ * G) *ᵥ x).re)` using `by ring`. Rewrite `this` using `[e, hε]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hH.im_star_dotProduct_mulVec_self x).symm`.

Rewrite using `[trace_smul, trace_transpose, smul_eq_mul, ht]`.
-/
theorem exists_diag_of_complexStructure {r m n : ℕ} (hr : r = m + n)
    (G M : Matrix (Fin r) (Fin r) ℂ) (hG : G.IsHermitian) (s : ℝ) (ε : ℝ) (hε : ε * ε = 1)
    (hs : 0 < ε * s) (hM : M * M = -1)
    (hinv : ∀ u v : Fin r → ℂ, ((s * Complex.I) * ((M *ᵥ u) ⬝ᵥ G *ᵥ star (M *ᵥ v))).re =
      ((s * Complex.I) * (u ⬝ᵥ G *ᵥ star v)).re)
    (hpos : ∀ u : Fin r → ℂ, u ≠ 0 → 0 < ((s * Complex.I) * ((M *ᵥ u) ⬝ᵥ G *ᵥ star u)).re)
    (ht : ε * Complex.I * M.trace = (m : ℂ) - n) :
    ∃ N : Matrix (Fin r) (Fin r) ℂ, N.det ≠ 0 ∧
      Nᴴ * G * N = diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ) := by
  classical
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h; rw [Complex.ofReal_eq_zero] at h; simp [h] at hs
  have hεc : (ε : ℂ) * ε = 1 := by exact_mod_cast hε
  have hMt : Mᵀ * Mᵀ = -1 := by rw [← transpose_mul, hM, transpose_neg, transpose_one]
  have hform : ∀ u w : Fin r → ℂ, (M *ᵥ u) ⬝ᵥ G *ᵥ w = u ⬝ᵥ (Mᵀ * G) *ᵥ w := by
    intro u w
    rw [← mulVec_mulVec, dotProduct_mulVec u Mᵀ, vecMul_transpose]
  have hI : Mᵀ * G * Mᵀᴴ = G := by
    refine eq_of_re_form _ _ (s * Complex.I) (mul_ne_zero hs0 Complex.I_ne_zero) fun u v => ?_
    rw [← hinv u v, hform, star_mulVec, ← mulVec_mulVec _ _ Mᵀᴴ]
    congr 4
    rw [← mulVec_transpose]; rfl
  have hI2 : G * Mᵀᴴ = -(Mᵀ * G) := by
    calc G * Mᵀᴴ = -((Mᵀ * Mᵀ) * G * Mᵀᴴ) := by rw [hMt]; simp
      _ = -(Mᵀ * (Mᵀ * G * Mᵀᴴ)) := by simp only [mul_assoc]
      _ = _ := by rw [hI]
  refine exists_diag_of_involution hr G ((ε * Complex.I : ℂ) • Mᵀ) hG ?_ ?_ ?_
  · rw [smul_mul_smul_comm, hMt, show (ε * Complex.I : ℂ) * (ε * Complex.I) = -1 by
      linear_combination (Complex.I * Complex.I) * hεc + Complex.I_mul_I]
    simp
  · have hH : (((ε * Complex.I : ℂ) • Mᵀ) * G).IsHermitian := by
      unfold IsHermitian
      rw [smul_mul_assoc, conjTranspose_smul, conjTranspose_mul, hG.eq, hI2]
      simp
    refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have h1 := hpos (star x) (by simpa using hx)
    rw [hform, star_star] at h1
    rw [Complex.lt_def]
    refine ⟨?_, ?_⟩
    · rw [smul_mul_assoc, smul_mulVec, dotProduct_smul, smul_eq_mul]
      simp only [mul_assoc, Complex.re_ofReal_mul] at h1 ⊢
      rw [Complex.zero_re]
      by_contra hc
      push Not at hc
      have := mul_nonpos_of_nonneg_of_nonpos hs.le hc
      have e : ε * s * (ε * (Complex.I * star x ⬝ᵥ (Mᵀ * G) *ᵥ x).re) =
        (ε * ε) * (s * (Complex.I * star x ⬝ᵥ (Mᵀ * G) *ᵥ x).re) := by ring
      rw [e, hε] at this
      linarith
    · exact (hH.im_star_dotProduct_mulVec_self x).symm
  · rw [trace_smul, trace_transpose, smul_eq_mul, ht]

/- English proof (translation)
Rewrite using `[LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower (Pi.basisFun ℂ (Fin r)))]`. Simplify using `[Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, two_mul, Finset.sum_add_distrib]`.
-/
theorem trace_real_toLin' {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) :
    LinearMap.trace ℝ _ ((toLin' N).restrictScalars ℝ) = 2 * N.trace.re := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower (Pi.basisFun ℂ (Fin r)))]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, two_mul,
    Finset.sum_add_distrib]

/- English proof (translation)
Establish `: f = ∑ τ, LinearMap.single ℝ (fun _ : ι => Fin r → ℂ) τ ∘ₗ (((toLin' (N τ)).restrictScalars ℝ) ∘ₗ LinearMap.proj τ)`. Use `LinearMap.ext fun u => funext fun τ => ?_` and prove the remaining obligations. Simplify using `[hf, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[this, map_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same, LinearMap.comp_id, trace_real_toLin']`.
-/
theorem trace_real_blocks {ι : Type} [Fintype ι] {r : ℕ} (N : ι → Matrix (Fin r) (Fin r) ℂ)
    (f : (ι → Fin r → ℂ) →ₗ[ℝ] (ι → Fin r → ℂ)) (hf : ∀ u τ, f u τ = N τ *ᵥ u τ) :
    LinearMap.trace ℝ _ f = ∑ τ, 2 * (N τ).trace.re := by
  classical
  have : f = ∑ τ, LinearMap.single ℝ (fun _ : ι => Fin r → ℂ) τ ∘ₗ
      (((toLin' (N τ)).restrictScalars ℝ) ∘ₗ LinearMap.proj τ) := by
    refine LinearMap.ext fun u => funext fun τ => ?_
    simp [hf, Finset.sum_apply, Pi.single_apply]
  rw [this, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same,
    LinearMap.comp_id, trace_real_toLin']

/- English proof (translation)
Set `g : (ι → Fin r → ℂ) →ₗ[ℂ] (ι → Fin r → ℂ)` to `{ toFun := f map_add' := f.map_add map_smul' := fun c u => hf (fun _ => c) u }`. Use `⟨fun τ => LinearMap.toMatrix' (LinearMap.proj τ ∘ₗ g ∘ₗ LinearMap.single ℂ (fun _ : ι => Fin r → ℂ) τ), fun u τ => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Establish `h1 : (Pi.single τ 1 : ι → ℂ) • u = Pi.single τ (u τ)`. Use function extensionality and compare the values at `σ`.

Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `h2` using `congrFun (hf (Pi.single τ 1) u) τ`.

Rewrite `h2` using `[h1]`. Simplify `h2.symm` using `[g]`.
-/
theorem exists_blocks {ι : Type} [Fintype ι] {r : ℕ}
    (f : (ι → Fin r → ℂ) →ₗ[ℝ] (ι → Fin r → ℂ)) (hf : ∀ (c : ι → ℂ) u, f (c • u) = c • f u) :
    ∃ N : ι → Matrix (Fin r) (Fin r) ℂ, ∀ u τ, f u τ = N τ *ᵥ u τ := by
  classical
  let g : (ι → Fin r → ℂ) →ₗ[ℂ] (ι → Fin r → ℂ) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c u => hf (fun _ => c) u }
  refine ⟨fun τ => LinearMap.toMatrix' (LinearMap.proj τ ∘ₗ g ∘ₗ
    LinearMap.single ℂ (fun _ : ι => Fin r → ℂ) τ), fun u τ => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have h1 : (Pi.single τ 1 : ι → ℂ) • u = Pi.single τ (u τ) := by
    funext σ
    by_cases h : σ = τ
    · subst h; simp
    · simp [h]
  have h2 := congrFun (hf (Pi.single τ 1) u) τ
  rw [h1] at h2
  simpa [g] using h2.symm

section
variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Set `δ : Φ → ℂ` to `fun τ => f (Pi.single τ 1) - Complex.I * f (Pi.single τ Complex.I)`. Establish `key : ∀ z : Φ → ℂ, f z = ∑ τ, (z τ * δ τ).re`. Introduce `z`.

Use `conv_lhs => rw [← Finset.univ_sum_single z, map_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `: (Pi.single τ (z τ) : Φ → ℂ) = (z τ).re • (Pi.single τ 1 : Φ → ℂ) + (z τ).im • (Pi.single τ Complex.I : Φ → ℂ)`. Rewrite using `[← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]`. Use `congr 1`.

Simplify using the standard rewrite rules. Rewrite using `[this, map_add, map_smul, map_smul]`. Simplify using `[δ]`. Establish `hδ : δ = 0` using `Φ.eq_zero_of_sum_re_eq_zero δ fun a => by`. Rewrite using `[← key (fun τ => τ.1 (a : E))]`.

Conclude with `hf (Submodule.subset_span ⟨a, rfl⟩)`. Use `hf0 (LinearMap.ext fun z => ?_)` and prove the remaining obligations. Simplify using `[key, hδ]`.
-/
theorem span_integers_eq_top (Φ : CMType E) :
    Submodule.span ℝ (Set.range fun a : 𝓞 E => fun τ : Φ => τ.1 (a : E)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let δ : Φ → ℂ := fun τ => f (Pi.single τ 1) - Complex.I * f (Pi.single τ Complex.I)
  have key : ∀ z : Φ → ℂ, f z = ∑ τ, (z τ * δ τ).re := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have : (Pi.single τ (z τ) : Φ → ℂ) =
        (z τ).re • (Pi.single τ 1 : Φ → ℂ) + (z τ).im • (Pi.single τ Complex.I : Φ → ℂ) := by
      rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
      congr 1
      simp
    rw [this, map_add, map_smul, map_smul]
    simp [δ]
  have hδ : δ = 0 := Φ.eq_zero_of_sum_re_eq_zero δ fun a => by
    rw [← key (fun τ => τ.1 (a : E))]
    exact hf (Submodule.subset_span ⟨a, rfl⟩)
  refine hf0 (LinearMap.ext fun z => ?_)
  simp [key, hδ]

/- English proof (translation)
Establish `hc : c ∈ Submodule.span ℝ (Set.range fun a : 𝓞 E => fun τ : Φ => τ.1 (a : E))`. Rewrite using `[span_integers_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨a, rfl⟩ := hx`.

Conclude with `h a`. Consider the case `zero => simpa using hsmul 0 _ (h 0)`. Consider the case `add x y _ _ hx hy => exact hadd _ _ hx hy`. Consider the case `smul t x _ hx => exact hsmul _ _ hx`.
-/
theorem induction_integers (Φ : CMType E) (P : (Φ → ℂ) → Prop)
    (h : ∀ a : 𝓞 E, P fun τ => τ.1 (a : E)) (hadd : ∀ c c', P c → P c' → P (c + c'))
    (hsmul : ∀ (t : ℝ) c, P c → P (t • c)) (c : Φ → ℂ) : P c := by
  have hc : c ∈ Submodule.span ℝ (Set.range fun a : 𝓞 E => fun τ : Φ => τ.1 (a : E)) := by
    rw [span_integers_eq_top]; trivial
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
  | zero => simpa using hsmul 0 _ (h 0)
  | add x y _ _ hx hy => exact hadd _ _ hx hy
  | smul t x _ hx => exact hsmul _ _ hx

variable [IsCMField E]

def hostType (H : Host E) : CMType E where
  carrier := {τ | τ (H.rt : E) = H.rt0}
  mem_iff_conjugate_notMem' τ := by
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
      simpa using this
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h2 : conj (τ (H.rt : E)) = -τ (H.rt : E) := by
      have h3 : conj (τ (H.rt : E)) ^ 2 = τ (H.rt : E) ^ 2 := by rw [← map_pow, h1]; simp
      refine (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left fun h => ?_
      obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h
      rw [hx] at h1
      have : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast h1
      nlinarith [sq_nonneg x]
    have h4 : H.rt0 ≠ 0 := by
      intro h
      have := H.sqrt_neg_disc_sq
      rw [h] at this
      have h5 : (H.d : ℝ) = 0 := by simpa using this
      exact hd.ne' h5
    simp only [Set.mem_setOf_eq, ComplexEmbedding.conjugate_coe_eq, h2]
    constructor
    · intro h h'
      rw [h] at h'
      exact h4 (by linear_combination (-1 / 2 : ℂ) * h')
    · intro h
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h6 | h6
      · exact h6
      · exact absurd (by rw [h6, neg_neg]) h

/- English proof (translation)
Simplify using `[FD.hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hermC_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    FD.hermC τ G u v = u ⬝ᵥ (G.map τ) *ᵥ star v := by
  simp [FD.hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [FD.gram, FD.hermC, FD.col, of_apply, map_apply, mul_apply, conjTranspose_apply, Finset.sum_mul, Complex.conj_conj, RCLike.star_def]`. Conclude with `Finset.sum_comm`.
-/
theorem gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (N : Matrix (Fin r) (Fin r) ℂ) : FD.gram τ G (N.map conj) = Nᴴ * G.map τ * N := by
  ext a b
  simp only [FD.gram, FD.hermC, FD.col, of_apply, map_apply, mul_apply, conjTranspose_apply,
    Finset.sum_mul, Complex.conj_conj, RCLike.star_def]
  exact Finset.sum_comm

end

section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {r : ℕ}
  (Φ : CMType E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))

noncomputable def realMap : ℝ ⊗[ℤ] D.La →ₗ[ℝ] (Φ → Fin r → ℂ) :=
  LinearMap.liftBaseChange ℝ
    ({ toFun := fun x τ i => τ.1 (φ x i)
       map_add' := fun x y => by funext τ i; simp
       map_smul' := fun n x => by funext τ i; simp } : D.La →ₗ[ℤ] (Φ → Fin r → ℂ))

/- English proof (translation)
Simplify using `[realMap]`.
-/
theorem realMap_tmul (t : ℝ) (x : D.La) (τ : Φ) (i : Fin r) :
    realMap D Φ φ (t ⊗ₜ x) τ i = t * τ.1 (φ x i) := by
  simp [realMap]

noncomputable def realAct (a : 𝓞 E) : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
  (DistribSMul.toLinearMap ℤ D.La a).baseChange ℝ

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, smul_add]`. Consider the case `tmul t x`. Use function extensionality and compare the values at `τ i`.

Simplify using `only [realAct, LinearMap.baseChange_tmul, DistribSMul.toLinearMap_apply, realMap_tmul, map_smul, Pi.smul_apply', Pi.smul_apply, smul_eq_mul, Algebra.smul_def (A := E), map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem realMap_realAct (a : 𝓞 E) (x : ℝ ⊗[ℤ] D.La) :
    realMap D Φ φ (realAct D a x) = (fun τ : Φ => τ.1 (a : E)) • realMap D Φ φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul t x =>
    funext τ i
    simp only [realAct, LinearMap.baseChange_tmul, DistribSMul.toLinearMap_apply, realMap_tmul,
      map_smul, Pi.smul_apply', Pi.smul_apply, smul_eq_mul, Algebra.smul_def (A := E), map_mul]
    ring

/- English proof (translation)
Establish `hst : ∀ c : Φ → ℂ, ∀ w ∈ LinearMap.range (realMap D Φ φ), c • w ∈ LinearMap.range (realMap D Φ φ)`. Use `induction_integers Φ _ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `a _ ⟨x, rfl⟩`. Conclude with `⟨_, realMap_realAct D Φ φ a x⟩`. Introduce `c c' h h' w hw`.

Rewrite using `[add_smul]`. Conclude with `add_mem (h w hw) (h' w hw)`. Introduce `t c h w hw`. Rewrite using `[smul_assoc]`. Conclude with `Submodule.smul_mem _ _ (h w hw)`.

Establish `hv : ∀ v : Fin r → E, (fun (τ : Φ) i => τ.1 (v i)) ∈ LinearMap.range (realMap D Φ φ)`. Introduce `v`. Establish `hv : v ∈ Submodule.span E (Set.range φ)` using `by rw [hspan]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨x, rfl⟩` from `hx`. Conclude with `⟨1 ⊗ₜ x, by funext τ i; simp [realMap_tmul]⟩`. Consider the case `zero => convert zero_mem (LinearMap.range (realMap D Φ φ)) using 1`. Use function extensionality and compare the values at `τ i`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy => convert add_mem hx hy using 1`. Use function extensionality and compare the values at `τ i`. Simplify using the standard rewrite rules. Consider the case `smul b x _ hx => convert hst (fun τ => τ.1 b) _ hx using 1`. Use function extensionality and compare the values at `τ i`.

Simplify using the standard rewrite rules. Introduce `u`. Establish `: u = ∑ i, (fun τ => u τ i) • (fun (τ : Φ) j => τ.1 ((Pi.single i 1 : Fin r → E) j))`. Use function extensionality and compare the values at `τ j`. Simplify using `[Finset.sum_apply, Pi.single_apply, apply_ite τ.1]`.

Rewrite using `[this]`. Conclude with `(LinearMap.range (realMap D Φ φ)).sum_mem fun i _ => hst _ _ (hv _)`.
-/
theorem realMap_surjective (hspan : Submodule.span E (Set.range φ) = ⊤) :
    Function.Surjective (realMap D Φ φ) := by
  classical
  have hst : ∀ c : Φ → ℂ, ∀ w ∈ LinearMap.range (realMap D Φ φ),
      c • w ∈ LinearMap.range (realMap D Φ φ) := by
    refine induction_integers Φ _ ?_ ?_ ?_
    · rintro a _ ⟨x, rfl⟩
      exact ⟨_, realMap_realAct D Φ φ a x⟩
    · intro c c' h h' w hw
      rw [add_smul]
      exact add_mem (h w hw) (h' w hw)
    · intro t c h w hw
      rw [smul_assoc]
      exact Submodule.smul_mem _ _ (h w hw)
  have hv : ∀ v : Fin r → E,
      (fun (τ : Φ) i => τ.1 (v i)) ∈ LinearMap.range (realMap D Φ φ) := by
    intro v
    have hv : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      exact ⟨1 ⊗ₜ x, by funext τ i; simp [realMap_tmul]⟩
    | zero => convert zero_mem (LinearMap.range (realMap D Φ φ)) using 1; funext τ i; simp
    | add x y _ _ hx hy => convert add_mem hx hy using 1; funext τ i; simp
    | smul b x _ hx => convert hst (fun τ => τ.1 b) _ hx using 1; funext τ i; simp
  intro u
  have : u = ∑ i, (fun τ => u τ i) • (fun (τ : Φ) j => τ.1 ((Pi.single i 1 : Fin r → E) j)) := by
    funext τ j
    simp [Finset.sum_apply, Pi.single_apply, apply_ite τ.1]
  rw [this]
  exact (LinearMap.range (realMap D Φ φ)).sum_mem fun i _ => hst _ _ (hv _)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx'`. Simplify using `only [map_add, LinearMap.add_apply, hx, hx', Pi.add_apply, add_dotProduct, mul_add, Complex.add_re, Finset.sum_add_distrib]`. Consider the case `tmul t x`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add y y' hy hy'`. Simplify using `only [map_add, hy, hy', Pi.add_apply, star_add, mulVec_add, dotProduct_add, mul_add, Complex.add_re, Finset.sum_add_distrib]`. Consider the case `tmul s y`.

Establish `h1 : ((D.EF x y : ℤ) : ℝ) = ∑ τ : Φ, 2 * (τ.1 (ξ * FD.herm Gm (φ x) (φ y))).re`. Rewrite using `[← Φ.trace_eq_sum_two_mul_re, ← hEF]`. Simplify using the standard rewrite rules. Rewrite using `[LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, h1, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Establish `h2 : realMap D Φ φ (t ⊗ₜ x) τ ⬝ᵥ (Gm.map τ.1) *ᵥ star (realMap D Φ φ (s ⊗ₜ y) τ) = ((t * s : ℝ) : ℂ) * τ.1 (FD.herm Gm (φ x) (φ y))`. Rewrite using `[← hermC_eq]`. Simplify using `only [FD.hermC, FD.herm, realMap_tmul, map_sum, map_mul, FD.cc, IsCMField.complexEmbedding_complexConj, Finset.mul_sum, Complex.conj_ofReal]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, mul_left_comm (τ.1 ξ), Complex.re_ofReal_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem baseChange_EF (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (x y : ℝ ⊗[ℤ] D.La) :
    D.EF.baseChange ℝ x y = ∑ τ : Φ, 2 * (τ.1 ξ *
      (realMap D Φ φ x τ ⬝ᵥ (Gm.map τ.1) *ᵥ star (realMap D Φ φ y τ))).re := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', Pi.add_apply, add_dotProduct, mul_add,
      Complex.add_re, Finset.sum_add_distrib]
  | tmul t x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' =>
      simp only [map_add, hy, hy', Pi.add_apply, star_add, mulVec_add, dotProduct_add, mul_add,
        Complex.add_re, Finset.sum_add_distrib]
    | tmul s y =>
      have h1 : ((D.EF x y : ℤ) : ℝ) = ∑ τ : Φ, 2 * (τ.1 (ξ * FD.herm Gm (φ x) (φ y))).re := by
        rw [← Φ.trace_eq_sum_two_mul_re, ← hEF]; simp
      rw [LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, h1, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have h2 : realMap D Φ φ (t ⊗ₜ x) τ ⬝ᵥ (Gm.map τ.1) *ᵥ star (realMap D Φ φ (s ⊗ₜ y) τ) =
          ((t * s : ℝ) : ℂ) * τ.1 (FD.herm Gm (φ x) (φ y)) := by
        rw [← hermC_eq]
        simp only [FD.hermC, FD.herm, realMap_tmul, map_sum, map_mul, FD.cc,
          IsCMField.complexEmbedding_complexConj, Finset.mul_sum, Complex.conj_ofReal]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        push_cast
        ring
      rw [h2, mul_left_comm (τ.1 ξ), Complex.re_ofReal_mul, map_mul]
      ring

/- English proof (translation)
Take `⟨J, hJ2, hJinv, hJpos, hJ⟩` from `D.dom`. Establish `hform` using `baseChange_EF D Φ φ ξ Gm hEF`. Establish `hinj : Function.Injective (realMap D Φ φ)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Assume the negation of the conclusion as `h`. Use `hJpos x h` as an intermediate fact. Rewrite `this` using `[hform, hx]`. Simplify using `at this`. Set `e : ℝ ⊗[ℤ] D.La ≃ₗ[ℝ] (Φ → Fin r → ℂ)` to `LinearEquiv.ofBijective (realMap D Φ φ) ⟨hinj, realMap_surjective D Φ φ hspan⟩`.

Establish `he : ∀ x, e x = realMap D Φ φ x` using `fun _ => rfl`. Establish `hA : ∀ a : 𝓞 E, J ∘ₗ realAct D a = realAct D a ∘ₗ J ∧ LinearMap.trace ℝ _ (realAct D a) = 2 * (∑ σ : Φ, ((D.p : ℂ) * σ.1 (a : E) + (D.q : ℂ) * conj (σ.1 (a : E)))).re ∧ LinearMap.trace ℝ _ (J ∘ₗ realAct D a) = -2 * (∑ σ : Φ, ((D.p : ℂ) * σ.1 (a : E) + (D.q : ℂ) * conj (σ.1 (a : E …`. Introduce `a`. Use `hJ a _ _ (fun x => by simp [realAct]) ?_` and prove the remaining obligations. Conclude with `(Finset.sum_subtype (p := fun σ => σ ∈ Φ) _ (fun σ => by rw [Finset.mem_filter]; simp [hΦ]) (fun σ : E →+* ℂ => (D.p : ℂ) * σ (a : E) + (D.q : ℂ) * conj (σ (a : E)))).symm`.

Establish `hJe : ∀ x, e.conj J (e x) = e (J x)` using `fun x => by simp [LinearEquiv.conj_apply]`. Establish `hcomm : ∀ (c : Φ → ℂ) u, e.conj J (c • u) = c • e.conj J u`. Use `induction_integers Φ _ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a u`. Take `⟨x, rfl⟩` from `e.surjective u`.

Rewrite using `[hJe, he, he, ← realMap_realAct, ← realMap_realAct, ← he, ← he, hJe]`. Conclude with `congrArg e (LinearMap.congr_fun (hA a).1 x)`. Introduce `c c' h h' u`. Rewrite using `[add_smul, map_add, h, h', add_smul]`. Introduce `t c h u`.

Rewrite using `[smul_assoc, map_smul, h, smul_assoc]`. Take `⟨M, hM⟩` from `exists_blocks (e.conj J) hcomm`. Establish `hMe : ∀ x σ, realMap D Φ φ (J x) σ = M σ *ᵥ realMap D Φ φ x σ` using `fun x σ => by`. Rewrite using `[← he, ← he, ← hJe, hM]`. Establish `hsingle : ∀ u : Fin r → ℂ, realMap D Φ φ (e.symm (Pi.single τ u)) = Pi.single τ u` using `fun u => e.apply_symm_apply _`.

Establish `hsum : ∀ (f : Φ → ℝ), (∀ σ, σ ≠ τ → f σ = 0) → ∑ σ, f σ = f τ` using `fun f hf => Finset.sum_eq_single τ (fun σ _ h => hf σ h) (by simp)`. Use `clear hJ hcomm`. Use `⟨?_, M τ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `(hA 1).2.1`. Rewrite using `[← LinearMap.trace_conj' _ e, trace_real_blocks (fun _ => 1) _ (fun u σ => by`.

Take `⟨x, rfl⟩` from `e.surjective u`. Simplify using `only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Simplify using `[he, realMap_realAct])] at h1`. Establish `hc : (Fintype.card Φ : ℝ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Simplify using `at h1`.

Establish `: (r : ℝ) = D.p + D.q` using `mul_left_cancel₀ hc (by linarith)`. Conclude with `this` after adjusting the coercions. Use `toLin'.injective (LinearMap.ext fun u => ?_)` and prove the remaining obligations. Use `hMe (J (e.symm (Pi.single τ u))) τ` as an intermediate fact. Rewrite `this` using `[hJ2, hMe, map_neg, hsingle]`.

Simplify `this.symm` using `[neg_mulVec]`. Introduce `u v`. Use `hJinv (e.symm (Pi.single τ u)) (e.symm (Pi.single τ v))` as an intermediate fact. Rewrite `this` using `[hform, hform, hsum _ (fun σ h => by simp [hMe, hsingle, h]), hsum _ (fun σ h => by simp [hsingle, h]), hMe, hMe, hsingle, hsingle]`. Simplify using `only [Pi.single_eq_same] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `u hu`. Use `hJpos (e.symm (Pi.single τ u)) (by simpa using hu)` as an intermediate fact. Rewrite `this` using `[hform, hsum _ (fun σ h => by simp [hsingle, h]), hMe, hsingle]`. Simplify using `only [Pi.single_eq_same] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `Φ.eq_zero_of_sum_re_eq_zero (fun σ => (M σ).trace - Complex.I * ((D.p : ℂ) - D.q)) fun a => by` as an intermediate fact. Establish `h1` using `(hA a).2.2`. Rewrite using `[← LinearMap.trace_conj' _ e, trace_real_blocks (fun σ => σ.1 (a : E) • M σ) _ (fun u σ => by`. Take `⟨x, rfl⟩` from `e.surjective u`.

Simplify using `only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Simplify using `only [he, hMe, realMap_realAct, Pi.smul_apply', mulVec_smul, smul_mulVec]), Complex.im_sum, Finset.mul_sum,`. Use the proof step `← sub_eq_zero, ← Finset.sum_sub_distrib] at h1`. Establish `h2 : 2 * ∑ σ : Φ, (σ.1 (a : E) * ((M σ).trace - Complex.I * ((D.p : ℂ) - D.q))).re = 0`. Rewrite using `[← h1, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `[trace_smul]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `sub_eq_zero.1 (congrFun this τ)`.
-/
theorem exists_complexStructure (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (hΦ : ∀ σ, σ ∈ Φ ↔ σ (H.rt : E) = H.rt0) (τ : Φ) :
    r = D.p + D.q ∧ ∃ M : Matrix (Fin r) (Fin r) ℂ, M * M = -1 ∧
      (∀ u v : Fin r → ℂ, (τ.1 ξ * ((M *ᵥ u) ⬝ᵥ (Gm.map τ.1) *ᵥ star (M *ᵥ v))).re =
        (τ.1 ξ * (u ⬝ᵥ (Gm.map τ.1) *ᵥ star v)).re) ∧
      (∀ u : Fin r → ℂ, u ≠ 0 → 0 < (τ.1 ξ * ((M *ᵥ u) ⬝ᵥ (Gm.map τ.1) *ᵥ star u)).re) ∧
      M.trace = Complex.I * ((D.p : ℂ) - D.q) := by
  classical
  obtain ⟨J, hJ2, hJinv, hJpos, hJ⟩ := D.dom
  have hform := baseChange_EF D Φ φ ξ Gm hEF
  have hinj : Function.Injective (realMap D Φ φ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    have := hJpos x h
    rw [hform, hx] at this
    simp at this
  let e : ℝ ⊗[ℤ] D.La ≃ₗ[ℝ] (Φ → Fin r → ℂ) :=
    LinearEquiv.ofBijective (realMap D Φ φ) ⟨hinj, realMap_surjective D Φ φ hspan⟩
  have he : ∀ x, e x = realMap D Φ φ x := fun _ => rfl
  have hA : ∀ a : 𝓞 E, J ∘ₗ realAct D a = realAct D a ∘ₗ J ∧
      LinearMap.trace ℝ _ (realAct D a) = 2 * (∑ σ : Φ, ((D.p : ℂ) * σ.1 (a : E) +
        (D.q : ℂ) * conj (σ.1 (a : E)))).re ∧
      LinearMap.trace ℝ _ (J ∘ₗ realAct D a) = -2 * (∑ σ : Φ, ((D.p : ℂ) * σ.1 (a : E) +
        (D.q : ℂ) * conj (σ.1 (a : E)))).im := by
    intro a
    refine hJ a _ _ (fun x => by simp [realAct]) ?_
    exact (Finset.sum_subtype (p := fun σ => σ ∈ Φ) _
      (fun σ => by rw [Finset.mem_filter]; simp [hΦ])
      (fun σ : E →+* ℂ => (D.p : ℂ) * σ (a : E) + (D.q : ℂ) * conj (σ (a : E)))).symm
  have hJe : ∀ x, e.conj J (e x) = e (J x) := fun x => by simp [LinearEquiv.conj_apply]
  have hcomm : ∀ (c : Φ → ℂ) u, e.conj J (c • u) = c • e.conj J u := by
    refine induction_integers Φ _ ?_ ?_ ?_
    · intro a u
      obtain ⟨x, rfl⟩ := e.surjective u
      rw [hJe, he, he, ← realMap_realAct, ← realMap_realAct, ← he, ← he, hJe]
      exact congrArg e (LinearMap.congr_fun (hA a).1 x)
    · intro c c' h h' u
      rw [add_smul, map_add, h, h', add_smul]
    · intro t c h u
      rw [smul_assoc, map_smul, h, smul_assoc]
  obtain ⟨M, hM⟩ := exists_blocks (e.conj J) hcomm
  have hMe : ∀ x σ, realMap D Φ φ (J x) σ = M σ *ᵥ realMap D Φ φ x σ := fun x σ => by
    rw [← he, ← he, ← hJe, hM]
  have hsingle : ∀ u : Fin r → ℂ, realMap D Φ φ (e.symm (Pi.single τ u)) = Pi.single τ u :=
    fun u => e.apply_symm_apply _
  have hsum : ∀ (f : Φ → ℝ), (∀ σ, σ ≠ τ → f σ = 0) → ∑ σ, f σ = f τ := fun f hf =>
    Finset.sum_eq_single τ (fun σ _ h => hf σ h) (by simp)
  clear hJ hcomm
  refine ⟨?_, M τ, ?_, ?_, ?_, ?_⟩
  · have h1 := (hA 1).2.1
    rw [← LinearMap.trace_conj' _ e, trace_real_blocks (fun _ => 1) _ (fun u σ => by
      obtain ⟨x, rfl⟩ := e.surjective u
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      simp [he, realMap_realAct])] at h1
    have hc : (Fintype.card Φ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp at h1
    have : (r : ℝ) = D.p + D.q := mul_left_cancel₀ hc (by linarith)
    exact_mod_cast this
  · refine toLin'.injective (LinearMap.ext fun u => ?_)
    have := hMe (J (e.symm (Pi.single τ u))) τ
    rw [hJ2, hMe, map_neg, hsingle] at this
    simpa [neg_mulVec] using this.symm
  · intro u v
    have := hJinv (e.symm (Pi.single τ u)) (e.symm (Pi.single τ v))
    rw [hform, hform, hsum _ (fun σ h => by simp [hMe, hsingle, h]),
      hsum _ (fun σ h => by simp [hsingle, h]), hMe, hMe, hsingle, hsingle] at this
    simp only [Pi.single_eq_same] at this
    linarith
  · intro u hu
    have := hJpos (e.symm (Pi.single τ u)) (by simpa using hu)
    rw [hform, hsum _ (fun σ h => by simp [hsingle, h]), hMe, hsingle] at this
    simp only [Pi.single_eq_same] at this
    linarith
  · have := Φ.eq_zero_of_sum_re_eq_zero
      (fun σ => (M σ).trace - Complex.I * ((D.p : ℂ) - D.q)) fun a => by
        have h1 := (hA a).2.2
        rw [← LinearMap.trace_conj' _ e, trace_real_blocks (fun σ => σ.1 (a : E) • M σ) _
          (fun u σ => by
            obtain ⟨x, rfl⟩ := e.surjective u
            simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
              LinearEquiv.symm_apply_apply]
            simp only [he, hMe, realMap_realAct, Pi.smul_apply', mulVec_smul, smul_mulVec]), Complex.im_sum, Finset.mul_sum,
          ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
        have h2 : 2 * ∑ σ : Φ, (σ.1 (a : E) *
            ((M σ).trace - Complex.I * ((D.p : ℂ) - D.q))).re = 0 := by
          rw [← h1, Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp [trace_smul]
          ring
        linarith
    exact sub_eq_zero.1 (congrFun this τ)

end Main

/- English proof (translation)
Take `⟨-, hspan, hherm, -, hEF⟩` from `hm`. Take `⟨hr, M, hM, hinv, hpos, htr⟩` from `exists_complexStructure D (hostType H) φ ξ Gm hspan hEF (fun _ => Iff.rfl) ⟨τ, hτ⟩`. Establish `hG : (Gm.map τ).IsHermitian`. Use extensionality with `a b`. Rewrite using `[conjTranspose_apply, map_apply, map_apply, ← hherm b a, FD.cc, IsCMField.complexEmbedding_complexConj]`.

Both sides reduce to the same expression. Establish `hre : τ ξ = ((τ ξ).im : ℂ) * Complex.I`. Establish `h` using `congrArg τ hξ`. Rewrite `h` using `[FD.cc, IsCMField.complexEmbedding_complexConj, map_neg]`. Use `congrArg Complex.re h` as an intermediate fact.

Simplify using `only [Complex.conj_re, Complex.neg_re] at this`. Apply the tactic sequence `apply Complex.ext <;> simp`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only at hinv hpos`. Rewrite `hinv`, `hpos` using `[hre]`.

Establish `fin : ∀ m : ℕ, (∃ N : Matrix (Fin r) (Fin r) ℂ, N.det ≠ 0 ∧ Nᴴ * Gm.map τ * N = diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ)) → ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ)`. Introduce and unpack `m ⟨N, hN, h⟩`. Use `⟨N.map conj, ?_, by rw [gram_eq, h]⟩` and prove the remaining obligations. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Simplify using `using hN`.

Use `⟨fun hs => fin _ ?_, fun hs => fin _ ?_⟩` and prove the remaining obligations. Use `exists_diag_of_complexStructure (n := D.p) (by omega) _ M hG _ 1 (by norm_num) (by simpa using hs) hM hinv hpos ?_` and prove the remaining obligations. Rewrite using `[htr]`. Use `push_cast`. Take the linear combination `((D.p : ℂ) - D.q) * Complex.I_mul_I`.

Use `exists_diag_of_complexStructure (n := D.q) hr _ M hG _ (-1) (by norm_num) (by simpa using hs) hM hinv hpos ?_` and prove the remaining obligations. Rewrite using `[htr]`. Use `push_cast`. Take the linear combination `(-((D.p : ℂ) - D.q)) * Complex.I_mul_I`.
-/
theorem signature_of_model (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hξ : FD.cc ξ = -ξ)
    (hm : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) :
    (0 < (τ ξ).im → (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q =
      Matrix.diagonal fun a : Fin r => ((FD.sgn D.q (a : ℕ) : ℝ) : ℂ))) ∧
    ((τ ξ).im < 0 → (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q =
      Matrix.diagonal fun a : Fin r => ((FD.sgn D.p (a : ℕ) : ℝ) : ℂ))) := by
  obtain ⟨-, hspan, hherm, -, hEF⟩ := hm
  obtain ⟨hr, M, hM, hinv, hpos, htr⟩ := exists_complexStructure D (hostType H) φ ξ Gm hspan hEF
    (fun _ => Iff.rfl) ⟨τ, hτ⟩
  have hG : (Gm.map τ).IsHermitian := by
    ext a b
    rw [conjTranspose_apply, map_apply, map_apply, ← hherm b a, FD.cc,
      IsCMField.complexEmbedding_complexConj]
    rfl
  have hre : τ ξ = ((τ ξ).im : ℂ) * Complex.I := by
    have h := congrArg τ hξ
    rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg] at h
    have := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.neg_re] at this
    apply Complex.ext <;> simp
    linarith
  dsimp only at hinv hpos
  rw [hre] at hinv hpos
  have fin : ∀ m : ℕ, (∃ N : Matrix (Fin r) (Fin r) ℂ, N.det ≠ 0 ∧
      Nᴴ * Gm.map τ * N = diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ)) →
      ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q =
        Matrix.diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ) := by
    rintro m ⟨N, hN, h⟩
    refine ⟨N.map conj, ?_, by rw [gram_eq, h]⟩
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hN
  refine ⟨fun hs => fin _ ?_, fun hs => fin _ ?_⟩
  · refine exists_diag_of_complexStructure (n := D.p) (by omega) _ M hG _ 1 (by norm_num)
      (by simpa using hs) hM hinv hpos ?_
    rw [htr]; push_cast
    linear_combination ((D.p : ℂ) - D.q) * Complex.I_mul_I
  · refine exists_diag_of_complexStructure (n := D.q) hr _ M hG _ (-1) (by norm_num)
      (by simpa using hs) hM hinv hpos ?_
    rw [htr]; push_cast
    linear_combination (-((D.p : ℂ) - D.q)) * Complex.I_mul_I

end GlobalTheory.HermSign
