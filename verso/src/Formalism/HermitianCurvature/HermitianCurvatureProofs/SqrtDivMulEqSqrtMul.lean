import Formalism.HermitianCurvature.HermitianCurvatureProofs.HcoSmulRight

namespace Formalism.FourierDecayAlt.P.PBI

open Finset Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

section xblock

variable {r : ℕ} (T T' : ℝ) (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)

/- English proof (translation)
Establish `h` using `congrFun (congrFun (Matrix.mul_adjugate Zm) a) (Fin.last r)`. Simplify using `only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h`. Unfold `kap`. Rewrite using `[h]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mul_kap (a : Fin (r + 1)) : ∑ b, Zm a b * kap Zm b = if a = Fin.last r then Zm.det else 0 := by
  have h := congrFun (congrFun (Matrix.mul_adjugate Zm) a) (Fin.last r)
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  unfold kap
  rw [h]
  split_ifs <;> simp

/- English proof (translation)
Unfold `kap`. Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]`. Simplify using `[← two_mul, pow_mul]`.
-/
theorem kap_last : kap Zm (Fin.last r) = (Zm.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold kap
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp [← two_mul, pow_mul]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, kap Zm b ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h2` using `mul_kap Zm (Fin.last r)`. Simplify using `[h] at h2`.

Use `first`. Consider the case `exact hdet h2.symm`. Consider the case `exact hdet h2`. Conclude with `Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨b, Finset.mem_univ _, Complex.normSq_pos.mpr hb⟩`.
-/
theorem nk_pos (hdet : Zm.det ≠ 0) : 0 < nk Zm := by
  obtain ⟨b, hb⟩ : ∃ b, kap Zm b ≠ 0 := by
    by_contra h
    push_neg at h
    have h2 := mul_kap Zm (Fin.last r)
    simp [h] at h2
    first
      | exact hdet h2.symm
      | exact hdet h2
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨b, Finset.mem_univ _, Complex.normSq_pos.mpr hb⟩

/- English proof (translation)
Establish `h` using `mul_kap Zm (Fin.last r)`. Rewrite `h` using `[if_pos rfl]`. Rewrite using `[neg_div, ← h, Finset.sum_div, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Unfold `al`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_kap_al (hT : 0 < T) (hT' : 0 < T') :
    ∑ b, kap Zm b * al T T' Zm b = -Zm.det / ((Real.sqrt (T * T') : ℝ) : ℂ) := by
  have h := mul_kap Zm (Fin.last r)
  rw [if_pos rfl] at h
  rw [neg_div, ← h, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  unfold al
  ring

/- English proof (translation)
Establish `hnk : ((nk Zm : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (nk_pos Zm hdet).ne'`. Unfold `be`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_div, Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Use `_ = ((nk Zm : ℝ) : ℂ) / ((nk Zm : ℝ) : ℂ) * ((sGT T T' Zm : ℝ) : ℂ) * ph Zm := by`. Simplify using `only [Complex.mul_conj]`. Rewrite using `[← Complex.ofReal_sum]`. Both sides reduce to the same expression.

Use `_ = ((sGT T T' Zm : ℝ) : ℂ) * ph Zm := by rw [div_self hnk, one_mul]`.
-/
theorem sum_kap_be (hdet : Zm.det ≠ 0) :
    ∑ b, kap Zm b * be T T' Zm b = ((sGT T T' Zm : ℝ) : ℂ) * ph Zm := by
  have hnk : ((nk Zm : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nk_pos Zm hdet).ne'
  unfold be
  calc ∑ b, kap Zm b * (conj (kap Zm b) / ((nk Zm : ℝ) : ℂ) * ((sGT T T' Zm : ℝ) : ℂ) * ph Zm)
      = (∑ b, kap Zm b * conj (kap Zm b)) / ((nk Zm : ℝ) : ℂ) * ((sGT T T' Zm : ℝ) : ℂ) * ph Zm := by
        rw [Finset.sum_div, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = ((nk Zm : ℝ) : ℂ) / ((nk Zm : ℝ) : ℂ) * ((sGT T T' Zm : ℝ) : ℂ) * ph Zm := by
        simp only [Complex.mul_conj]
        rw [← Complex.ofReal_sum]
        rfl
    _ = ((sGT T T' Zm : ℝ) : ℂ) * ph Zm := by rw [div_self hnk, one_mul]

/- English proof (translation)
Establish `h1 : T * T' = (T / T') * T' ^ 2`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Rewrite using `[h1, Real.sqrt_mul (div_nonneg hT.le hT'.le), Real.sqrt_sq hT'.le]`.
-/
theorem sqrt_div_mul_eq_sqrt_mul (hT : 0 < T) (hT' : 0 < T') : Real.sqrt (T / T') * T' = Real.sqrt (T * T') := by
  have h1 : T * T' = (T / T') * T' ^ 2 := by
    field_simp
    try ring
  rw [h1, Real.sqrt_mul (div_nonneg hT.le hT'.le), Real.sqrt_sq hT'.le]

/- English proof (translation)
Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Establish `hne : ∀ a : Fin r, ¬ (Fin.last r = a.castSucc)` using `fun a h => (Fin.castSucc_lt_last a).ne' h`. Establish `hs : ((Real.sqrt (T * T') : ℝ) : ℂ) ≠ 0`. Conclude with `(Real.sqrt_pos.mpr (mul_pos hT hT')).ne'` after adjusting the coercions.

Establish `key : (T' : ℂ) * ((Real.sqrt (T / T') : ℝ) : ℂ) = ((Real.sqrt (T * T') : ℝ) : ℂ)`. Rewrite using `[mul_comm]`. Conclude with `sqrt_div_mul_eq_sqrt_mul T T' hT hT'` after adjusting the coercions. Simplify using `[hco, xco, fco, al, hne]`. Rewrite using `[show -((T' : ℂ) * (-Zm (Fin.last r) b / ((Real.sqrt (T * T') : ℝ) : ℂ)) * ((Real.sqrt (T / T') : ℝ) : ℂ)) = Zm (Fin.last r) b * ((T' : ℂ) * ((Real.sqrt (T / T') : ℝ) : ℂ)) / ((Real.sqrt (T * T') : ℝ) : ℂ) by ring, key, mul_div_assoc, div_self hs, mul_one]`.

Consider the case `cast a0`. Simplify using `[hco, xco, fco, al]`.
-/
theorem xco_fco (hT : 0 < T) (hT' : 0 < T') (hdet : Zm.det ≠ 0) (a b : Fin (r + 1)) :
    hco T' (xco T T' Zm b) (fco T T' a) = Zm a b := by
  induction a using Fin.lastCases with
  | last =>
    have hne : ∀ a : Fin r, ¬ (Fin.last r = a.castSucc) := fun a h => (Fin.castSucc_lt_last a).ne' h
    have hs : ((Real.sqrt (T * T') : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (mul_pos hT hT')).ne'
    have key : (T' : ℂ) * ((Real.sqrt (T / T') : ℝ) : ℂ) = ((Real.sqrt (T * T') : ℝ) : ℂ) := by
      rw [mul_comm]
      exact_mod_cast sqrt_div_mul_eq_sqrt_mul T T' hT hT'
    simp [hco, xco, fco, al, hne]
    rw [show -((T' : ℂ) * (-Zm (Fin.last r) b / ((Real.sqrt (T * T') : ℝ) : ℂ)) *
        ((Real.sqrt (T / T') : ℝ) : ℂ)) = Zm (Fin.last r) b * ((T' : ℂ) * ((Real.sqrt (T / T') : ℝ) : ℂ)) /
        ((Real.sqrt (T * T') : ℝ) : ℂ) by ring, key, mul_div_assoc, div_self hs, mul_one]
  | cast a0 =>
    simp [hco, xco, fco, al]

end xblock

section gram

variable {r : ℕ} (T T' : ℝ) (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)

/- English proof (translation)
Establish `hAp : ∀ b c : Fin (r + 1), star (Ap T' c b) = Ap T' b c`. Introduce `b c`. Unfold `Ap`. Distinguish the cases in `h : b = Fin.last r ∧ c = Fin.last r`. Rewrite using `[if_pos ⟨h.2, h.1⟩, if_pos h]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h, star_zero]`. Establish `hH : ∀ b c : Fin (r + 1), star (Heta T T' Zm c b) = Heta T T' Zm b c`. Introduce `b c`. Unfold `Heta`.

Simplify using `only [star_add, star_mul', star_neg, Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `c b`. Simplify using `only [Matrix.conjTranspose_apply, Rm, Matrix.of_apply, star_sub, hAp, hH]`.
-/
theorem Rm_herm : (Rm T T' Zm)ᴴ = Rm T T' Zm := by
  have hAp : ∀ b c : Fin (r + 1), star (Ap T' c b) = Ap T' b c := by
    intro b c
    unfold Ap
    by_cases h : b = Fin.last r ∧ c = Fin.last r
    · rw [if_pos ⟨h.2, h.1⟩, if_pos h]
      simp
    · rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h, star_zero]
  have hH : ∀ b c : Fin (r + 1), star (Heta T T' Zm c b) = Heta T T' Zm b c := by
    intro b c
    unfold Heta
    simp only [star_add, star_mul', star_neg, Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]
    ring
  ext c b
  simp only [Matrix.conjTranspose_apply, Rm, Matrix.of_apply, star_sub, hAp, hH]

/- English proof (translation)
Use extensionality with `c b`. Simplify using `only [Matrix.conjTranspose_apply, Qm, Matrix.of_apply, star_div₀, star_mul', Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Qm_herm : (Qm Zm)ᴴ = Qm Zm := by
  ext c b
  simp only [Matrix.conjTranspose_apply, Qm, Matrix.of_apply, star_div₀, star_mul', Complex.star_def,
    Complex.conj_conj, Complex.conj_ofReal]
  ring

/- English proof (translation)
Rewrite using `[Pm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Qm_herm]`.
-/
theorem Pm_herm : (Pm Zm)ᴴ = Pm Zm := by
  rw [Pm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Qm_herm]

/- English proof (translation)
Establish `hs : star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Unfold `Km`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Pm_herm, Rm_herm, Qm_herm, hs]`. Rewrite using `[← Matrix.mul_assoc (Pm Zm) (Rm T T' Zm) (Pm Zm), ← Matrix.mul_assoc (Qm Zm) (Rm T T' Zm) (Pm Zm)]`. Establish `e : (1 / 2 : ℂ) • (Pm Zm * Rm T T' Zm * Pm Zm) + Pm Zm * Rm T T' Zm * Qm Zm + ((1 / 2 : ℂ) • (Pm Zm * Rm T T' Zm * Pm Zm) + Qm Zm * Rm T T' Zm * Pm Zm) = Pm Zm * Rm T T' Zm * Pm Zm + Pm Zm * Rm T T' Zm * Qm Zm + Qm Zm * Rm T T' Zm * Pm Zm` using `by module`.

Rewrite using `[e, Pm]`. Use `noncomm_ring`.
-/
theorem Km_add : Km T T' Zm + (Km T T' Zm)ᴴ = Rm T T' Zm - Qm Zm * Rm T T' Zm * Qm Zm := by
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  unfold Km
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Pm_herm, Rm_herm,
    Qm_herm, hs]
  rw [← Matrix.mul_assoc (Pm Zm) (Rm T T' Zm) (Pm Zm), ← Matrix.mul_assoc (Qm Zm) (Rm T T' Zm) (Pm Zm)]
  have e : (1 / 2 : ℂ) • (Pm Zm * Rm T T' Zm * Pm Zm) + Pm Zm * Rm T T' Zm * Qm Zm +
      ((1 / 2 : ℂ) • (Pm Zm * Rm T T' Zm * Pm Zm) + Qm Zm * Rm T T' Zm * Pm Zm) =
      Pm Zm * Rm T T' Zm * Pm Zm + Pm Zm * Rm T T' Zm * Qm Zm + Qm Zm * Rm T T' Zm * Pm Zm := by
    module
  rw [e, Pm]
  noncomm_ring

/- English proof (translation)
Establish `hnk : ((nk Zm : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (nk_pos Zm hdet).ne'`. Establish `hsum : ∑ d, conj (kap Zm d) * kap Zm d = ((nk Zm : ℝ) : ℂ)`. Simplify using `only [← Complex.normSq_eq_conj_mul_self]`. Rewrite using `[← Complex.ofReal_sum]`. Both sides reduce to the same expression.

Simplify using `only [Pm, Matrix.sub_apply, Matrix.one_apply, Qm, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `h2 : ∑ d, conj (kap Zm d) * (kap Zm d * conj (kap Zm e) / ((nk Zm : ℝ) : ℂ)) = (∑ d, conj (kap Zm d) * kap Zm d) * conj (kap Zm e) / ((nk Zm : ℝ) : ℂ)`. Rewrite using `[Finset.sum_mul, Finset.sum_div]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2, hsum, mul_comm ((nk Zm : ℝ) : ℂ), mul_div_assoc, div_self hnk, mul_one, sub_self]`.
-/
theorem kap_Pm (hdet : Zm.det ≠ 0) (e : Fin (r + 1)) : ∑ d, conj (kap Zm d) * Pm Zm d e = 0 := by
  have hnk : ((nk Zm : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nk_pos Zm hdet).ne'
  have hsum : ∑ d, conj (kap Zm d) * kap Zm d = ((nk Zm : ℝ) : ℂ) := by
    simp only [← Complex.normSq_eq_conj_mul_self]
    rw [← Complex.ofReal_sum]
    rfl
  simp only [Pm, Matrix.sub_apply, Matrix.one_apply, Qm, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : ∑ d, conj (kap Zm d) * (kap Zm d * conj (kap Zm e) / ((nk Zm : ℝ) : ℂ)) =
      (∑ d, conj (kap Zm d) * kap Zm d) * conj (kap Zm e) / ((nk Zm : ℝ) : ℂ) := by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  rw [h2, hsum, mul_comm ((nk Zm : ℝ) : ℂ), mul_div_assoc, div_self hnk, mul_one, sub_self]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero (fun e _ => ?_)` and prove the remaining obligations. Repeatedly rewrite using `[← mul_assoc]`. Rewrite using `[← Finset.sum_mul, kap_Pm Zm hdet e, zero_mul]`.
-/
theorem kap_Pm_mul (hdet : Zm.det ≠ 0) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (b : Fin (r + 1)) :
    ∑ d, conj (kap Zm d) * (Pm Zm * X) d b = 0 := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun e _ => ?_)
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, kap_Pm Zm hdet e, zero_mul]

/- English proof (translation)
Establish `h : Km T T' Zm = Pm Zm * ((1 / 2 : ℂ) • (Rm T T' Zm * Pm Zm) + Rm T T' Zm * Qm Zm)`. Simplify using `only [Km, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]`. Rewrite using `[h]`. Conclude with `kap_Pm_mul Zm hdet _ b`.
-/
theorem kap_Km (hdet : Zm.det ≠ 0) (b : Fin (r + 1)) : ∑ d, conj (kap Zm d) * Km T T' Zm d b = 0 := by
  have h : Km T T' Zm = Pm Zm * ((1 / 2 : ℂ) • (Rm T T' Zm * Pm Zm) + Rm T T' Zm * Qm Zm) := by
    simp only [Km, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]
  rw [h]
  exact kap_Pm_mul Zm hdet _ b

/- English proof (translation)
Establish `hn : ((‖Zm.det‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.mpr hdet`. Unfold `ph`. Rewrite using `[map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Rewrite using `[sq, div_self (mul_ne_zero hn hn)]`.
-/
theorem ph_conj (hdet : Zm.det ≠ 0) : ph Zm * conj (ph Zm) = 1 := by
  have hn : ((‖Zm.det‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hdet
  unfold ph
  rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [sq, div_self (mul_ne_zero hn hn)]

/- English proof (translation)
Use `set k := kap Zm with hkdef`. Establish `key : ∀ u : Fin (r + 1) → ℂ, ∑ d, ∑ e, conj (k d) * (u e * conj (u d)) * k e = (∑ e, k e * u e) * conj (∑ d, k d * u d)`. Introduce `u`. Rewrite using `[map_sum, Finset.sum_mul_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))` and prove the remaining obligations.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA : ∑ d, ∑ e, conj (k d) * Ap T' e d * k e = -((T' : ℝ) : ℂ) * (conj (k (Fin.last r)) * k (Fin.last r))`. Rewrite using `[Fintype.sum_eq_single (Fin.last r)]`. Rewrite using `[Fintype.sum_eq_single (Fin.last r)]`.

Simplify using `only [Ap, and_self, if_true]`. Expand and normalize the polynomial expressions, which then agree. Introduce `e he`. Simplify using `[Ap, he]`. Introduce `d hd`.

Use `Finset.sum_eq_zero (fun e _ => ?_)` and prove the remaining obligations. Simplify using `[Ap, hd]`. Establish `hB : ∑ d, ∑ e, conj (k d) * Heta T T' Zm e d * k e = -((T' : ℝ) : ℂ) * ((∑ e, k e * al T T' Zm e) * conj (∑ d, k d * al T T' Zm d)) + (∑ e, k e * be T T' Zm e) * conj (∑ d, k d * be T T' Zm d)`. Rewrite using `[← key, ← key, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun e _ => ?_)` and prove the remaining obligations. Unfold `Heta`. Expand and normalize the polynomial expressions, which then agree. Establish `hsplit : ∑ d, ∑ e, conj (k d) * Rm T T' Zm d e * k e = ∑ d, ∑ e, conj (k d) * Ap T' e d * k e - ∑ d, ∑ e, conj (k d) * Heta T T' Zm e d * k e`.

Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl (fun e _ => ?_)` and prove the remaining obligations. Simplify using `only [Rm, Matrix.of_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hal` using `sum_kap_al T T' Zm hT hT'`. Establish `hbe` using `sum_kap_be T T' Zm hdet`. Establish `hph` using `ph_conj Zm hdet`. Establish `hkl : k (Fin.last r) = (Zm.submatrix Fin.castSucc Fin.castSucc).det` using `kap_last Zm`.

Establish `hsq : ((Real.sqrt (T * T') : ℝ) : ℂ) * ((Real.sqrt (T * T') : ℝ) : ℂ) = ((T * T' : ℝ) : ℂ)`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (mul_pos hT hT').le]`. Establish `hg : ((sGT T T' Zm : ℝ) : ℂ) * ((sGT T T' Zm : ℝ) : ℂ) = ((gPoly (T * T') Zm / T : ℝ) : ℂ)`. Rewrite using `[← Complex.ofReal_mul, sGT, Real.mul_self_sqrt (div_pos hG hT).le]`. Establish `hs0 : ((Real.sqrt (T * T') : ℝ) : ℂ) ≠ 0`.

Conclude with `(Real.sqrt_pos.mpr (mul_pos hT hT')).ne'` after adjusting the coercions. Establish `hT0 : ((T : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hT.ne'`. Establish `hT'0 : ((T' : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hT'.ne'`. Rewrite using `[hsplit, hA, hB, hal, hbe, hkl]`. Simplify using `only [map_mul, map_div₀, map_neg, Complex.conj_ofReal]`.

Establish `e1 : (Zm.submatrix Fin.castSucc Fin.castSucc).det * conj (Zm.submatrix Fin.castSucc Fin.castSucc).det = ((Complex.normSq (Zm.submatrix Fin.castSucc Fin.castSucc).det : ℝ) : ℂ)` using `Complex.mul_conj _`. Establish `e2 : Zm.det * conj Zm.det = ((Complex.normSq Zm.det : ℝ) : ℂ)` using `Complex.mul_conj _`. Establish `e3 : conj (Zm.submatrix Fin.castSucc Fin.castSucc).det * (Zm.submatrix Fin.castSucc Fin.castSucc).det = ((Complex.normSq (Zm.submatrix Fin.castSucc Fin.castSucc).det : ℝ) : ℂ)`. Rewrite using `[mul_comm]`. Conclude with `e1`.

Unfold `gPoly at hg`. Move the coercions through the operations in `at hg hsq e1 e2 e3`. Rewrite using `[e3]`. Establish `eA : -Zm.det / ((Real.sqrt (T * T') : ℝ) : ℂ) * (-conj Zm.det / ((Real.sqrt (T * T') : ℝ) : ℂ)) = ((Complex.normSq Zm.det : ℝ) : ℂ) / ((T : ℂ) * (T' : ℂ))`. Rewrite using `[show -Zm.det / ((Real.sqrt (T * T') : ℝ) : ℂ) * (-conj Zm.det / ((Real.sqrt (T * T') : ℝ) : ℂ)) = (Zm.det * conj Zm.det) / (((Real.sqrt (T * T') : ℝ) : ℂ) * ((Real.sqrt (T * T') : ℝ) : ℂ)) by ring, e2, hsq]`.

Establish `eB : ((sGT T T' Zm : ℝ) : ℂ) * ph Zm * (((sGT T T' Zm : ℝ) : ℂ) * conj (ph Zm)) = (((sGT T T' Zm : ℝ) : ℂ) * ((sGT T T' Zm : ℝ) : ℂ)) * (ph Zm * conj (ph Zm))` using `by ring`. Rewrite using `[eA, eB, hph, hg, mul_one]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_zero (hT : 0 < T) (hT' : 0 < T') (hdet : Zm.det ≠ 0) (hG : 0 < gPoly (T * T') Zm) :
    ∑ d, ∑ e, conj (kap Zm d) * Rm T T' Zm d e * kap Zm e = 0 := by
  set k := kap Zm with hkdef
  have key : ∀ u : Fin (r + 1) → ℂ, ∑ d, ∑ e, conj (k d) * (u e * conj (u d)) * k e =
      (∑ e, k e * u e) * conj (∑ d, k d * u d) := by
    intro u
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
    rw [map_mul]
    ring
  have hA : ∑ d, ∑ e, conj (k d) * Ap T' e d * k e = -((T' : ℝ) : ℂ) * (conj (k (Fin.last r)) * k (Fin.last r)) := by
    rw [Fintype.sum_eq_single (Fin.last r)]
    · rw [Fintype.sum_eq_single (Fin.last r)]
      · simp only [Ap, and_self, if_true]
        ring
      · intro e he
        simp [Ap, he]
    · intro d hd
      refine Finset.sum_eq_zero (fun e _ => ?_)
      simp [Ap, hd]
  have hB : ∑ d, ∑ e, conj (k d) * Heta T T' Zm e d * k e =
      -((T' : ℝ) : ℂ) * ((∑ e, k e * al T T' Zm e) * conj (∑ d, k d * al T T' Zm d)) +
        (∑ e, k e * be T T' Zm e) * conj (∑ d, k d * be T T' Zm d) := by
    rw [← key, ← key, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    unfold Heta
    ring
  have hsplit : ∑ d, ∑ e, conj (k d) * Rm T T' Zm d e * k e =
      ∑ d, ∑ e, conj (k d) * Ap T' e d * k e - ∑ d, ∑ e, conj (k d) * Heta T T' Zm e d * k e := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [Rm, Matrix.of_apply]
    ring
  have hal := sum_kap_al T T' Zm hT hT'
  have hbe := sum_kap_be T T' Zm hdet
  have hph := ph_conj Zm hdet
  have hkl : k (Fin.last r) = (Zm.submatrix Fin.castSucc Fin.castSucc).det := kap_last Zm
  have hsq : ((Real.sqrt (T * T') : ℝ) : ℂ) * ((Real.sqrt (T * T') : ℝ) : ℂ) = ((T * T' : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (mul_pos hT hT').le]
  have hg : ((sGT T T' Zm : ℝ) : ℂ) * ((sGT T T' Zm : ℝ) : ℂ) = ((gPoly (T * T') Zm / T : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, sGT, Real.mul_self_sqrt (div_pos hG hT).le]
  have hs0 : ((Real.sqrt (T * T') : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos hT hT')).ne'
  have hT0 : ((T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hT'0 : ((T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  rw [hsplit, hA, hB, hal, hbe, hkl]
  simp only [map_mul, map_div₀, map_neg, Complex.conj_ofReal]
  have e1 : (Zm.submatrix Fin.castSucc Fin.castSucc).det * conj (Zm.submatrix Fin.castSucc Fin.castSucc).det =
      ((Complex.normSq (Zm.submatrix Fin.castSucc Fin.castSucc).det : ℝ) : ℂ) := Complex.mul_conj _
  have e2 : Zm.det * conj Zm.det = ((Complex.normSq Zm.det : ℝ) : ℂ) := Complex.mul_conj _
  have e3 : conj (Zm.submatrix Fin.castSucc Fin.castSucc).det * (Zm.submatrix Fin.castSucc Fin.castSucc).det =
      ((Complex.normSq (Zm.submatrix Fin.castSucc Fin.castSucc).det : ℝ) : ℂ) := by
    rw [mul_comm]; exact e1
  unfold gPoly at hg
  push_cast at hg hsq e1 e2 e3
  rw [e3]
  have eA : -Zm.det / ((Real.sqrt (T * T') : ℝ) : ℂ) * (-conj Zm.det / ((Real.sqrt (T * T') : ℝ) : ℂ)) =
      ((Complex.normSq Zm.det : ℝ) : ℂ) / ((T : ℂ) * (T' : ℂ)) := by
    rw [show -Zm.det / ((Real.sqrt (T * T') : ℝ) : ℂ) * (-conj Zm.det / ((Real.sqrt (T * T') : ℝ) : ℂ)) =
      (Zm.det * conj Zm.det) / (((Real.sqrt (T * T') : ℝ) : ℂ) * ((Real.sqrt (T * T') : ℝ) : ℂ)) by ring,
      e2, hsq]
  have eB : ((sGT T T' Zm : ℝ) : ℂ) * ph Zm * (((sGT T T' Zm : ℝ) : ℂ) * conj (ph Zm)) =
      (((sGT T T' Zm : ℝ) : ℂ) * ((sGT T T' Zm : ℝ) : ℂ)) * (ph Zm * conj (ph Zm)) := by ring
  rw [eA, eB, hph, hg, mul_one]
  field_simp
  ring

/- English proof (translation)
Use extensionality with `c b`. Establish `h : (Qm Zm * Rm T T' Zm * Qm Zm) c b = kap Zm c * conj (kap Zm b) / (((nk Zm : ℝ) : ℂ) * ((nk Zm : ℝ) : ℂ)) * ∑ d, ∑ e, conj (kap Zm d) * Rm T T' Zm d e * kap Zm e`. Simplify using `only [Matrix.mul_apply, Qm, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, quad_zero T T' Zm hT hT' hdet hG, mul_zero, Matrix.zero_apply]`.
-/
theorem QRQ_zero (hT : 0 < T) (hT' : 0 < T') (hdet : Zm.det ≠ 0) (hG : 0 < gPoly (T * T') Zm) :
    Qm Zm * Rm T T' Zm * Qm Zm = 0 := by
  ext c b
  have h : (Qm Zm * Rm T T' Zm * Qm Zm) c b = kap Zm c * conj (kap Zm b) / (((nk Zm : ℝ) : ℂ) * ((nk Zm : ℝ) : ℂ)) *
      ∑ d, ∑ e, conj (kap Zm d) * Rm T T' Zm d e * kap Zm e := by
    simp only [Matrix.mul_apply, Qm, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
    ring
  rw [h, quad_zero T T' Zm hT hT' hdet hG, mul_zero, Matrix.zero_apply]

/- English proof (translation)
Establish `h` using `kap_Km T T' Zm hdet b`. Unfold `Mf`. Rewrite using `[Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations.

Rewrite using `[Matrix.conjTranspose_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', star_mul']`. Unfold `kap`. Simplify using `only [Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [← Finset.mul_sum, h, mul_zero]`.
-/
theorem Mf_last (hdet : Zm.det ≠ 0) (b : Fin (r + 1)) : Mf T T' Zm (Fin.last r) b = 0 := by
  have h := kap_Km T T' Zm hdet b
  unfold Mf
  rw [Matrix.mul_apply]
  calc ∑ d, (Zm⁻¹)ᴴ (Fin.last r) d * Km T T' Zm d b
      = ∑ d, star (Zm.det⁻¹) * (conj (kap Zm d) * Km T T' Zm d b) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Matrix.conjTranspose_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
          Ring.inverse_eq_inv', star_mul']
        unfold kap
        simp only [Complex.star_def]
        ring
    _ = 0 := by rw [← Finset.mul_sum, h, mul_zero]

/- English proof (translation)
Establish `hdetU : IsUnit Zm.det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `hfull : ∑ a : Fin (r + 1), Mf T T' Zm a b * conj (Zm a c) = Km T T' Zm c b`. Establish `h1 : (Zmᴴ * Mf T T' Zm) c b = Km T T' Zm c b`. Unfold `Mf`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hdetU, Matrix.conjTranspose_one, Matrix.one_mul]`.

Rewrite using `[← h1, Matrix.mul_apply]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_apply, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hfull, Fin.sum_univ_castSucc, Mf_last T T' Zm hdet b, zero_mul, add_zero]`.
-/
theorem Mf_Z (hdet : Zm.det ≠ 0) (b c : Fin (r + 1)) :
    ∑ a : Fin r, Mf T T' Zm a.castSucc b * conj (Zm a.castSucc c) = Km T T' Zm c b := by
  have hdetU : IsUnit Zm.det := isUnit_iff_ne_zero.mpr hdet
  have hfull : ∑ a : Fin (r + 1), Mf T T' Zm a b * conj (Zm a c) = Km T T' Zm c b := by
    have h1 : (Zmᴴ * Mf T T' Zm) c b = Km T T' Zm c b := by
      unfold Mf
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hdetU,
        Matrix.conjTranspose_one, Matrix.one_mul]
    rw [← h1, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.conjTranspose_apply, Complex.star_def]
    ring
  rw [← hfull, Fin.sum_univ_castSucc, Mf_last T T' Zm hdet b, zero_mul, add_zero]

/- English proof (translation)
Establish `h1` using `Mf_Z T T' Zm hdet b c`. Establish `h2` using `Mf_Z T T' Zm hdet c b`. Establish `h3 : Km T T' Zm + (Km T T' Zm)ᴴ = Rm T T' Zm`. Rewrite using `[Km_add, QRQ_zero T T' Zm hT hT' hdet hG, sub_zero]`. Establish `h4` using `congrFun (congrFun h3 c) b`.

Simplify using `only [Matrix.add_apply, Matrix.conjTranspose_apply, Rm, Matrix.of_apply, Complex.star_def] at h4`. Establish `h5 : ∑ a : Fin r, Zm a.castSucc b * conj (Mf T T' Zm a.castSucc c) = conj (Km T T' Zm b c)`. Rewrite using `[← h2, map_sum]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, Complex.conj_conj]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hco, xco]`. Rewrite using `[h1, h5]`. Unfold `Heta at h4`. Take the linear combination `h4`.
-/
theorem xco_gram (hT : 0 < T) (hT' : 0 < T') (hdet : Zm.det ≠ 0) (hG : 0 < gPoly (T * T') Zm)
    (b c : Fin (r + 1)) : hco T' (xco T T' Zm b) (xco T T' Zm c) = Ap T' b c := by
  have h1 := Mf_Z T T' Zm hdet b c
  have h2 := Mf_Z T T' Zm hdet c b
  have h3 : Km T T' Zm + (Km T T' Zm)ᴴ = Rm T T' Zm := by
    rw [Km_add, QRQ_zero T T' Zm hT hT' hdet hG, sub_zero]
  have h4 := congrFun (congrFun h3 c) b
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Rm, Matrix.of_apply, Complex.star_def] at h4
  have h5 : ∑ a : Fin r, Zm a.castSucc b * conj (Mf T T' Zm a.castSucc c) = conj (Km T T' Zm b c) := by
    rw [← h2, map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_mul, Complex.conj_conj]
    ring
  simp only [hco, xco]
  rw [h1, h5]
  unfold Heta at h4
  linear_combination h4

end gram

end

end Formalism.FourierDecayAlt.P.PBI
