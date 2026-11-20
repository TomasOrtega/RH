import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerBlockPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousInvUpper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RemainderNormLeStrictUpper

open Matrix MeasureTheory

namespace Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic

open Formalism.FourierDecayAlt.G

/- English proof (translation)
Simplify using `[wMat, Matrix.mul_apply]`.
-/
private lemma wMat_mul_apply_eq_rev {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (r c : Fin m) :
    (wMat m * M) r c = M r.rev c := by
  simp [wMat, Matrix.mul_apply]

/- English proof (translation)
Simplify using `[wMat, Matrix.mulVec, dotProduct]`.
-/
private lemma wMat_mulVec_apply_eq_rev {m : ℕ} (v : Fin m → ℂ) (r : Fin m) : (wMat m *ᵥ v) r = v r.rev := by
  simp [wMat, Matrix.mulVec, dotProduct]

/- English proof (translation)
Rewrite using `[Equiv.symm_apply_eq]`. Both sides reduce to the same expression.
-/
private lemma finSumFinEquiv_symm_castSucc_eq_inl {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (Fin.castSucc i : Fin (n + 1)) = (Sum.inl i : Fin n ⊕ Fin 1) := by
  rw [Equiv.symm_apply_eq]; rfl

/- English proof (translation)
Rewrite using `[Equiv.symm_apply_eq]`. Both sides reduce to the same expression.
-/
private lemma finSumFinEquiv_symm_last_eq_inr (n : ℕ) : finSumFinEquiv.symm (Fin.last n) = (Sum.inr 0 : Fin n ⊕ Fin 1) := by
  rw [Equiv.symm_apply_eq]; rfl

/- English proof (translation)
Rewrite using `[wMat_mul_apply_eq_rev]`. Use `first`. Consider the case `simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]`. Consider the case `simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]`.
-/
theorem wM_succ_last {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) i.succ (Fin.last n) = B i := by
  rw [wMat_mul_apply_eq_rev]
  first
    | simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]
    | simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

/- English proof (translation)
Rewrite using `[wMat_mul_apply_eq_rev]`. Use `first`. Consider the case `simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]`. Consider the case `simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]`.
-/
theorem wM_succ_cast {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i j : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) i.succ j.castSucc = t * (1 : Matrix (Fin n) (Fin n) ℂ) i j + X i j := by
  rw [wMat_mul_apply_eq_rev]
  first
    | simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]
    | simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

/- English proof (translation)
Rewrite using `[wMat_mul_apply_eq_rev]`. Use `first`. Consider the case `simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]`. Consider the case `simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]`.
-/
theorem wM_zero_cast {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (j : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) 0 j.castSucc = ρ j := by
  rw [wMat_mul_apply_eq_rev]
  first
    | simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]
    | simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

/- English proof (translation)
Rewrite using `[wMat_mul_apply_eq_rev]`. Use `first`. Consider the case `simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]`. Consider the case `simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]`.
-/
theorem wM_zero_last {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    (wMat (n + 1) * Mcoord t X B ρ σ) 0 (Fin.last n) = σ := by
  rw [wMat_mul_apply_eq_rev]
  first
    | simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]
    | simp [Mcoord, blk, Fin.rev_succ, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

/- English proof (translation)
Simplify using `only [Matrix.diagonal_apply, Fin.cons_succ]`.
-/
theorem diagonal_cons_succ {n : ℕ} (a b : ℂ) (x : Fin n → ℂ) (i : Fin n) (j : Fin (n + 1)) :
    Matrix.diagonal (Fin.cons a x : Fin (n + 1) → ℂ) i.succ j =
      Matrix.diagonal (Fin.cons b x : Fin (n + 1) → ℂ) i.succ j := by
  simp only [Matrix.diagonal_apply, Fin.cons_succ]

/- English proof (translation)
Use `Fin.lastCases ?_ (fun k => ?_) k` and prove the remaining obligations. Rewrite using `[G6.xOf_last]`. Simplify using `[redOf, triXY, strictUpper, Fin.succ_last]`. Rewrite using `[G6.xOf_castSucc]`. Establish `h : k.castSucc < k.succ` using `Fin.castSucc_lt_succ`.

Simplify using `[redOf, triXY, strictUpper, h]`.
-/
theorem xOf_redOf (m : ℕ) (p : XY m) (k : Fin (m + 1)) :
    xOf (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 k = p.1 k := by
  refine Fin.lastCases ?_ (fun k => ?_) k
  · rw [G6.xOf_last]
    simp [redOf, triXY, strictUpper, Fin.succ_last]
  · rw [G6.xOf_castSucc]
    have h : k.castSucc < k.succ := Fin.castSucc_lt_succ
    simp [redOf, triXY, strictUpper, h]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Establish `hs : subShift (m + 2) 0 j = 0` using `by simp [subShift]`. Rewrite using `[hs, mul_zero, zero_add]`.

Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Rewrite using `[wM_zero_last]`. Simplify using `[redOf, triXY]`. Rewrite using `[wM_zero_cast]`. Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations.

Simplify using `[strictUpper]`. Establish `h : (0 : Fin (m + 2)) ≠ k.castSucc.succ` using `(Fin.succ_ne_zero _).symm`. Simplify using `[redOf, triXY, Matrix.diagonal_apply_ne _ h]`. Rewrite using `[diagonal_cons_succ ρ₁ 0]`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations.

Rewrite using `[wM_succ_last]`. Establish `hs : subShift (m + 2) i.succ (Fin.last (m + 1)) = 0`. Use `i.isLt` as an intermediate fact. Simplify using `only [subShift, Matrix.of_apply, Fin.val_last, Fin.val_succ]`. Rewrite using `[if_neg (by omega)]`.

Rewrite using `[hs, mul_zero, zero_add]`. Simplify using `[redOf, triXY]`. Rewrite using `[wM_succ_cast]`. Establish `hs : subShift (m + 2) i.succ j.castSucc = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i j`. Simplify using `only [subShift, Matrix.of_apply, Fin.val_castSucc, Fin.val_succ, Matrix.one_apply, Fin.ext_iff]`.

Distinguish the cases in `h : (i : ℕ) = j`. Rewrite using `[if_pos (by omega), if_pos h]`. Rewrite using `[if_neg (by omega), if_neg h]`. Rewrite using `[hs, add_assoc]`. Use `congr 1`.

Distinguish the cases in `h : i < j`. Simplify using `[redOf, triXY, strictUpper, h]`. Establish `h1 : i.succ ≠ j.castSucc`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact.

Simplify using `only [Fin.val_succ, Fin.val_castSucc] at this`. Conclude with `h (by rw [Fin.lt_def]; omega)`. Establish `h2 : ¬ (i.succ < j.castSucc)`. Introduce `e`. Rewrite `e` using `[Fin.lt_def]`.

Simplify using `only [Fin.val_succ, Fin.val_castSucc] at e`. Conclude with `h (by rw [Fin.lt_def]; omega)`. Simplify using `[strictUpper, h, h2, Matrix.diagonal_apply_ne _ h1]`.
-/
theorem wM_redOf (m : ℕ) (t ρ₁ : ℂ) (p : XY m) :
    wMat (m + 2) * Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
        (Fin.cons ρ₁ (redOf m p).2.1) (redOf m p).1 =
      t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ p.1 : Fin (m + 2) → ℂ) + strictUpper p.2 := by
  ext i j
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine Fin.cases ?_ (fun i => ?_) i
  · have hs : subShift (m + 2) 0 j = 0 := by simp [subShift]
    rw [hs, mul_zero, zero_add]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [wM_zero_last]
      simp [redOf, triXY]
    · rw [wM_zero_cast]
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [strictUpper]
      · have h : (0 : Fin (m + 2)) ≠ k.castSucc.succ := (Fin.succ_ne_zero _).symm
        simp [redOf, triXY, Matrix.diagonal_apply_ne _ h]
  · rw [diagonal_cons_succ ρ₁ 0]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [wM_succ_last]
      have hs : subShift (m + 2) i.succ (Fin.last (m + 1)) = 0 := by
        have := i.isLt
        simp only [subShift, Matrix.of_apply, Fin.val_last, Fin.val_succ]
        rw [if_neg (by omega)]
      rw [hs, mul_zero, zero_add]
      simp [redOf, triXY]
    · rw [wM_succ_cast]
      have hs : subShift (m + 2) i.succ j.castSucc = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i j := by
        simp only [subShift, Matrix.of_apply, Fin.val_castSucc, Fin.val_succ, Matrix.one_apply, Fin.ext_iff]
        by_cases h : (i : ℕ) = j
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      rw [hs, add_assoc]
      congr 1
      by_cases h : i < j
      · simp [redOf, triXY, strictUpper, h]
      · have h1 : i.succ ≠ j.castSucc := by
          intro e
          have := congrArg Fin.val e
          simp only [Fin.val_succ, Fin.val_castSucc] at this
          exact h (by rw [Fin.lt_def]; omega)
        have h2 : ¬ (i.succ < j.castSucc) := by
          intro e
          rw [Fin.lt_def] at e
          simp only [Fin.val_succ, Fin.val_castSucc] at e
          exact h (by rw [Fin.lt_def]; omega)
        simp [strictUpper, h, h2, Matrix.diagonal_apply_ne _ h1]

end Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic

/- English proof (translation)
Introduce `d β`. Establish `hι : MeasurePreserving (fun k : UT d → ℂ => coordU (wMat d * (upper k)⁻¹ * wMat d)ᵀ) (muPi β (UT d)) (muPi β (UT d))`. Simplify using `only [G5.coordU_conj]`. Conclude with `(G5.mp_comp_equiv β (G5.revEquiv d)).comp (G5.mp_invU β d)`. Establish `hm : Measurable (Function.uncurry fun (k : UT d → ℂ) (u : UT d → ℂ) => coordU (upper k * upper u))`.

Use `Continuous.measurable ?_` and prove the remaining obligations. Conclude with `(G5.continuous_coordU d).comp (((G5.continuous_upper d).comp continuous_fst).matrix_mul ((G5.continuous_upper d).comp continuous_snd))`. Conclude with `hι.skew_product (μc := muPi β (UT d)) (μd := muPi β (UT d)) hm (Filter.Eventually.of_forall fun k => (G5.mp_lmulU β d k).map_eq)`.
-/
theorem quotient_measure_long_orbit : Formalism.FourierDecayAlt.G.QuotientMeasureLong := by
  intro d β
  have hι : MeasurePreserving (fun k : UT d → ℂ => coordU (wMat d * (upper k)⁻¹ * wMat d)ᵀ)
      (muPi β (UT d)) (muPi β (UT d)) := by
    simp only [G5.coordU_conj]
    exact (G5.mp_comp_equiv β (G5.revEquiv d)).comp (G5.mp_invU β d)
  have hm : Measurable (Function.uncurry fun (k : UT d → ℂ) (u : UT d → ℂ) => coordU (upper k * upper u)) := by
    refine Continuous.measurable ?_
    exact (G5.continuous_coordU d).comp
      (((G5.continuous_upper d).comp continuous_fst).matrix_mul ((G5.continuous_upper d).comp continuous_snd))
  exact hι.skew_product (μc := muPi β (UT d)) (μd := muPi β (UT d)) hm
    (Filter.Eventually.of_forall fun k => (G5.mp_lmulU β d k).map_eq)

/- English proof (translation)
Introduce `n β g l u k k' hg hl hu hk hk' hs`. Establish `h0 : subSum k + superSum k' = 0`. Break down `hg with ⟨z, hz, rfl⟩ | ⟨t, c, ht, rfl⟩` into its components or cases. Conclude with `(stabilizer_long_point n z hz k k' hk hk').2 hs`. Conclude with `(stabilizer_block_point n t c ht k k' hk hk').2 hs`.

Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[(character_additive n l k).2 hl hk, (character_additive n k' u).1 hk' hu, ← (additive_character_psi β _ _).1, ← (additive_character_psi β _ _).1]`. Use `congr 1`. Take the linear combination `h0`.
-/
theorem stabilizer_invariant : Formalism.FourierDecayAlt.G.StabInvariant := by
  intro n β g l u k k' hg hl hu hk hk' hs
  have h0 : subSum k + superSum k' = 0 := by
    rcases hg with ⟨z, hz, rfl⟩ | ⟨t, c, ht, rfl⟩
    · exact (stabilizer_long_point n z hz k k' hk hk').2 hs
    · exact (stabilizer_block_point n t c ht k k' hk hk').2 hs
  constructor
  · calc l * k * g * (k' * u) = l * (k * g * k') * u := by simp only [Matrix.mul_assoc]
      _ = l * g * u := by rw [hs]
  · rw [(character_additive n l k).2 hl hk, (character_additive n k' u).1 hk' hu,
      ← (additive_character_psi β _ _).1, ← (additive_character_psi β _ _).1]
    congr 1
    linear_combination h0

/- English proof (translation)
Introduce `m Kc hK h0 R hR`. Take `⟨d, hd, hball⟩` from `Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0`. Establish `hD : ∀ D ∈ Kc, d ≤ ‖D‖`. Introduce `D hDK`. Assume the negation of the conclusion as `hlt`.

Conclude with `hball (by simpa [Metric.mem_ball] using not_le.mp hlt) hDK`. Use `set R' : ℝ := max 1 R with hR'`. Establish `hR1 : 1 ≤ R'` using `le_max_left _ _`. Establish `hRR : R ≤ R'` using `le_max_right _ _`. Establish `hR0 : 0 < R'` using `lt_of_lt_of_le one_pos hR1`.

Use `set Cm : ℝ := ((m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) ^ m) with hCm`. Establish `hCm0 : 0 ≤ Cm` using `by positivity`. Use `set q : ℝ := d / (2 * (Cm + 1) * R' ^ (m + 2)) with hq`. Establish `hq0 : 0 < q` using `by positivity`. Use `⟨min 1 (q ^ 2), d / (2 * R'), by positivity, by positivity, ?_⟩` and prove the remaining obligations.

Introduce `ε hε hε2 D hDK t ht htle X B ρ₁ ρ' σ hS hX hB hρ₁ hρ' hσ hrel`. Establish `hT : 0 < ‖t‖` using `norm_pos_iff.mpr ht`. Establish `hT1 : ‖t‖ ≤ 1` using `le_trans htle (min_le_left _ _)`. Establish `hTq : ‖t‖ ≤ q ^ 2` using `le_trans htle (min_le_right _ _)`. Use `set L₀ : ℝ := ‖t‖ ^ (-ε) with hL₀def`.

Establish `hL₀ : 1 ≤ L₀` using `Real.one_le_rpow_of_pos_of_le_one_of_nonpos hT hT1 (by linarith)`. Establish `hL₀0 : 0 < L₀` using `lt_of_lt_of_le one_pos hL₀`. Use `set L : ℝ := R' * L₀ with hLdef`. Establish `hL : 1 ≤ L` using `by nlinarith`. Establish `hL0 : 0 < L` using `lt_of_lt_of_le one_pos hL`.

Establish `hRL : R * L₀ ≤ L` using `mul_le_mul_of_nonneg_right hRR hL₀0.le`. Establish `hsq : L ^ (m + 2) * ‖t‖ ≤ R' ^ (m + 2) * q`. Rewrite using `[hLdef, mul_pow, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (le_trans (G6.rpow_bound m hT hT1 hε2) (Real.sqrt_le_iff.mpr ⟨hq0.le, hTq⟩)) (by positivity)`. Establish `hRb` using `G6.remainder_norm_le_strict_upper (t := t) hL hT1 hS (fun i j => (hX i j).trans hRL) (fun i => (hB i).trans hRL) (fun k => (hρ' k).trans hRL)`.

Establish `h1 : ‖t ^ (m + 1) * σ‖ ≤ L ^ (m + 2) * ‖t‖`. Rewrite using `[norm_mul, norm_pow, mul_comm]`. Use `mul_le_mul (le_trans (hσ.trans hRL) (le_self_pow₀ hL (by omega))) (pow_le_of_le_one hT.le hT1 (by omega)) (by positivity) (by positivity)` and prove the remaining obligations. Establish `h2 : ‖Cof X B t * ρ₁‖ ≤ ‖Cof X B t‖ * L`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_left (hρ₁.trans hRL) (norm_nonneg _)`. Establish `hDeq : D = t ^ (m + 1) * σ - Cof X B t * ρ₁ - R0 X B ρ' t`. Rewrite using `[hrel]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ‖D‖ ≤ L ^ (m + 2) * ‖t‖ + ‖Cof X B t‖ * L + Cm * (L ^ (m + 2) * ‖t‖)`.

Combine the equalities or inequalities in the displayed calculation. Establish `h4 : (Cm + 1) * (L ^ (m + 2) * ‖t‖) ≤ d / 2`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : d / 2 ≤ ‖Cof X B t‖ * L`. Use `hD D hDK` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hinv : ‖t‖ ^ ε = L₀⁻¹`. Rewrite using `[hL₀def, Real.rpow_neg hT.le, inv_inv]`. Establish `e : d / (2 * R') * L₀⁻¹ = d / 2 / L`. Rewrite using `[hLdef]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hinv, e, div_le_iff₀ hL0]`. Conclude with `h5`.
-/
theorem cofactor_lower_bound_radius : Formalism.FourierDecayAlt.G.CofLowerR := by
  intro m Kc hK h0 R hR
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0
  have hD : ∀ D ∈ Kc, d ≤ ‖D‖ := by
    intro D hDK
    by_contra hlt
    exact hball (by simpa [Metric.mem_ball] using not_le.mp hlt) hDK
  set R' : ℝ := max 1 R with hR'
  have hR1 : 1 ≤ R' := le_max_left _ _
  have hRR : R ≤ R' := le_max_right _ _
  have hR0 : 0 < R' := lt_of_lt_of_le one_pos hR1
  set Cm : ℝ := ((m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) ^ m) with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set q : ℝ := d / (2 * (Cm + 1) * R' ^ (m + 2)) with hq
  have hq0 : 0 < q := by positivity
  refine ⟨min 1 (q ^ 2), d / (2 * R'), by positivity, by positivity, ?_⟩
  intro ε hε hε2 D hDK t ht htle X B ρ₁ ρ' σ hS hX hB hρ₁ hρ' hσ hrel
  have hT : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hT1 : ‖t‖ ≤ 1 := le_trans htle (min_le_left _ _)
  have hTq : ‖t‖ ≤ q ^ 2 := le_trans htle (min_le_right _ _)
  set L₀ : ℝ := ‖t‖ ^ (-ε) with hL₀def
  have hL₀ : 1 ≤ L₀ := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hT hT1 (by linarith)
  have hL₀0 : 0 < L₀ := lt_of_lt_of_le one_pos hL₀
  set L : ℝ := R' * L₀ with hLdef
  have hL : 1 ≤ L := by nlinarith
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hRL : R * L₀ ≤ L := mul_le_mul_of_nonneg_right hRR hL₀0.le
  have hsq : L ^ (m + 2) * ‖t‖ ≤ R' ^ (m + 2) * q := by
    rw [hLdef, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (le_trans (G6.rpow_bound m hT hT1 hε2) (Real.sqrt_le_iff.mpr ⟨hq0.le, hTq⟩)) (by positivity)
  have hRb := G6.remainder_norm_le_strict_upper (t := t) hL hT1 hS (fun i j => (hX i j).trans hRL) (fun i => (hB i).trans hRL)
    (fun k => (hρ' k).trans hRL)
  have h1 : ‖t ^ (m + 1) * σ‖ ≤ L ^ (m + 2) * ‖t‖ := by
    rw [norm_mul, norm_pow, mul_comm]
    refine mul_le_mul (le_trans (hσ.trans hRL) (le_self_pow₀ hL (by omega)))
      (pow_le_of_le_one hT.le hT1 (by omega)) (by positivity) (by positivity)
  have h2 : ‖Cof X B t * ρ₁‖ ≤ ‖Cof X B t‖ * L := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hρ₁.trans hRL) (norm_nonneg _)
  have hDeq : D = t ^ (m + 1) * σ - Cof X B t * ρ₁ - R0 X B ρ' t := by
    rw [hrel]; ring
  have h3 : ‖D‖ ≤ L ^ (m + 2) * ‖t‖ + ‖Cof X B t‖ * L + Cm * (L ^ (m + 2) * ‖t‖) := by
    calc ‖D‖ = ‖t ^ (m + 1) * σ - Cof X B t * ρ₁ - R0 X B ρ' t‖ := by rw [← hDeq]
      _ ≤ ‖t ^ (m + 1) * σ‖ + ‖Cof X B t * ρ₁‖ + ‖R0 X B ρ' t‖ :=
          le_trans (norm_sub_le _ _) (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ _ := add_le_add (add_le_add h1 h2) hRb
  have h4 : (Cm + 1) * (L ^ (m + 2) * ‖t‖) ≤ d / 2 := by
    calc (Cm + 1) * (L ^ (m + 2) * ‖t‖) ≤ (Cm + 1) * (R' ^ (m + 2) * q) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = d / 2 := by rw [hq]; field_simp
  have h5 : d / 2 ≤ ‖Cof X B t‖ * L := by
    have := hD D hDK
    nlinarith
  have hinv : ‖t‖ ^ ε = L₀⁻¹ := by
    rw [hL₀def, Real.rpow_neg hT.le, inv_inv]
  have e : d / (2 * R') * L₀⁻¹ = d / 2 / L := by
    rw [hLdef]; field_simp
  rw [hinv, e, div_le_iff₀ hL0]
  exact h5

/- English proof (translation)
Use `⟨fun r hr => ?_, fun r hr => ?_, fun r => ⟨?_, ?_⟩, fun k => ?_⟩` and prove the remaining obligations. Conclude with `Real.smoothTransition.one_of_one_le (by linarith)`. Conclude with `Real.smoothTransition.zero_of_nonpos (by linarith)`. Conclude with `Real.smoothTransition.nonneg _`. Conclude with `Real.smoothTransition.le_one _`.

Conclude with `(Real.smoothTransition.contDiff).comp (contDiff_const.sub contDiff_id)`.
-/
theorem smooth_cutoff_spec : Formalism.FourierDecayAlt.G.Chi0Spec := by
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r => ⟨?_, ?_⟩, fun k => ?_⟩
  · exact Real.smoothTransition.one_of_one_le (by linarith)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.nonneg _
  · exact Real.smoothTransition.le_one _
  · exact (Real.smoothTransition.contDiff).comp (contDiff_const.sub contDiff_id)

/- English proof (translation)
Introduce `m β D t ht V _ _ Φ p`. Establish `hx` using `xOf_redOf m p`. Unfold `amp redIntegrand`. Rewrite using `[smul_smul, ← mul_assoc, ← (additive_character_psi β _ _).1]`. Use `congr 3`.

Unfold `gRem g0 rhoXY`. Simplify using `only [hx]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem amplitude_eq : Formalism.FourierDecayAlt.G.AmpEq := by
  intro m β D t ht V _ _ Φ p
  have hx := xOf_redOf m p
  unfold amp redIntegrand
  rw [smul_smul, ← mul_assoc, ← (additive_character_psi β _ _).1]
  congr 3
  unfold gRem g0 rhoXY
  simp only [hx]
  field_simp
  ring

/- English proof (translation)
Introduce `m z y`. Rewrite using `[wM_redOf m 0 z (fun _ => z, y)]`. Use `congr 1`. Rewrite using `[zero_smul, zero_add]`. Use extensionality with `i j`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Apply the tactic sequence `refine Fin.cases ?_ (fun i' => ?_) i <;> simp [Matrix.diagonal, Matrix.smul_apply]`. Simplify using `[Matrix.diagonal, h, Matrix.smul_apply]`.
-/
theorem limit_coordinates_xy : Formalism.FourierDecayAlt.G.LimitCoordsXY := by
  intro m z y
  rw [wM_redOf m 0 z (fun _ => z, y)]
  congr 1
  rw [zero_smul, zero_add]
  ext i j
  by_cases h : i = j
  · subst h
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp [Matrix.diagonal, Matrix.smul_apply]
  · simp [Matrix.diagonal, h, Matrix.smul_apply]

end Formalism.FourierDecayAlt.P
