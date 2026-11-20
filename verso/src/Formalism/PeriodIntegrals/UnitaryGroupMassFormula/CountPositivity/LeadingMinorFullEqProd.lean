import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.HermFormAnisotropicOrthSecond

noncomputable section

namespace PI.CntNotPosW

open Matrix Formalism.BasicNotions Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {S : HSpace E} {r : ℕ} {T T' : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zhat_apply (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (a b : Fin (r + 1)) :
    Zhat F F' a b = S.hT (F.fvec a) (F'.fvec b) := rfl

/- English proof (translation)
Unfold `leadMinorE`. Rewrite using `[dif_pos (Nat.le_succ r)]`. Use `congr 1`. Use extensionality with `a b`. Establish `hc : ∀ x : Fin r, Fin.castLE (Nat.le_succ r) x = Fin.castSucc x` using `fun x => Fin.ext rfl`.

Simplify using `only [Matrix.submatrix_apply, hc, zhat_apply, FlagG.fvec, Fin.snoc_castSucc, Pm, Matrix.of_apply]`.
-/
theorem lead_r (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) :
    leadMinorE (Zhat F F') r = (Pm F F').det := by
  unfold leadMinorE
  rw [dif_pos (Nat.le_succ r)]
  congr 1
  ext a b
  have hc : ∀ x : Fin r, Fin.castLE (Nat.le_succ r) x = Fin.castSucc x := fun x => Fin.ext rfl
  simp only [Matrix.submatrix_apply, hc, zhat_apply, FlagG.fvec, Fin.snoc_castSucc, Pm, Matrix.of_apply]

/- English proof (translation)
Unfold `leadMinorE`. Rewrite using `[dif_pos le_rfl]`. Both sides reduce to the same expression.
-/
theorem leadingMinor_full_eq_det (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) :
    leadMinorE (Zhat F F') (r + 1) = (Zhat F F').det := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  rfl

def kk (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (c : Fin r) : E :=
  ∑ a, cz' F F' a * (Pm F F')⁻¹ c a

def Um (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun c b => if b = Fin.last r then Fin.snoc (α := fun _ => E) (kk F F') 1 c
    else if c = b then 1 else 0

def gv (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : Fin (r + 1) → S.V :=
  Fin.snoc (α := fun _ => S.V) F'.e (zt' F F')

/- English proof (translation)
Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Um, Matrix.of_apply, if_pos rfl, Fin.snoc_castSucc, Fin.snoc_last, gv, FlagG.fvec, one_smul]`. Rewrite using `[zp_eq F F', add_comm]`.

Simplify using `[kk]`. Consider the case `cast b`. Simplify using `only [Um, Matrix.of_apply, FlagG.fvec, Fin.snoc_castSucc, if_neg (Fin.castSucc_ne_last b), ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, gv]`.
-/
theorem fvec_eq (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (b : Fin (r + 1)) :
    F'.fvec b = ∑ c, Um F F' c b • gv F F' c := by
  induction b using Fin.lastCases with
  | last =>
    rw [Fin.sum_univ_castSucc]
    simp only [Um, Matrix.of_apply, if_pos rfl, Fin.snoc_castSucc, Fin.snoc_last, gv, FlagG.fvec,
      one_smul]
    rw [zp_eq F F', add_comm]
    simp [kk]
  | cast b =>
    simp only [Um, Matrix.of_apply, FlagG.fvec, Fin.snoc_castSucc, if_neg (Fin.castSucc_ne_last b),
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, gv]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[zhat_apply, fvec_eq F F' b, hr_sum]`. Simplify using `only [hr_smul, Matrix.mul_apply, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zhat_eq_mul (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) :
    Zhat F F' = (Matrix.of fun a b => S.hT (F.fvec a) (gv F F' b)) * Um F F' := by
  ext a b
  rw [zhat_apply, fvec_eq F F' b, hr_sum]
  simp only [hr_smul, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `h : i = Fin.last r`. Substitute `h` using the available equality.

Simplify using `[Um]`. Simplify using `[Um, h]`. Introduce `i j hij`. Establish `hj : j ≠ Fin.last r`. Introduce and unpack `rfl`.

Conclude with `absurd hij (not_lt.2 (Fin.le_last i))`. Establish `hij' : i ≠ j` using `fun h => by subst h; exact lt_irrefl _ hij`. Simplify using `[Um, hj, hij']`.
-/
theorem det_Um (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : (Um F F').det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    by_cases h : i = Fin.last r
    · subst h; simp [Um]
    · simp [Um, h]
  · intro i j hij
    have hj : j ≠ Fin.last r := by
      rintro rfl
      exact absurd hij (not_lt.2 (Fin.le_last i))
    have hij' : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    simp [Um, hj, hij']

/- English proof (translation)
Establish `hsub : (Matrix.of fun a b => S.hT (F.fvec a) (gv F F' b)).submatrix (Fin.last r).succAbove (Fin.last r).succAbove = Pm F F'`. Use extensionality with `a b`. Simplify using `[Fin.succAbove_last, gv, FlagG.fvec, Pm]`. Establish `hlast : S.hT (F.fvec (Fin.last r)) (gv F F' (Fin.last r)) = beta F F'`. Simplify using `only [FlagG.fvec, gv, Fin.snoc_last, beta, zt, hl_sub, hl_sum, hl_smul, h_e_zt' F F' hP, mul_zero, Finset.sum_const_zero, sub_zero]`.

Rewrite using `[Matrix.det_succ_column _ (Fin.last r), Fintype.sum_eq_single (Fin.last r)]`. Rewrite using `[hsub, Matrix.of_apply, hlast, Fin.val_last]`. Establish `hpow : ((-1 : E) ^ (r + r)) = 1` using `by rw [← two_mul, pow_mul]; simp`. Rewrite using `[hpow, one_mul]`. Introduce `i hi`.

Take `⟨i0, rfl⟩` from `Fin.exists_castSucc_eq.2 hi`. Simplify using `[gv, FlagG.fvec, h_e_zt' F F' hP]`.
-/
theorem det_Zt (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (hP : (Pm F F').det ≠ 0) :
    (Matrix.of fun a b => S.hT (F.fvec a) (gv F F' b)).det = beta F F' * (Pm F F').det := by
  have hsub : (Matrix.of fun a b => S.hT (F.fvec a) (gv F F' b)).submatrix (Fin.last r).succAbove
      (Fin.last r).succAbove = Pm F F' := by
    ext a b
    simp [Fin.succAbove_last, gv, FlagG.fvec, Pm]
  have hlast : S.hT (F.fvec (Fin.last r)) (gv F F' (Fin.last r)) = beta F F' := by
    simp only [FlagG.fvec, gv, Fin.snoc_last, beta, zt, hl_sub, hl_sum, hl_smul, h_e_zt' F F' hP,
      mul_zero, Finset.sum_const_zero, sub_zero]
  rw [Matrix.det_succ_column _ (Fin.last r), Fintype.sum_eq_single (Fin.last r)]
  · rw [hsub, Matrix.of_apply, hlast, Fin.val_last]
    have hpow : ((-1 : E) ^ (r + r)) = 1 := by rw [← two_mul, pow_mul]; simp
    rw [hpow, one_mul]
  · intro i hi
    obtain ⟨i0, rfl⟩ := Fin.exists_castSucc_eq.2 hi
    simp [gv, FlagG.fvec, h_e_zt' F F' hP]

/- English proof (translation)
Rewrite using `[leadingMinor_full_eq_det, zhat_eq_mul, Matrix.det_mul, det_Um, mul_one, det_Zt F F' hP]`.
-/
theorem leadingMinor_full_eq_prod (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (hP : (Pm F F').det ≠ 0) :
    leadMinorE (Zhat F F') (r + 1) = beta F F' * (Pm F F').det := by
  rw [leadingMinor_full_eq_det, zhat_eq_mul, Matrix.det_mul, det_Um, mul_one, det_Zt F F' hP]

/- English proof (translation)
Establish `hns : ∀ x : E, τ x * τ (star x) = ((Complex.normSq (τ x) : ℝ) : ℂ)`. Introduce `x`. Rewrite using `[hτ, Complex.mul_conj]`. Establish `hGf : Gflag F F' = leadMinorE (Zhat F F') (r + 1) * star (leadMinorE (Zhat F F') (r + 1)) - (T : E) * (T' : E) * (leadMinorE (Zhat F F') r * star (leadMinorE (Zhat F F') r))` using `rfl`. Use `set D1 := leadMinorE (Zhat F F') (r + 1) with hD1`.

Use `set D0 := leadMinorE (Zhat F F') r with hD0`. Use `set R : ℝ := Complex.normSq (τ D1) - (T : ℝ) * T' * Complex.normSq (τ D0) with hR`. Establish `hτG : τ (Gflag F F') = (R : ℂ)`. Rewrite using `[hGf, map_sub, map_mul, map_mul, map_mul, map_mul, hns, hns, map_natCast, map_natCast, hR]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hτG, Complex.ofReal_re]`. Assume the negation of the conclusion as `hle`. Use `push Not at hle`. Establish `hne : R ≠ 0`.

Introduce `h0`. Apply `hG` to reduce the goal to its premises. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hτG, h0, map_zero, Complex.ofReal_zero]`. Establish `hlt : R < 0` using `lt_of_le_of_ne hle hne`.

Distinguish the cases in `hP : (Pm F F').det = 0`. Establish `: D0 = 0` using `by rw [hD0, lead_r, hP]`. Rewrite `hlt` using `[hR, this, map_zero, Complex.normSq_zero, mul_zero, sub_zero]`. Conclude with `absurd hlt (not_lt.2 (Complex.normSq_nonneg _))`. Establish `hD1e : D1 = beta F F' * D0` using `by rw [hD1, leadingMinor_full_eq_prod F F' hP, hD0, lead_r]`.

Establish `hD0ne : τ D0 ≠ 0`. Rewrite using `[hD0, lead_r, map_ne_zero]`. Conclude with `hP`. Establish `hpos0 : 0 < Complex.normSq (τ D0)` using `Complex.normSq_pos.2 hD0ne`. Use `set nb := Complex.normSq (τ (beta F F')) with hnb`.

Establish `hRe : R = Complex.normSq (τ D0) * (nb - (T : ℝ) * T')`. Rewrite using `[hR, hD1e, map_mul, Complex.normSq_mul, hnb]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbT : nb < (T : ℝ) * T'`. Rewrite `hlt` using `[hRe]`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `: 0 ≤ Complex.normSq (τ D0) * (nb - (T : ℝ) * T')` using `mul_nonneg hpos0.le (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnb0 : 0 ≤ nb` using `Complex.normSq_nonneg _`.

Establish `hTpos : (0 : ℝ) < T`. Break down `Nat.eq_zero_or_pos T with h | h` into its components or cases. Rewrite `hbT` using `[h]`. Simplify using `at hbT`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h` after adjusting the coercions. Establish `hTE : (T : E) ≠ 0`. Establish `: T ≠ 0` using `by exact_mod_cast hTpos.ne'`. Conclude with `this` after adjusting the coercions. Set `w : Fin r ⊕ Bool → S.V` to `Sum.elim (vv F F') (fun b => if b then zt2 F F' else zt F F')`.

Set `d : Fin r ⊕ Bool → ℝ` to `Sum.elim (fun _ => -2) (fun b => if b then -(T' : ℝ) + nb / T else -(T : ℝ))`. Establish `hoff : ∀ i j, i ≠ j → S.hT (w i) (w j) = 0`. Introduce `i j hij`. Apply the tactic sequence `rcases i with a | bi <;> rcases j with b | bj`. Establish `hab : a ≠ b` using `fun h => hij (by rw [h])`.

Simplify using `only [w, Sum.elim_inl, h_v_v F F' hP, if_neg hab]`. Consider the cases of `bj`. Simplify using `only [w, Sum.elim_inl, Sum.elim_inr]`. Conclude with `h_v_zt F F' hP a`. Simplify using `only [w, Sum.elim_inl, Sum.elim_inr]`.

Conclude with `hermForm_vector_orth_second F F' hP a`. Consider the cases of `bi`. Simplify using `only [w, Sum.elim_inl, Sum.elim_inr]`. Conclude with `h_zero_swap S (h_v_zt F F' hP b)`. Simplify using `only [w, Sum.elim_inl, Sum.elim_inr]`.

Conclude with `h_zero_swap S (hermForm_vector_orth_second F F' hP b)`. Apply the tactic sequence `cases bi <;> cases bj`. Conclude with `absurd rfl hij`. Simplify using `only [w, Sum.elim_inr]`. Conclude with `hermForm_anisotropic_orth_second F F' hTE`.

Simplify using `only [w, Sum.elim_inr]`. Conclude with `h_zero_swap S (hermForm_anisotropic_orth_second F F' hTE)`. Conclude with `absurd rfl hij`. Establish `hdiag : ∀ i, τ (S.hT (w i) (w i)) = (d i : ℂ)`. Introduce `i`.

Break down `i with a | b` into its components or cases. Simplify using `only [w, d, Sum.elim_inl, h_v_v F F' hP, ↓reduceIte, map_neg]`. Rewrite using `[show (2 : E) = ((2 : ℕ) : E) by norm_num, map_natCast]`. Evaluate the numerical expressions. Consider the cases of `b`.

Simplify using `only [w, d, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte]`. Rewrite using `[h_zt_zt]`. Simplify using the standard rewrite rules. Simplify using `only [w, d, Sum.elim_inr, ↓reduceIte]`. Rewrite using `[hermForm_second_anisotropic F F' hTE, map_add, map_div₀, map_mul, hns, map_neg, map_natCast, map_natCast, hnb]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hneg : ∀ i, d i < 0`. Introduce `i`. Break down `i with a | b` into its components or cases.

Simplify using `[d]`. Consider the cases of `b`. Simplify using `only [d, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [d, Sum.elim_inr, ↓reduceIte]`.

Establish `: nb / T < T'`. Rewrite using `[div_lt_iff₀ hTpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc` using `card_le_of_negFamily S τ hτ hS w d hoff hdiag hneg`.

Simplify using `only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc`. Use linear arithmetic over natural numbers and integers.
-/
theorem gflag_pos (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) {p' q' : ℕ}
    (hS : Formalism.UG.HasSignature (S.gram.map τ) p' q') (hq : q' = r + 1) (hG : Gflag F F' ≠ 0) :
    0 < (τ (Gflag F F')).re := by
  have hns : ∀ x : E, τ x * τ (star x) = ((Complex.normSq (τ x) : ℝ) : ℂ) := by
    intro x; rw [hτ, Complex.mul_conj]
  have hGf : Gflag F F' = leadMinorE (Zhat F F') (r + 1) * star (leadMinorE (Zhat F F') (r + 1)) -
      (T : E) * (T' : E) * (leadMinorE (Zhat F F') r * star (leadMinorE (Zhat F F') r)) := rfl
  set D1 := leadMinorE (Zhat F F') (r + 1) with hD1
  set D0 := leadMinorE (Zhat F F') r with hD0
  set R : ℝ := Complex.normSq (τ D1) - (T : ℝ) * T' * Complex.normSq (τ D0) with hR
  have hτG : τ (Gflag F F') = (R : ℂ) := by
    rw [hGf, map_sub, map_mul, map_mul, map_mul, map_mul, hns, hns, map_natCast, map_natCast, hR]
    push_cast
    ring
  rw [hτG, Complex.ofReal_re]
  by_contra hle
  push Not at hle
  have hne : R ≠ 0 := by
    intro h0
    apply hG
    apply τ.injective
    rw [hτG, h0, map_zero, Complex.ofReal_zero]
  have hlt : R < 0 := lt_of_le_of_ne hle hne
  by_cases hP : (Pm F F').det = 0
  · have : D0 = 0 := by rw [hD0, lead_r, hP]
    rw [hR, this, map_zero, Complex.normSq_zero, mul_zero, sub_zero] at hlt
    exact absurd hlt (not_lt.2 (Complex.normSq_nonneg _))
  · have hD1e : D1 = beta F F' * D0 := by rw [hD1, leadingMinor_full_eq_prod F F' hP, hD0, lead_r]
    have hD0ne : τ D0 ≠ 0 := by
      rw [hD0, lead_r, map_ne_zero]
      exact hP
    have hpos0 : 0 < Complex.normSq (τ D0) := Complex.normSq_pos.2 hD0ne
    set nb := Complex.normSq (τ (beta F F')) with hnb
    have hRe : R = Complex.normSq (τ D0) * (nb - (T : ℝ) * T') := by
      rw [hR, hD1e, map_mul, Complex.normSq_mul, hnb]
      ring
    have hbT : nb < (T : ℝ) * T' := by
      rw [hRe] at hlt
      by_contra h
      push Not at h
      have : 0 ≤ Complex.normSq (τ D0) * (nb - (T : ℝ) * T') :=
        mul_nonneg hpos0.le (by linarith)
      linarith
    have hnb0 : 0 ≤ nb := Complex.normSq_nonneg _
    have hTpos : (0 : ℝ) < T := by
      rcases Nat.eq_zero_or_pos T with h | h
      · rw [h] at hbT; simp at hbT; linarith
      · exact_mod_cast h
    have hTE : (T : E) ≠ 0 := by
      have : T ≠ 0 := by exact_mod_cast hTpos.ne'
      exact_mod_cast this
    let w : Fin r ⊕ Bool → S.V := Sum.elim (vv F F') (fun b => if b then zt2 F F' else zt F F')
    let d : Fin r ⊕ Bool → ℝ := Sum.elim (fun _ => -2) (fun b => if b then -(T' : ℝ) + nb / T else -(T : ℝ))
    have hoff : ∀ i j, i ≠ j → S.hT (w i) (w j) = 0 := by
      intro i j hij
      rcases i with a | bi <;> rcases j with b | bj
      · have hab : a ≠ b := fun h => hij (by rw [h])
        simp only [w, Sum.elim_inl, h_v_v F F' hP, if_neg hab]
      · cases bj
        · simp only [w, Sum.elim_inl, Sum.elim_inr]; exact h_v_zt F F' hP a
        · simp only [w, Sum.elim_inl, Sum.elim_inr]; exact hermForm_vector_orth_second F F' hP a
      · cases bi
        · simp only [w, Sum.elim_inl, Sum.elim_inr]; exact h_zero_swap S (h_v_zt F F' hP b)
        · simp only [w, Sum.elim_inl, Sum.elim_inr]; exact h_zero_swap S (hermForm_vector_orth_second F F' hP b)
      · cases bi <;> cases bj
        · exact absurd rfl hij
        · simp only [w, Sum.elim_inr]; exact hermForm_anisotropic_orth_second F F' hTE
        · simp only [w, Sum.elim_inr]; exact h_zero_swap S (hermForm_anisotropic_orth_second F F' hTE)
        · exact absurd rfl hij
    have hdiag : ∀ i, τ (S.hT (w i) (w i)) = (d i : ℂ) := by
      intro i
      rcases i with a | b
      · simp only [w, d, Sum.elim_inl, h_v_v F F' hP, ↓reduceIte, map_neg]
        rw [show (2 : E) = ((2 : ℕ) : E) by norm_num, map_natCast]
        norm_num
      · cases b
        · simp only [w, d, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte]
          rw [h_zt_zt]
          simp
        · simp only [w, d, Sum.elim_inr, ↓reduceIte]
          rw [hermForm_second_anisotropic F F' hTE, map_add, map_div₀, map_mul, hns, map_neg, map_natCast, map_natCast, hnb]
          push_cast
          ring
    have hneg : ∀ i, d i < 0 := by
      intro i
      rcases i with a | b
      · simp [d]
      · cases b
        · simp only [d, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte]; linarith
        · simp only [d, Sum.elim_inr, ↓reduceIte]
          have : nb / T < T' := by
            rw [div_lt_iff₀ hTpos]; linarith
          linarith
    have hc := card_le_of_negFamily S τ hτ hS w d hoff hdiag hneg
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc
    omega

end PI.CntNotPosW
