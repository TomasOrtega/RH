import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.VacUnique
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.EqZeroOfEvalReal

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

variable {sg : ℤˣ} {L : LOp m n}

def nbM (c : Matrix (Fin n) (Fin n) ℂ) : M2 n := Matrix.fromBlocks 1 0 c 1

/- English proof (translation)
Unfold `InG nbM JJ`. Rewrite using `[Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `[hc]`.
-/
theorem inG_nbM {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (nbM c) := by
  unfold InG nbM JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hc]

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Unfold `nbM`. Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem nbM_inv (c : Matrix (Fin n) (Fin n) ℂ) : (nbM c)⁻¹ = nbM (-c) := by
  apply Matrix.inv_eq_left_inv
  unfold nbM
  rw [Matrix.fromBlocks_multiply]
  simp

/- English proof (translation)
Establish `hci : (c⁻¹)ᴴ = c⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hc]`. Establish `hnu : IsUnit (-c⁻¹).det`. Rewrite using `[Matrix.det_neg]`. Conclude with `((isUnit_one.neg).pow _).mul (Matrix.isUnit_nonsing_inv_det c hu)`. Apply `mR_injective` to reduce the goal to its premises.

Rewrite using `[mR_toGR, mR_mul, mR_mul, mR_mul, mR_mG hnu, mR_nG hc, mR_jG, mR_nG hci]`. Establish `h1 : c⁻¹ * c = 1` using `Matrix.nonsing_inv_mul c hu`. Establish `h2 : c * c⁻¹ = 1` using `Matrix.mul_nonsing_inv c hu`. Establish `h3 : ((-c⁻¹)ᴴ)⁻¹ = -c`. Rewrite using `[Matrix.conjTranspose_neg, hci]`.

Conclude with `Matrix.inv_eq_left_inv (by rw [neg_mul_neg, h2])`. Unfold `nbM mLc nU JJ`. Rewrite using `[h3]`. Simplify using `only [Matrix.fromBlocks_multiply]`. Simplify using `[h1, h2, Matrix.neg_mul, Matrix.mul_neg]`.
-/
theorem nb_eq {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) (hu : IsUnit c.det) :
    toGR (nbM c) (inG_nbM hc) = mG (-c⁻¹) * nG c * jG n * nG c⁻¹ := by
  have hci : (c⁻¹)ᴴ = c⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hc]
  have hnu : IsUnit (-c⁻¹).det := by
    rw [Matrix.det_neg]
    exact ((isUnit_one.neg).pow _).mul (Matrix.isUnit_nonsing_inv_det c hu)
  apply mR_injective
  rw [mR_toGR, mR_mul, mR_mul, mR_mul, mR_mG hnu, mR_nG hc, mR_jG, mR_nG hci]
  have h1 : c⁻¹ * c = 1 := Matrix.nonsing_inv_mul c hu
  have h2 : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv c hu
  have h3 : ((-c⁻¹)ᴴ)⁻¹ = -c := by
    rw [Matrix.conjTranspose_neg, hci]
    exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, h2])
  unfold nbM mLc nU JJ
  rw [h3]
  simp only [Matrix.fromBlocks_multiply]
  simp [h1, h2, Matrix.neg_mul, Matrix.mul_neg]

def dT (i0 : Fin n) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if i = i0 then (t : ℂ) else 1

/- English proof (translation)
Unfold `dT`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h : i = i0 <;> simp [h]`.
-/
theorem dT_herm (i0 : Fin n) (t : ℝ) : (dT i0 t)ᴴ = dT i0 t := by
  unfold dT
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i = i0 <;> simp [h]

/- English proof (translation)
Simplify using `[dT, Matrix.det_diagonal]`.
-/
theorem dT_det (i0 : Fin n) (t : ℝ) : (dT i0 t).det = t := by
  simp [dT, Matrix.det_diagonal]

def pth (i0 : Fin n) (t : ℝ) : GR n :=
  toGR (nbM (-dT i0 t)) (inG_nbM (by rw [Matrix.conjTranspose_neg, dT_herm]))

/- English proof (translation)
Establish `hdT : Continuous fun t : ℝ => dT i0 t`. Unfold `dT`. Use `Continuous.matrix_diagonal (continuous_pi fun i => ?_)` and prove the remaining obligations. Distinguish the cases in `h : i = i0`. Simplify using `only [h, if_true]`.

Conclude with `Complex.continuous_ofReal`. Simplify using `only [h, if_false]`. Conclude with `continuous_const`. Establish `hnb : ∀ f : ℝ → Matrix (Fin n) (Fin n) ℂ, Continuous f → Continuous fun t => nbM (f t)`. Introduce `f hf`.

Unfold `nbM`. Conclude with `continuous_const.matrix_fromBlocks continuous_const hf continuous_const`. Unfold `pth toGR`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Rewrite using `[Units.continuous_iff]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun t => nbM (-dT i0 t)`. Conclude with `hnb _ hdT.neg`. Use `show Continuous fun t => (nbM (-dT i0 t))⁻¹`. Simplify using `only [nbM_inv, neg_neg]`.

Conclude with `hnb _ hdT`.
-/
theorem pth_cont (i0 : Fin n) : Continuous (pth i0) := by
  have hdT : Continuous fun t : ℝ => dT i0 t := by
    unfold dT
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    by_cases h : i = i0
    · simp only [h, if_true]
      exact Complex.continuous_ofReal
    · simp only [h, if_false]
      exact continuous_const
  have hnb : ∀ f : ℝ → Matrix (Fin n) (Fin n) ℂ, Continuous f → Continuous fun t => nbM (f t) := by
    intro f hf
    unfold nbM
    exact continuous_const.matrix_fromBlocks continuous_const hf continuous_const
  unfold pth toGR
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun t => nbM (-dT i0 t)
    exact hnb _ hdT.neg
  · show Continuous fun t => (nbM (-dT i0 t))⁻¹
    simp only [nbM_inv, neg_neg]
    exact hnb _ hdT

/- English proof (translation)
Unfold `F0 f0`. Establish `h1 : Matrix.det (mR g) ≠ 0` using `(det_ne_of_inG (M := mR g) g.2).ne_zero`. Conclude with `mul_ne_zero (zpow_ne_zero _ h1) (mul_ne_zero (zpow_ne_zero _ (automorphy_first_det_ne_zero g)) (zpow_ne_zero _ (automorphy_second_det_ne_zero g)))`.
-/
theorem weight_factor_ne_zero (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  unfold F0 f0
  have h1 : Matrix.det (mR g) ≠ 0 := (det_ne_of_inG (M := mR g) g.2).ne_zero
  exact mul_ne_zero (zpow_ne_zero _ h1)
    (mul_ne_zero (zpow_ne_zero _ (automorphy_first_det_ne_zero g)) (zpow_ne_zero _ (automorphy_second_det_ne_zero g)))

/- English proof (translation)
Unfold `pOf qOf`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem pq_sum (sg : ℤˣ) (m : ℕ) : ((pOf sg m : ℕ) : ℤ) + (qOf sg m : ℕ) = m := by
  unfold pOf qOf
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[mR_mul, mR_mG ha, mR_nG hb, lower_left_block_mul]`. Simplify using `[mLc, nU]`.
-/
theorem lower_left_block_levi_unipotent (a b : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) (hb : bᴴ = b) :
    (mR (mG a * nG b)).toBlocks₂₁ = 0 := by
  rw [mR_mul, mR_mG ha, mR_nG hb, lower_left_block_mul]
  simp [mLc, nU]

/- English proof (translation)
Establish `hf` using `isSw_fP (1 : PX m n)`. Establish `hz : ∀ F : (Fin m → Fin n → ℂ) → ℂ, F (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = F 0`. Introduce `F`. Use `congr 1`. Conclude with `Matrix.zero_mul a`.

Establish `e2 : L (nG b * g) (fP 1) (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = L g (fP 1) 0`. Use `(hz _).trans ?_` and prove the remaining obligations. Rewrite using `[h.mul _ _ _ hf, h.nU (nG b) b hb (mR_nG hb) _ (h.sw _ _ hf)]`. Simplify using the standard rewrite rules. Establish `e1` using `congrFun (hk (mG a) a ha (mR_mG ha) _ (h.sw (nG b * g) _ hf)) 0`.

Rewrite using `[mul_assoc, h.mul _ _ _ hf, e1]`. Use `show _ * _ * L (nG b * g) (fP 1) (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = _`. Rewrite using `[e2]`.
-/
theorem S_law (h : LocHyp sg L) {k : ℤ}
    (hk : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mLc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ m * f (Matrix.of u * a))
    (a b : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) (hb : bᴴ = b) (g : GR n) :
    L (mG a * nG b * g) (fP 1) 0 = (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ m * L g (fP 1) 0 := by
  have hf := isSw_fP (1 : PX m n)
  have hz : ∀ F : (Fin m → Fin n → ℂ) → ℂ, F (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = F 0 := by
    intro F
    congr 1
    exact Matrix.zero_mul a
  have e2 : L (nG b * g) (fP 1) (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = L g (fP 1) 0 := by
    refine (hz _).trans ?_
    rw [h.mul _ _ _ hf, h.nU (nG b) b hb (mR_nG hb) _ (h.sw _ _ hf)]
    simp
  have e1 := congrFun (hk (mG a) a ha (mR_mG ha) _ (h.sw (nG b * g) _ hf)) 0
  rw [mul_assoc, h.mul _ _ _ hf, e1]
  show _ * _ * L (nG b * g) (fP 1) (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = _
  rw [e2]

/- English proof (translation)
Establish `hf` using `isSw_fP (1 : PX m n)`. Rewrite using `[h.mul _ _ _ hf, hJ (jG n) mR_jG _ (h.sw _ _ hf), h.nU (nG b) b hb (mR_nG hb) _ hf]`. Unfold `secN fP`. Use `congr 1`. Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[gramX_true]`. Establish `e : Complex.I * ((2 * Real.pi * (((sg : ℤ) : ℝ)) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I * (((sg : ℤ) : ℂ))`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem S_cell (h : LocHyp sg L) {C : ℂ}
    (hJ : ∀ y : GR n, mR y = JJ n → ∀ f, IsSw f → L y f 0 = C * ∫ v, f v)
    (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    L (jG n * nG b) (fP (1 : PX m n)) 0 =
      C * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (1 : PX m n) b := by
  have hf := isSw_fP (1 : PX m n)
  rw [h.mul _ _ _ hf, hJ (jG n) mR_jG _ (h.sw _ _ hf), h.nU (nG b) b hb (mR_nG hb) _ hf]
  unfold secN fP
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [gramX_true]
  have e : Complex.I * ((2 * Real.pi * (((sg : ℤ) : ℝ)) : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * (((sg : ℤ) : ℂ)) := by
    push_cast
    ring
  rw [e]
  ring

/- English proof (translation)
Take `i0 : Fin n` from `⟨0, hn⟩`. Take `⟨C, hC0, hJ⟩` from `h.longWeylFunctional`. Take `⟨κ, hκ0, hκ⟩` from `gauss_cell (m := m) (n := n) sg 0`. Establish `key : ∀ t : ℝ, t ≠ 0 → L (pth i0 t) (fP 1) 0 * κ * star ((t : ℂ)⁻¹) ^ (m : ℤ) = F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C * (((t : ℂ)⁻¹ / (‖(t : ℂ)⁻¹‖ : ℂ)) ^ k * (‖(t : ℂ)⁻¹‖ : ℂ) ^ m)`. Introduce `t ht`.

Establish `ht' : (t : ℂ) ≠ 0` using `by exact_mod_cast ht`. Establish `hc : (-dT i0 t)ᴴ = -dT i0 t` using `by rw [Matrix.conjTranspose_neg, dT_herm]`. Establish `hdc : (-dT i0 t).det = (-1) ^ n * (t : ℂ)`. Rewrite using `[Matrix.det_neg, dT_det, Fintype.card_fin]`. Establish `hu : IsUnit (-dT i0 t).det`.

Rewrite using `[hdc]`. Conclude with `isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) ht')`. Establish `hci : ((-dT i0 t)⁻¹)ᴴ = (-dT i0 t)⁻¹`. Rewrite using `[Matrix.conjTranspose_nonsing_inv, hc]`. Establish `hd : (-(-dT i0 t)⁻¹).det = (t : ℂ)⁻¹`.

Rewrite using `[Matrix.det_neg, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdc, Fintype.card_fin, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]`. Establish `hnu : IsUnit (-(-dT i0 t)⁻¹).det`. Rewrite using `[hd]`. Conclude with `isUnit_iff_ne_zero.2 (inv_ne_zero ht')`. Establish `hp : pth i0 t = mG (-(-dT i0 t)⁻¹) * nG (-dT i0 t) * jG n * nG (-dT i0 t)⁻¹` using `nb_eq hc hu`.

Rewrite using `[hp, mul_assoc (mG _ * nG _) (jG n) _, S_law h hk _ _ hnu hc, S_cell h hJ _ hci, weight_factor_mul_parabolic _ _ _ _ _ (lower_left_block_levi_unipotent _ _ hnu hc), weight_factor_levi_unipotent _ _ _ _ _ hnu hc, hκ _ hci, hd, pq_sum]`. Simplify using `only [zpow_zero, one_mul, sub_zero]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : ∀ t : ℝ, 0 < t → L (pth i0 t) (fP 1) 0 * κ = F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C`. Introduce `t ht`.

Establish `e` using `key t ht.ne'`. Establish `hr : ((t : ℂ))⁻¹ = ((t⁻¹ : ℝ) : ℂ)` using `by push_cast; rfl`. Establish `hr0 : ((t⁻¹ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast inv_ne_zero ht.ne'`. Rewrite `e` using `[hr, Complex.star_def, Complex.conj_ofReal, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 ht.le), div_self hr0, one_zpow, one_mul, zpow_natCast]`. Apply `mul_right_cancel₀ (pow_ne_zero m hr0)` to reduce the goal to its premises.

Rewrite using `[e]`. Establish `hneg : ∀ t : ℝ, t < 0 → L (pth i0 t) (fP 1) 0 * κ = (-1) ^ k * (-1) ^ m * (F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C)`. Introduce `t ht`. Establish `e` using `key t ht.ne`. Establish `hr : ((t : ℂ))⁻¹ = ((t⁻¹ : ℝ) : ℂ)` using `by push_cast; rfl`.

Establish `hr0 : ((t⁻¹ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast inv_ne_zero ht.ne`. Rewrite `e` using `[hr, Complex.star_def, Complex.conj_ofReal, Complex.norm_real, Real.norm_of_nonpos (inv_nonpos.2 ht.le), Complex.ofReal_neg, div_neg, div_self hr0, neg_pow, zpow_natCast]`. Apply `mul_right_cancel₀ (pow_ne_zero m hr0)` to reduce the goal to its premises. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hφ : Continuous fun t : ℝ => L (pth i0 t) (fP 1) 0 * κ` using `((h.cont 1 0).comp (pth_cont i0)).mul continuous_const`. Establish `hψ : Continuous fun t : ℝ => F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C` using `((continuous_weight_factor_unitary _ _ _).comp (pth_cont i0)).mul continuous_const`. Establish `hs : Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) Filter.atTop (nhds 0)` using `tendsto_one_div_add_atTop_nhds_zero_nat`. Establish `hs' : Filter.Tendsto (fun j : ℕ => -(1 / ((j : ℝ) + 1))) Filter.atTop (nhds 0)`. Simplify using `using hs.neg`.

Establish `hpos' : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1)` using `fun j => by positivity`. Establish `e1 : L (pth i0 0) (fP 1) 0 * κ = F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C`. Establish `A` using `(hφ.tendsto 0).comp hs`. Establish `B` using `(hψ.tendsto 0).comp hs`. Use `tendsto_nhds_unique A ?_` and prove the remaining obligations.

Use `B.congr (fun j => ?_)` and prove the remaining obligations. Conclude with `(hpos _ (hpos' j)).symm`. Establish `e2 : L (pth i0 0) (fP 1) 0 * κ = (-1) ^ k * (-1) ^ m * (F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C)`. Establish `A` using `(hφ.tendsto 0).comp hs'`. Establish `B` using `((hψ.tendsto 0).comp hs').const_mul ((-1 : ℂ) ^ k * (-1) ^ m)`.

Use `tendsto_nhds_unique A ?_` and prove the remaining obligations. Use `B.congr (fun j => ?_)` and prove the remaining obligations. Conclude with `(hneg _ (neg_neg_of_pos (hpos' j))).symm`. Establish `hψ0 : F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C ≠ 0` using `mul_ne_zero (weight_factor_ne_zero _ _ _ _) hC0`. Establish `hε : ((-1 : ℂ)) ^ k * (-1) ^ m = 1`.

Rewrite `e2` using `[e1]`. Use `mul_right_cancel₀ hψ0 (e2.symm.trans (one_mul _).symm)` as an intermediate fact. Conclude with `this`. Break down `Int.even_or_odd (k - m) with he | ho` into its components or cases. Conclude with `he`.

It suffices to derive a contradiction. Establish `h1 : ((-1 : ℂ)) ^ (k - m) = -1` using `ho.neg_one_zpow`. Establish `h2 : ((-1 : ℂ)) ^ k = (-1) ^ (k - m) * (-1) ^ m`. Rewrite using `[← zpow_natCast, ← zpow_add₀ (by norm_num)]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hε` using `[h2, h1]`. Establish `h3 : ((-1 : ℂ)) ^ m * (-1) ^ m = 1`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.

Establish `: (-1 : ℂ) = 1` using `by linear_combination hε + h3`. Evaluate the numerical expressions using `at this`.
-/
theorem even_im_hermitian_sub (h : LocHyp sg L) (hn : 0 < n) {k : ℤ}
    (hk : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mLc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ m * f (Matrix.of u * a)) :
    Even (k - m) := by
  obtain i0 : Fin n := ⟨0, hn⟩
  obtain ⟨C, hC0, hJ⟩ := h.longWeylFunctional
  obtain ⟨κ, hκ0, hκ⟩ := gauss_cell (m := m) (n := n) sg 0
  have key : ∀ t : ℝ, t ≠ 0 →
      L (pth i0 t) (fP 1) 0 * κ * star ((t : ℂ)⁻¹) ^ (m : ℤ) =
        F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C *
          (((t : ℂ)⁻¹ / (‖(t : ℂ)⁻¹‖ : ℂ)) ^ k * (‖(t : ℂ)⁻¹‖ : ℂ) ^ m) := by
    intro t ht
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have hc : (-dT i0 t)ᴴ = -dT i0 t := by rw [Matrix.conjTranspose_neg, dT_herm]
    have hdc : (-dT i0 t).det = (-1) ^ n * (t : ℂ) := by
      rw [Matrix.det_neg, dT_det, Fintype.card_fin]
    have hu : IsUnit (-dT i0 t).det := by
      rw [hdc]
      exact isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) ht')
    have hci : ((-dT i0 t)⁻¹)ᴴ = (-dT i0 t)⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, hc]
    have hd : (-(-dT i0 t)⁻¹).det = (t : ℂ)⁻¹ := by
      rw [Matrix.det_neg, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdc, Fintype.card_fin,
        mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]
    have hnu : IsUnit (-(-dT i0 t)⁻¹).det := by
      rw [hd]
      exact isUnit_iff_ne_zero.2 (inv_ne_zero ht')
    have hp : pth i0 t = mG (-(-dT i0 t)⁻¹) * nG (-dT i0 t) * jG n * nG (-dT i0 t)⁻¹ :=
      nb_eq hc hu
    rw [hp, mul_assoc (mG _ * nG _) (jG n) _, S_law h hk _ _ hnu hc, S_cell h hJ _ hci,
      weight_factor_mul_parabolic _ _ _ _ _ (lower_left_block_levi_unipotent _ _ hnu hc), weight_factor_levi_unipotent _ _ _ _ _ hnu hc, hκ _ hci, hd, pq_sum]
    simp only [zpow_zero, one_mul, sub_zero]
    ring
  have hpos : ∀ t : ℝ, 0 < t →
      L (pth i0 t) (fP 1) 0 * κ = F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C := by
    intro t ht
    have e := key t ht.ne'
    have hr : ((t : ℂ))⁻¹ = ((t⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    have hr0 : ((t⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero ht.ne'
    rw [hr, Complex.star_def, Complex.conj_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 ht.le), div_self hr0, one_zpow, one_mul, zpow_natCast] at e
    apply mul_right_cancel₀ (pow_ne_zero m hr0)
    rw [e]
  have hneg : ∀ t : ℝ, t < 0 →
      L (pth i0 t) (fP 1) 0 * κ = (-1) ^ k * (-1) ^ m * (F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C) := by
    intro t ht
    have e := key t ht.ne
    have hr : ((t : ℂ))⁻¹ = ((t⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    have hr0 : ((t⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero ht.ne
    rw [hr, Complex.star_def, Complex.conj_ofReal, Complex.norm_real,
      Real.norm_of_nonpos (inv_nonpos.2 ht.le), Complex.ofReal_neg, div_neg, div_self hr0,
      neg_pow, zpow_natCast] at e
    apply mul_right_cancel₀ (pow_ne_zero m hr0)
    rw [e]
    ring
  have hφ : Continuous fun t : ℝ => L (pth i0 t) (fP 1) 0 * κ :=
    ((h.cont 1 0).comp (pth_cont i0)).mul continuous_const
  have hψ : Continuous fun t : ℝ => F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C :=
    ((continuous_weight_factor_unitary _ _ _).comp (pth_cont i0)).mul continuous_const
  have hs : Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hs' : Filter.Tendsto (fun j : ℕ => -(1 / ((j : ℝ) + 1))) Filter.atTop (nhds 0) := by
    simpa using hs.neg
  have hpos' : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  have e1 : L (pth i0 0) (fP 1) 0 * κ = F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C := by
    have A := (hφ.tendsto 0).comp hs
    have B := (hψ.tendsto 0).comp hs
    refine tendsto_nhds_unique A ?_
    refine B.congr (fun j => ?_)
    exact (hpos _ (hpos' j)).symm
  have e2 : L (pth i0 0) (fP 1) 0 * κ =
      (-1) ^ k * (-1) ^ m * (F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C) := by
    have A := (hφ.tendsto 0).comp hs'
    have B := ((hψ.tendsto 0).comp hs').const_mul ((-1 : ℂ) ^ k * (-1) ^ m)
    refine tendsto_nhds_unique A ?_
    refine B.congr (fun j => ?_)
    exact (hneg _ (neg_neg_of_pos (hpos' j))).symm
  have hψ0 : F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C ≠ 0 := mul_ne_zero (weight_factor_ne_zero _ _ _ _) hC0
  have hε : ((-1 : ℂ)) ^ k * (-1) ^ m = 1 := by
    rw [e1] at e2
    have := mul_right_cancel₀ hψ0 (e2.symm.trans (one_mul _).symm)
    exact this
  rcases Int.even_or_odd (k - m) with he | ho
  · exact he
  · exfalso
    have h1 : ((-1 : ℂ)) ^ (k - m) = -1 := ho.neg_one_zpow
    have h2 : ((-1 : ℂ)) ^ k = (-1) ^ (k - m) * (-1) ^ m := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      ring
    rw [h2, h1] at hε
    have h3 : ((-1 : ℂ)) ^ m * (-1) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    have : (-1 : ℂ) = 1 := by linear_combination hε + h3
    norm_num at this

/- English proof (translation)
Take `⟨k, hk⟩` from `h.mM`. Break down `Nat.eq_zero_or_pos n with hn0 | hn` into its components or cases. Substitute `hn0` using the available equality. Use `⟨0, fun y a ha hy f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[hk y a ha hy f hf]`.

Simplify using `[Matrix.det_isEmpty]`. Take `⟨j, hj⟩` from `even_im_hermitian_sub h hn hk`. Use `⟨m + j, fun y a ha hy f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[hk y a ha hy f hf]`. Use function extensionality and compare the values at `u`.

Use `congr 1`. Establish `hz : a.det ≠ 0` using `ha.ne_zero`. Establish `hr : (‖a.det‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hz`. Establish `hs : star a.det = (‖a.det‖ : ℂ) * (‖a.det‖ : ℂ) * (a.det)⁻¹`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ hz, mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs, show k = (m : ℤ) + (j + j) by omega, show (m : ℤ) - (m + j) = -j by ring]`. Establish `hzj` using `zpow_ne_zero j hz`. Establish `hrj` using `zpow_ne_zero j hr`.

Rewrite using `[div_zpow, zpow_add₀ hz, zpow_add₀ hz, zpow_add₀ hr, zpow_add₀ hr, zpow_add₀ hz, zpow_natCast, zpow_natCast, zpow_neg, mul_zpow, mul_zpow, inv_zpow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem LocHyp.mM' (h : LocHyp sg L) : ∃ e : ℤ, ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det →
    mR y = mLc a → ∀ f, IsSw f → L y f = fun u => a.det ^ e * (star a.det) ^ ((m : ℤ) - e) * f (Matrix.of u * a) := by
  obtain ⟨k, hk⟩ := h.mM
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    refine ⟨0, fun y a ha hy f hf => ?_⟩
    rw [hk y a ha hy f hf]
    simp [Matrix.det_isEmpty]
  · obtain ⟨j, hj⟩ := even_im_hermitian_sub h hn hk
    refine ⟨m + j, fun y a ha hy f hf => ?_⟩
    rw [hk y a ha hy f hf]
    funext u
    congr 1
    have hz : a.det ≠ 0 := ha.ne_zero
    have hr : (‖a.det‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
    have hs : star a.det = (‖a.det‖ : ℂ) * (‖a.det‖ : ℂ) * (a.det)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hz, mul_comm, Complex.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hs, show k = (m : ℤ) + (j + j) by omega, show (m : ℤ) - (m + j) = -j by ring]
    have hzj := zpow_ne_zero j hz
    have hrj := zpow_ne_zero j hr
    rw [div_zpow, zpow_add₀ hz, zpow_add₀ hz, zpow_add₀ hr, zpow_add₀ hr, zpow_add₀ hz,
      zpow_natCast, zpow_natCast, zpow_neg, mul_zpow, mul_zpow, inv_zpow]
    field_simp

end PositivityTheory.SiegelWeilFormula.KLI

end
