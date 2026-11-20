import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiIntH
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TLeftH

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.CB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS

variable {k r : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, hpk_apply]`. Distinguish the cases in `h : j = sigI k r i`. Substitute `h` using the available equality. Rewrite using `[if_pos (sig_sig i).symm, if_pos rfl, sgn_sig, star_sgn]`.

Establish `h' : ¬ i = sigI k r j` using `fun h2 => h (by rw [h2, sig_sig])`. Rewrite using `[if_neg h', if_neg h, star_zero]`.
-/
theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, hpk_apply]
  by_cases h : j = sigI k r i
  · subst h; rw [if_pos (sig_sig i).symm, if_pos rfl, sgn_sig, star_sgn]
  · have h' : ¬ i = sigI k r j := fun h2 => h (by rw [h2, sig_sig])
    rw [if_neg h', if_neg h, star_zero]

/- English proof (translation)
Establish `h2` using `HermitianLiftIdentities.hpk_sq (k := k) (r := r)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r`. Rewrite using `[hpk_conjT, Matrix.mul_assoc, h2, Matrix.mul_one]`. Rewrite using `[hpk_conjT, h2]`.
-/
theorem hpk_K : Hpk k r ∈ Kset k r := by
  have h2 := HermitianLiftIdentities.hpk_sq (k := k) (r := r)
  refine ⟨?_, ?_⟩
  · show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
    rw [hpk_conjT, Matrix.mul_assoc, h2, Matrix.mul_one]
  · rw [hpk_conjT, h2]

/- English proof (translation)
Simplify using `only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gN_sq (g : Mat k r) : (∑ i, ∑ j, Complex.normSq (g i j)) = (trace (gᴴ * g)).re := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

/- English proof (translation)
Unfold `gN`. Rewrite using `[gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]`.
-/
theorem gN_left {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) : gN (κ * g) = gN g := by
  unfold gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]

/- English proof (translation)
Establish `hκ' : κ * κᴴ = 1` using `mul_eq_one_comm.mp hκ`. Unfold `gN`. Rewrite using `[gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hκ', Matrix.mul_one]`.
-/
theorem gN_right {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) : gN (g * κ) = gN g := by
  have hκ' : κ * κᴴ = 1 := mul_eq_one_comm.mp hκ
  unfold gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hκ', Matrix.mul_one]

/- English proof (translation)
Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (Hpk k r) (Hpk k r), HermitianLiftIdentities.hpk_sq, Matrix.one_mul]`.
-/
theorem conjH_mul (a b : Mat k r) :
    Hpk k r * a * Hpk k r * (Hpk k r * b * Hpk k r) = Hpk k r * (a * b) * Hpk k r := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), HermitianLiftIdentities.hpk_sq, Matrix.one_mul]

/- English proof (translation)
Establish `h` using `HE_adj (HE k r (WithLp.toLp 2 v)) (WithLp.toLp 2 w)`. Rewrite `h` using `[HE_HE]`. Simplify using `only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp] at h`. Rewrite using `[dotProduct_comm (star (Hpk k r *ᵥ v)), ← h, dotProduct_comm]`.
-/
theorem dot_H (v w : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ v) ⬝ᵥ (Hpk k r *ᵥ w) = star v ⬝ᵥ w := by
  have h := HE_adj (HE k r (WithLp.toLp 2 v)) (WithLp.toLp 2 w)
  rw [HE_HE] at h
  simp only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp] at h
  rw [dotProduct_comm (star (Hpk k r *ᵥ v)), ← h, dotProduct_comm]

/- English proof (translation)
Unfold `Ga`. Simplify using `only [dot_H]`.
-/
theorem ga_H (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => Hpk k r *ᵥ Y a) = Ga k r l Y := by
  unfold Ga; simp only [dot_H]

/- English proof (translation)
Unfold `fsR xiR Del`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `e : (fun a => (Hpk k r * x * Hpk k r) *ᵥ phiV' k r a) = fun a => Hpk k r *ᵥ (x *ᵥ phiV k r a)`. Use function extensionality and compare the values at `a`. Rewrite using `[phiV', mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (Hpk k r * x), HermitianLiftIdentities.hpk_sq, Matrix.mul_one]`.

Rewrite using `[e, ga_H, Real.sqrt_eq_rpow, ← Real.rpow_mul (XI.ga_nonneg _ _ _ _)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fsR_conj (s : Fin (r + 1) → ℝ) (x : Mat k r) :
    fsR k r s (Hpk k r * x * Hpk k r) = xiR k r s x := by
  unfold fsR xiR Del
  refine Finset.prod_congr rfl fun l _ => ?_
  have e : (fun a => (Hpk k r * x * Hpk k r) *ᵥ phiV' k r a) = fun a => Hpk k r *ᵥ (x *ᵥ phiV k r a) := by
    funext a
    rw [phiV', mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (Hpk k r * x), HermitianLiftIdentities.hpk_sq, Matrix.mul_one]
  rw [e, ga_H, Real.sqrt_eq_rpow, ← Real.rpow_mul (XI.ga_nonneg _ _ _ _)]
  congr 1; ring

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _`.
-/
theorem xiR_nonneg (s : Fin (r + 1) → ℝ) (x : Mat k r) : 0 ≤ xiR k r s x :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _

/- English proof (translation)
Establish `h1 : 1 ≤ gN h` using `hGN k r h hh`. Establish `hp : 0 < gN h ^ A` using `Real.rpow_pos_of_pos (by linarith) A`. Establish `hc0 : 0 ≤ c` using `le_trans (mul_nonneg hp.le (norm_nonneg _)) (hF h hh)`. Establish `h2 : ‖F h‖ ≤ c * gN h ^ (-A)`. Rewrite using `[Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]; exact hF h hh`.

Rewrite using `[← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc0]`. Conclude with `ENNReal.ofReal_le_ofReal h2`.
-/
theorem norm_bd {E : Type*} [NormedAddCommGroup E] (hGN : GNLower) (F : Mat k r → E) (c A : ℝ)
    (hF : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) (h : Mat k r) (hh : h ∈ GV k r) :
    ‖F h‖ₑ ≤ ENNReal.ofReal c * ENNReal.ofReal (gN h ^ (-A)) := by
  have h1 : 1 ≤ gN h := hGN k r h hh
  have hp : 0 < gN h ^ A := Real.rpow_pos_of_pos (by linarith) A
  have hc0 : 0 ≤ c := le_trans (mul_nonneg hp.le (norm_nonneg _)) (hF h hh)
  have h2 : ‖F h‖ ≤ c * gN h ^ (-A) := by
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]; exact hF h hh
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc0]
  exact ENNReal.ofReal_le_ofReal h2

/- English proof (translation)
Establish `: 0 < gN (1 : Mat k r) ^ A` using `Real.rpow_pos_of_pos (by linarith [hGN k r 1 h1]) A`. Conclude with `le_trans (mul_nonneg this.le (norm_nonneg _)) (hF 1 h1)`.
-/
theorem c_nonneg {E : Type*} [NormedAddCommGroup E] (hGN : GNLower) (F : Mat k r → E) (c A : ℝ)
    (hF : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) (h1 : (1 : Mat k r) ∈ GV k r) : 0 ≤ c := by
  have : 0 < gN (1 : Mat k r) ^ A := Real.rpow_pos_of_pos (by linarith [hGN k r 1 h1]) A
  exact le_trans (mul_nonneg this.le (norm_nonneg _)) (hF 1 h1)

/- English proof (translation)
Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `h1 : ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s0 k r l` using `Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (by linarith [(hs l).1]) (by positivity)`. Establish `h2 : ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s0 k r l ≤ 2 * (r : ℝ) * r + ((r : ℝ) + 1) * k`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [s0, Fin.coe_castSucc, Fin.is_lt, ite_true, Fin.val_last, lt_self_iff_false, ite_false]`.

Establish `h3 : ∑ i : Fin r, ((i.val : ℝ) + 1) * 2 ≤ ∑ i : Fin r, (r : ℝ) * 2` using `Finset.sum_le_sum fun i _ => by`. Establish `h` using `Nat.succ_le_of_lt i.isLt`. Establish `: (i.val : ℝ) + 1 ≤ r` using `by exact_mod_cast h`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr : (0 : ℝ) ≤ r` using `by positivity`. Establish `h4 : 2 * (r : ℝ) * r + ((r : ℝ) + 1) * k ≤ AB k r` using `by unfold AB; nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_le (hk : 1 ≤ k) (s : Fin (r + 1) → ℝ) (hs : SAdm k r s) (A : ℝ) (hA : AB k r ≤ A) :
    ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ A := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s0 k r l :=
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (by linarith [(hs l).1]) (by positivity)
  have h2 : ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s0 k r l ≤ 2 * (r : ℝ) * r + ((r : ℝ) + 1) * k := by
    rw [Fin.sum_univ_castSucc]
    simp only [s0, Fin.coe_castSucc, Fin.is_lt, ite_true, Fin.val_last, lt_self_iff_false, ite_false]
    have h3 : ∑ i : Fin r, ((i.val : ℝ) + 1) * 2 ≤ ∑ i : Fin r, (r : ℝ) * 2 := Finset.sum_le_sum fun i _ => by
      have h := Nat.succ_le_of_lt i.isLt
      have : (i.val : ℝ) + 1 ≤ r := by exact_mod_cast h
      linarith
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    linarith
  have hr : (0 : ℝ) ≤ r := by positivity
  have h4 : 2 * (r : ℝ) * r + ((r : ℝ) + 1) * k ≤ AB k r := by unfold AB; nlinarith
  linarith

/- English proof (translation)
Establish `h1` using `(hs l).2`. Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Apply the tactic sequence `unfold s0 at h1; split_ifs at h1 <;> linarith`.
-/
theorem s_nonneg (hk : 1 ≤ k) (s : Fin (r + 1) → ℝ) (hs : SAdm k r s) (l : Fin (r + 1)) : 0 ≤ s l := by
  have h1 := (hs l).2
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold s0 at h1; split_ifs at h1 <;> linarith

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D A s hs hA hJ`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGN, -, -, -, hCG', -⟩` from `hB2`. Establish `hCG` using `hCG' k r`. Establish `hk` using `D.k_pos`. Establish `hμ` using `D.haarG`.

Establish `hHK : Hpk k r ∈ Kset k r` using `hpk_K`. Establish `hHG : Hpk k r ∈ GV k r` using `hHK.1`. Establish `hH2 : Hpk k r * Hpk k r = 1` using `HermitianLiftIdentities.hpk_sq k r`. Take `⟨CD, hCD⟩` from `hD k r s A hk (s_nonneg hk s hs) (sum_le hk s hs A hA)`. Establish `hgc : Continuous fun g : Mt k r => gN (Matrix.of g)`.

Unfold `gN`. Simplify using `only [Matrix.of_apply]`. Conclude with `Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))`. Establish `hΦm : Measurable fun g : Mt k r => ENNReal.ofReal (gN (Matrix.of g) ^ (-A))` using `(hgc.measurable.pow_const (-A)).ennreal_ofReal`. Establish `hΦinv : ∀ κ ∈ Kset k r, ∀ g : Mt k r, ENNReal.ofReal (gN (Matrix.of (lmulM κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∧ ENNReal.ofReal (gN (Matrix.of (rmulF κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A))` using `fun κ hκ g => ⟨by rw [show Matrix.of (lmulM κ g) = κ * Matrix.of g from rfl, gN_left _ hκ.2], by rw [show Matrix.of (rmulF κ g) = Matrix.of g * κ from rfl, gN_right _ hκ.2]⟩`.

Use `⟨CD * (JInt D.μG A s).toReal, fun F F' c c' _ _ hF hF' x hx y hy => ?_⟩` and prove the remaining obligations. Establish `hc0 : 0 ≤ c` using `c_nonneg hGN F c A hF hCG.one_mem`. Establish `hc0' : 0 ≤ c'` using `c_nonneg hGN F' c' A hF' hCG.one_mem`. Establish `hx' : Hpk k r * x * Hpk k r ∈ GV k r` using `hCG.mul_mem _ (hCG.mul_mem _ hHG _ hx) _ hHG`. Establish `hy' : Hpk k r * y * Hpk k r ∈ GV k r` using `hCG.mul_mem _ (hCG.mul_mem _ hHG _ hy) _ hHG`.

Establish `hxinv : (Hpk k r * x * Hpk k r)⁻¹ = Hpk k r * x⁻¹ * Hpk k r` using `Matrix.inv_eq_left_inv (by rw [conjH_mul, HermitianLiftIdentities.uh_inv_mul hx, Matrix.mul_one, hH2])`. Establish `hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r` using `by rw [ae_iff]; exact hμ.conc`. Use `set K : ℝ≥0∞ := ENNReal.ofReal c * ENNReal.ofReal c' * (CD : ℝ≥0∞) with hK`. Establish `hKt : K ≠ ⊤` using `ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top`. Establish `hpt : ∀ᵐ g ∂D.μG, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ≤ K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)))` using `by filter_upwards [hae] with g hg`.

Establish `hh : x⁻¹ * Matrix.of g * y ∈ GV k r` using `hCG.mul_mem _ (hCG.mul_mem _ (hCG.inv_mem _ hx) _ hg) _ hy`. Establish `e1 : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r = (Hpk k r * x * Hpk k r)⁻¹ * (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)`. Rewrite using `[hxinv, conjH_mul, conjH_mul]`. Establish `hhH : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r ∈ GV k r` using `hCG.mul_mem _ (hCG.mul_mem _ hHG _ hh) _ hHG`. Establish `gNe : gN (x⁻¹ * Matrix.of g * y) = gN (Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r)`.

Rewrite using `[gN_right _ hHK.2, gN_left _ hHK.2]`. Establish `b1` using `norm_bd hGN F c A hF _ hh`. Establish `b2 : ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A)) ≤ (CD : ℝ≥0∞) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))`. Rewrite using `[gNe, ← e1]`. Conclude with `hCD _ hhH`.

Establish `b3` using `norm_bd hGN F' c' A hF' _ hg`. Combine the equalities or inequalities in the displayed calculation. Establish `hsub : (∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG) = ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of g * (Hpk k r * y …`. Rewrite using `[← HermitianLiftIdentities.rmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of g * (Hpk k r * y * Hpk k r))), ← HermitianLiftIdentities.lmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) g)) ^ …`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations.

Use `show _ = ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g))) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g)) * (Hpk k r * y * Hpk k r))`. Rewrite using `[(hΦinv _ hHK _).2, (hΦinv _ hHK _).1]`. Both sides reduce to the same expression. Establish `hTb` using `hT k r s D.μG (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) hk hμ hΦm hΦinv _ hx' _ hy'`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[fsR_conj, fsR_conj, ENNReal.ofReal_mul (xiR_nonneg s x)]`. Rewrite using `[show (xiN k r s x : ℝ≥0∞) = ENNReal.ofReal (xiR k r s x) from rfl, show (xiN k r s y : ℝ≥0∞) = ENNReal.ofReal (xiR k r s y) from rfl]`. Rewrite using `[ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg) hc0), ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg), ENNReal.ofReal_mul (NNReal.coe_nonneg CD), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hJ.ne, hK]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coefStepC (hB2 : InductiveHeisenbergInputs) (hT : TBoth) (hD : DET) : CoefStep := by
  intro k r Wp Wq _ _ _ _ _ _ D A s hs hA hJ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGN, -, -, -, hCG', -⟩ := hB2
  have hCG := hCG' k r
  have hk := D.k_pos
  have hμ := D.haarG
  have hHK : Hpk k r ∈ Kset k r := hpk_K
  have hHG : Hpk k r ∈ GV k r := hHK.1
  have hH2 : Hpk k r * Hpk k r = 1 := HermitianLiftIdentities.hpk_sq k r
  obtain ⟨CD, hCD⟩ := hD k r s A hk (s_nonneg hk s hs) (sum_le hk s hs A hA)
  have hgc : Continuous fun g : Mt k r => gN (Matrix.of g) := by
    unfold gN
    simp only [Matrix.of_apply]
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
  have hΦm : Measurable fun g : Mt k r => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) :=
    (hgc.measurable.pow_const (-A)).ennreal_ofReal
  have hΦinv : ∀ κ ∈ Kset k r, ∀ g : Mt k r,
      ENNReal.ofReal (gN (Matrix.of (lmulM κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∧
      ENNReal.ofReal (gN (Matrix.of (rmulF κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) :=
    fun κ hκ g => ⟨by rw [show Matrix.of (lmulM κ g) = κ * Matrix.of g from rfl, gN_left _ hκ.2],
      by rw [show Matrix.of (rmulF κ g) = Matrix.of g * κ from rfl, gN_right _ hκ.2]⟩
  refine ⟨CD * (JInt D.μG A s).toReal, fun F F' c c' _ _ hF hF' x hx y hy => ?_⟩
  have hc0 : 0 ≤ c := c_nonneg hGN F c A hF hCG.one_mem
  have hc0' : 0 ≤ c' := c_nonneg hGN F' c' A hF' hCG.one_mem
  have hx' : Hpk k r * x * Hpk k r ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ hHG _ hx) _ hHG
  have hy' : Hpk k r * y * Hpk k r ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ hHG _ hy) _ hHG
  have hxinv : (Hpk k r * x * Hpk k r)⁻¹ = Hpk k r * x⁻¹ * Hpk k r :=
    Matrix.inv_eq_left_inv (by rw [conjH_mul, HermitianLiftIdentities.uh_inv_mul hx, Matrix.mul_one, hH2])
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by rw [ae_iff]; exact hμ.conc
  set K : ℝ≥0∞ := ENNReal.ofReal c * ENNReal.ofReal c' * (CD : ℝ≥0∞) with hK
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    ENNReal.coe_ne_top
  have hpt : ∀ᵐ g ∂D.μG, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ≤
      K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))) := by
    filter_upwards [hae] with g hg
    have hh : x⁻¹ * Matrix.of g * y ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ (hCG.inv_mem _ hx) _ hg) _ hy
    have e1 : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r = (Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r) := by
      rw [hxinv, conjH_mul, conjH_mul]
    have hhH : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r ∈ GV k r :=
      hCG.mul_mem _ (hCG.mul_mem _ hHG _ hh) _ hHG
    have gNe : gN (x⁻¹ * Matrix.of g * y) = gN (Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r) := by
      rw [gN_right _ hHK.2, gN_left _ hHK.2]
    have b1 := norm_bd hGN F c A hF _ hh
    have b2 : ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A)) ≤ (CD : ℝ≥0∞) * FsE k r s
        ((Hpk k r * x * Hpk k r)⁻¹ * (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) := by
      rw [gNe, ← e1]; exact hCD _ hhH
    have b3 := norm_bd hGN F' c' A hF' _ hg
    calc ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ
        ≤ (ENNReal.ofReal c * ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A))) *
          (ENNReal.ofReal c' * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) := mul_le_mul' b1 b3
      _ ≤ (ENNReal.ofReal c * ((CD : ℝ≥0∞) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
            (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)))) *
          (ENNReal.ofReal c' * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) :=
        mul_le_mul' (mul_le_mul' le_rfl b2) le_rfl
      _ = _ := by rw [hK]; ring
  have hsub : (∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG) =
      ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        Matrix.of g * (Hpk k r * y * Hpk k r)) ∂D.μG := by
    rw [← HermitianLiftIdentities.rmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of g * (Hpk k r * y * Hpk k r))),
      ← HermitianLiftIdentities.lmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) g)) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) g) * (Hpk k r * y * Hpk k r)))]
    refine lintegral_congr fun g => ?_
    show _ = ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g))) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g)) *
          (Hpk k r * y * Hpk k r))
    rw [(hΦinv _ hHK _).2, (hΦinv _ hHK _).1]
    rfl
  have hTb := hT k r s D.μG (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) hk hμ hΦm hΦinv _ hx' _ hy'
  calc (∫⁻ g, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g, K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))) ∂D.μG := lintegral_mono_ae hpt
    _ = K * ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG := lintegral_const_mul' _ _ hKt
    _ = K * (ENNReal.ofReal (fsR k r s (Hpk k r * x * Hpk k r) * fsR k r s (Hpk k r * y * Hpk k r)) *
        JInt D.μG A s) := by rw [hsub, hTb]; rfl
    _ = ENNReal.ofReal (CD * (JInt D.μG A s).toReal * c * c') * (xiN k r s x : ℝ≥0∞) *
        (xiN k r s y : ℝ≥0∞) := by
      rw [fsR_conj, fsR_conj, ENNReal.ofReal_mul (xiR_nonneg s x)]
      rw [show (xiN k r s x : ℝ≥0∞) = ENNReal.ofReal (xiR k r s x) from rfl,
        show (xiN k r s y : ℝ≥0∞) = ENNReal.ofReal (xiR k r s y) from rfl]
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg) hc0),
        ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg), ENNReal.ofReal_mul (NNReal.coe_nonneg CD),
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hJ.ne, hK]
      ring

end ReciprocityTheory.ChartRestriction.DS.Xi.CB
