import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLeadMinorDecay
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DecGapBound

/- English proof (translation)
Establish `hJY : Jm ε * Y * Jm ε = -Y`. Rewrite using `[mul_assoc, h.2, mul_neg, ← mul_assoc, Jm_mul_self, one_mul]`. Establish `hconj` using `exp_signature_conj ε Y`. Rewrite `hconj` using `[hJY]`. Establish `hdetJ : (Jm ε).det * (Jm ε).det = 1`.

Rewrite using `[← Matrix.det_mul, Jm_mul_self, Matrix.det_one]`. Establish `h1 : (NormedSpace.exp (-Y)).det * (NormedSpace.exp Y).det = 1`. Rewrite using `[← Matrix.det_mul, matrix_exp_neg_mul_exp, Matrix.det_one]`. Establish `h2 : (NormedSpace.exp (-Y)).det = (NormedSpace.exp Y).det`. Rewrite using `[hconj, Matrix.det_mul, Matrix.det_mul]`.

Take the linear combination `(NormedSpace.exp Y).det * hdetJ`. Rewrite `h1` using `[h2]`. Conclude with `h1`.
-/
lemma det_exp_sq {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inP ε Y) :
    (NormedSpace.exp Y).det * (NormedSpace.exp Y).det = 1 := by

  have hJY : Jm ε * Y * Jm ε = -Y := by
    rw [mul_assoc, h.2, mul_neg, ← mul_assoc, Jm_mul_self, one_mul]
  have hconj := exp_signature_conj ε Y
  rw [hJY] at hconj
  have hdetJ : (Jm ε).det * (Jm ε).det = 1 := by
    rw [← Matrix.det_mul, Jm_mul_self, Matrix.det_one]
  have h1 : (NormedSpace.exp (-Y)).det * (NormedSpace.exp Y).det = 1 := by
    rw [← Matrix.det_mul, matrix_exp_neg_mul_exp, Matrix.det_one]
  have h2 : (NormedSpace.exp (-Y)).det = (NormedSpace.exp Y).det := by
    rw [hconj, Matrix.det_mul, Matrix.det_mul]
    linear_combination (NormedSpace.exp Y).det * hdetJ
  rw [h2] at h1
  exact h1

/- English proof (translation)
Take `⟨m, hm⟩` from `hlam.2 a`. Establish `e : lam a + Formalism.QuantumDeterminants.rhoStd n a = ((m + (n : ℤ) - 1 - ((a : ℕ) : ℤ) : ℤ) : ℝ)`. Simplify using `only [Formalism.QuantumDeterminants.rhoStd]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `GlobalTheory.Dec.muInt`. Rewrite using `[e, Int.floor_intCast]`.
-/
lemma muInt_cast {n : ℕ} {lam : Fin n → ℝ} (hlam : IsHCParam lam) (a : Fin n) :
    (muInt lam a : ℝ) = lam a + Formalism.QuantumDeterminants.rhoStd n a := by
  obtain ⟨m, hm⟩ := hlam.2 a
  have e : lam a + Formalism.QuantumDeterminants.rhoStd n a = ((m + (n : ℤ) - 1 - ((a : ℕ) : ℤ) : ℤ) : ℝ) := by
    simp only [Formalism.QuantumDeterminants.rhoStd]
    push_cast
    linarith
  unfold GlobalTheory.Dec.muInt
  rw [e, Int.floor_intCast]

/- English proof (translation)
Take `⟨hpos, hprod⟩` from `GlobalTheory.MinorDecay.prod_leadMinor_decay n ε lam h X km hlam hgap hX hk`. Use `set Z := km⁻¹ * NormedSpace.exp X * km with hZ`. Establish `hR : decHS h (rkR ε) (Real.sqrt (hs X)) = Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card : ℕ) : ℝ))))`. Unfold `GlobalTheory.Dec.decHS GlobalTheory.Count.rkR`. Rewrite using `[Real.sq_sqrt (GlobalTheory.MinorDecay.hs_nonneg X)]`.

Rewrite using `[hR]`. Use `le_trans (le_of_eq ?_) hprod` and prove the remaining obligations. Establish `hre : ∀ (l : ℕ) (hl : l ≤ n), ‖leadMinor Z l hl‖ = (leadMinor Z l hl).re`. Introduce `l hl`. Take `⟨h1, h2⟩` from `hpos l hl`.

Use `set z := leadMinor Z l hl`. Establish `e : z = (z.re : ℂ)` using `Complex.ext (by simp) (by simp [h2])`. Rewrite using `[e, Complex.norm_real, Real.norm_of_nonneg h1.le, Complex.ofReal_re]`. Establish `hinv : km⁻¹ * km = 1` using `Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 hk.1))`. Establish `hdet2 : Z.det = (NormedSpace.exp X).det`.

Rewrite using `[hZ, Matrix.det_mul, Matrix.det_mul, mul_comm (km⁻¹.det), mul_assoc, ← Matrix.det_mul, hinv, Matrix.det_one, mul_one]`. Break down `n with _ | m` into its components or cases. Simplify using `[GlobalTheory.Dec.Phi]`. Use `show ‖Phi lam Z‖ = ∏ i : Fin m, (leadMinor Z (i.val + 1) (by omega)).re ^ (-(lam i.castSucc - lam i.succ + 1))`. Establish `hlast : ∀ hl : m + 1 ≤ m + 1, ‖leadMinor Z (m + 1) hl‖ = 1`.

Introduce `hl`. Rewrite using `[hre]`. Take `⟨h1, h2⟩` from `hpos (m + 1) hl`. Establish `hdet : leadMinor Z (m + 1) hl = Z.det`. Unfold `leadMinor`.

Use `congr 1`. Establish `hsq` using `det_exp_sq hX`. Rewrite `hsq` using `[← hdet2, ← hdet]`. Establish `h3` using `congrArg Complex.re hsq`. Simplify using `only [Complex.mul_re, h2, mul_zero, sub_zero, Complex.one_re] at h3`.

Use the polynomial consequences of the given equalities and inequalities. Unfold `GlobalTheory.Dec.Phi`. Rewrite using `[norm_prod, Fin.prod_univ_castSucc]`. Simplify using `only [norm_zpow, Fin.val_last, Fin.coe_castSucc]`. Rewrite using `[hlast, _root_.one_zpow, mul_one]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hre, ← Real.rpow_intCast]`. Use `congr 1`. Establish `hi : (i.castSucc : ℕ) + 1 < m + 1` using `by simp`. Establish `e : (⟨(i.castSucc : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ` using `Fin.ext (by simp)`.

Simplify using `only [GlobalTheory.Dec.sInt, dif_pos hi, e]`. Use `push_cast`. Rewrite using `[muInt_cast hlam, muInt_cast hlam]`. Simplify using `only [Formalism.QuantumDeterminants.rhoStd, Fin.coe_castSucc, Fin.val_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_Phi_le {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {X km : Matrix (Fin n) (Fin n) ℂ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h)
    (hX : inP ε X) (hk : km ∈ Kset ε) :
    ‖Phi lam (km⁻¹ * NormedSpace.exp X * km)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := by
  obtain ⟨hpos, hprod⟩ := GlobalTheory.MinorDecay.prod_leadMinor_decay n ε lam h X km hlam hgap hX hk
  set Z := km⁻¹ * NormedSpace.exp X * km with hZ
  have hR : decHS h (rkR ε) (Real.sqrt (hs X)) = Real.exp (-(h / 8) * min (hs X)
      (Real.sqrt (hs X) / Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
        (univ.filter fun a => ε a = false).card : ℕ) : ℝ)))) := by
    unfold GlobalTheory.Dec.decHS GlobalTheory.Count.rkR
    rw [Real.sq_sqrt (GlobalTheory.MinorDecay.hs_nonneg X)]
  rw [hR]
  refine le_trans (le_of_eq ?_) hprod

  have hre : ∀ (l : ℕ) (hl : l ≤ n), ‖leadMinor Z l hl‖ = (leadMinor Z l hl).re := by
    intro l hl
    obtain ⟨h1, h2⟩ := hpos l hl
    set z := leadMinor Z l hl
    have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h2])
    rw [e, Complex.norm_real, Real.norm_of_nonneg h1.le, Complex.ofReal_re]
  have hinv : km⁻¹ * km = 1 :=
    Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 hk.1))
  have hdet2 : Z.det = (NormedSpace.exp X).det := by
    rw [hZ, Matrix.det_mul, Matrix.det_mul, mul_comm (km⁻¹.det), mul_assoc, ← Matrix.det_mul, hinv,
      Matrix.det_one, mul_one]
  rcases n with _ | m
  · simp [GlobalTheory.Dec.Phi]
  · show ‖Phi lam Z‖ = ∏ i : Fin m, (leadMinor Z (i.val + 1) (by omega)).re ^
      (-(lam i.castSucc - lam i.succ + 1))

    have hlast : ∀ hl : m + 1 ≤ m + 1, ‖leadMinor Z (m + 1) hl‖ = 1 := by
      intro hl
      rw [hre]
      obtain ⟨h1, h2⟩ := hpos (m + 1) hl
      have hdet : leadMinor Z (m + 1) hl = Z.det := by
        unfold leadMinor
        congr 1
      have hsq := det_exp_sq hX
      rw [← hdet2, ← hdet] at hsq
      have h3 := congrArg Complex.re hsq
      simp only [Complex.mul_re, h2, mul_zero, sub_zero, Complex.one_re] at h3
      nlinarith
    unfold GlobalTheory.Dec.Phi
    rw [norm_prod, Fin.prod_univ_castSucc]
    simp only [norm_zpow, Fin.val_last, Fin.coe_castSucc]
    rw [hlast, _root_.one_zpow, mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hre, ← Real.rpow_intCast]
    congr 1
    have hi : (i.castSucc : ℕ) + 1 < m + 1 := by simp
    have e : (⟨(i.castSucc : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ := Fin.ext (by simp)
    simp only [GlobalTheory.Dec.sInt, dif_pos hi, e]
    push_cast
    rw [muInt_cast hlam, muInt_cast hlam]
    simp only [Formalism.QuantumDeterminants.rhoStd, Fin.coe_castSucc, Fin.val_succ]
    push_cast
    ring

/- English proof (translation)
Unfold `GlobalTheory.Dec.Phi`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Establish `e : leadMinor (1 : Matrix (Fin n) (Fin n) ℂ) (i.val + 1) i.isLt = 1`. Unfold `leadMinor`. Rewrite using `[Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]`.

Rewrite using `[e, _root_.one_zpow]`.
-/
lemma Phi_one' {n : ℕ} (lam : Fin n → ℝ) : Phi lam (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold GlobalTheory.Dec.Phi
  refine Finset.prod_eq_one fun i _ => ?_
  have e : leadMinor (1 : Matrix (Fin n) (Fin n) ℂ) (i.val + 1) i.isLt = 1 := by
    unfold leadMinor
    rw [Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
  rw [e, _root_.one_zpow]

/- English proof (translation)
Conclude with `Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`.
-/
lemma continuous_toMK {n : ℕ} (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) := by
  exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

/- English proof (translation)
Use `set A := ∫ x, ‖a x‖ ^ 2 ∂μ with hA`. Use `set B := ∫ x, ‖b x‖ ^ 2 ∂μ with hB`. Establish `ma : AEStronglyMeasurable (fun x => ‖a x‖) μ`. Use `(Real.continuous_sqrt.comp_aestronglyMeasurable i1.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Conclude with `Real.sqrt_sq (norm_nonneg _)`. Establish `mb : AEStronglyMeasurable (fun x => ‖b x‖) μ`. Use `(Real.continuous_sqrt.comp_aestronglyMeasurable i2.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Conclude with `Real.sqrt_sq (norm_nonneg _)`.

Establish `La : MemLp (fun x => ‖a x‖) (ENNReal.ofReal 2) μ`. Rewrite using `[ENNReal.ofReal_ofNat]`. Conclude with `(memLp_two_iff_integrable_sq ma).2 i1`. Establish `Lb : MemLp (fun x => ‖b x‖) (ENNReal.ofReal 2) μ`. Rewrite using `[ENNReal.ofReal_ofNat]`.

Conclude with `(memLp_two_iff_integrable_sq mb).2 i2`. Establish `hH` using `integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two (Filter.Eventually.of_forall fun x => norm_nonneg (a x)) (Filter.Eventually.of_forall fun x => norm_nonneg (b x)) La Lb`. Simplify using `only [Real.rpow_two] at hH`. Rewrite `hH` using `[← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]`. Establish `iab : Integrable (fun x => ‖a x‖ * ‖b x‖) μ`.

Use `Integrable.mono' ((i1.add i2).div_const 2) (ma.mul mb) (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Rewrite using `[Real.norm_of_nonneg (by positivity)]`. Use polynomial arithmetic with `[sq_nonneg (‖a x‖ - ‖b x‖)]`. Establish `h1 : ‖∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * (Real.sqrt A * Real.sqrt B)`.

Combine the equalities or inequalities in the displayed calculation. Use `norm_integral_le_of_norm_le (iab.const_mul M) (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hφ x) (by positivity)`. Use `_ = M * ∫ x, ‖a x‖ * ‖b x‖ ∂μ := integral_const_mul M _`.

Use `_ ≤ M * (Real.sqrt A * Real.sqrt B) := mul_le_mul_of_nonneg_left hH hM`. Establish `hVs : V = Real.sqrt ((d : ℝ) * A)` using `by rw [ha, Real.sqrt_sq hV]`. Establish `hUs : U = Real.sqrt ((d : ℝ) * B)` using `by rw [hb, Real.sqrt_sq hU]`. Establish `hdd` using `Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) d)`. Rewrite using `[norm_mul, Complex.norm_natCast, hVs, hUs, Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_mul (Nat.cast_nonneg d)]`.

Use `le_trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) (le_of_eq ?_)` and prove the remaining obligations. Take the linear combination `(-(M * Real.sqrt A * Real.sqrt B)) * hdd`.
-/
lemma weighted_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) (d : ℕ) (φ a b : α → ℂ)
    (M U V : ℝ) (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V) (hφ : ∀ x, ‖φ x‖ ≤ M)
    (i1 : Integrable (fun x => ‖a x‖ ^ 2) μ) (i2 : Integrable (fun x => ‖b x‖ ^ 2) μ)
    (ha : (d : ℝ) * ∫ x, ‖a x‖ ^ 2 ∂μ = V ^ 2) (hb : (d : ℝ) * ∫ x, ‖b x‖ ^ 2 ∂μ = U ^ 2) :
    ‖(d : ℂ) * ∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * U * V := by
  set A := ∫ x, ‖a x‖ ^ 2 ∂μ with hA
  set B := ∫ x, ‖b x‖ ^ 2 ∂μ with hB
  have ma : AEStronglyMeasurable (fun x => ‖a x‖) μ := by
    refine (Real.continuous_sqrt.comp_aestronglyMeasurable i1.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (norm_nonneg _)
  have mb : AEStronglyMeasurable (fun x => ‖b x‖) μ := by
    refine (Real.continuous_sqrt.comp_aestronglyMeasurable i2.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (norm_nonneg _)
  have La : MemLp (fun x => ‖a x‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq ma).2 i1
  have Lb : MemLp (fun x => ‖b x‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq mb).2 i2

  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x => norm_nonneg (a x))
    (Filter.Eventually.of_forall fun x => norm_nonneg (b x)) La Lb
  simp only [Real.rpow_two] at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  have iab : Integrable (fun x => ‖a x‖ * ‖b x‖) μ := by
    refine Integrable.mono' ((i1.add i2).div_const 2) (ma.mul mb) (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  have h1 : ‖∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * (Real.sqrt A * Real.sqrt B) := by
    calc ‖∫ x, φ x * (a x * b x) ∂μ‖ ≤ ∫ x, M * (‖a x‖ * ‖b x‖) ∂μ := by
          refine norm_integral_le_of_norm_le (iab.const_mul M) (Filter.Eventually.of_forall fun x => ?_)
          rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_right (hφ x) (by positivity)
      _ = M * ∫ x, ‖a x‖ * ‖b x‖ ∂μ := integral_const_mul M _
      _ ≤ M * (Real.sqrt A * Real.sqrt B) := mul_le_mul_of_nonneg_left hH hM
  have hVs : V = Real.sqrt ((d : ℝ) * A) := by rw [ha, Real.sqrt_sq hV]
  have hUs : U = Real.sqrt ((d : ℝ) * B) := by rw [hb, Real.sqrt_sq hU]
  have hdd := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) d)
  rw [norm_mul, Complex.norm_natCast, hVs, hUs, Real.sqrt_mul (Nat.cast_nonneg d),
    Real.sqrt_mul (Nat.cast_nonneg d)]
  refine le_trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) (le_of_eq ?_)
  linear_combination (-(M * Real.sqrt A * Real.sqrt B)) * hdd

/- English proof (translation)
Use `haveI : CompleteSpace H := hDS.1`. Take `⟨w, hw⟩` from `(GlobalTheory.LowKProj.lowK_projection n ε lam H σ hDS).1`. Establish `hURep` using `hDS.2.2.1`. Establish `hform` using `hF n ε lam H σ hlam hDS h hgap hh w hw`. Establish `hK : ∀ k : KG ε, toMK k ∈ Kset ε` using `fun k => k.2`.

Establish `hUJ : ∀ k : KG ε, toMK k ∈ UJset ε` using `fun k => GlobalTheory.LowKProj.mem_UJset_of_Kset (hK k)`. Establish `hinv : ∀ k : KG ε, (toMK k)⁻¹ * toMK k = 1` using `fun k => Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 (hK k).1))`. Establish `hcont : ∀ x : H, Continuous (fun k : KG ε => σ (toMK k) x)` using `fun x => (hURep.2.2 x).comp_continuous (continuous_toMK ε) hUJ`. Establish `hnorm : ∀ (k : KG ε) (x : H), ‖σ (toMK k) x‖ = ‖x‖` using `fun k x => hURep.2.1 _ (hUJ k) x`. Establish `hint : ∀ x : H, Integrable (fun k : KG ε => ‖⟪x, σ (toMK k) w⟫_ℂ‖ ^ 2) (muK ε)`.

Introduce `x`. Use `Integrable.of_bound ((continuous_const.inner (hcont w)).norm.pow 2).aestronglyMeasurable (‖x‖ ^ 2) (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Establish `h1 : ‖⟪x, σ (toMK k) w⟫_ℂ‖ ≤ ‖x‖`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.norm_of_nonneg (by positivity)]`.

Conclude with `pow_le_pow_left₀ (norm_nonneg _) h1 2`. Establish `h0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ)` using `by simp [inP, inG]`. Establish `horth : ∀ x ∈ lowKSub ε lam σ, (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) * ∫ k, ‖⟪x, σ (toMK k) w⟫_ℂ‖ ^ 2 ∂(muK ε) = ‖x‖ ^ 2`. Introduce `x hx`. Establish `hpt : ∀ k : KG ε, ⟪x, σ (toMK k) w⟫_ℂ * ⟪σ (toMK k) w, x⟫_ℂ = ((‖⟪x, σ (toMK k) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ)` using `fun k => by`.

Rewrite using `[← inner_conj_symm (σ (toMK k) w) x, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `e` using `hform 0 h0 x hx x hx`. Simplify using `only [NormedSpace.exp_zero, hURep.1.1, ContinuousLinearMap.one_apply, mul_one, hinv, Phi_one', one_mul, hpt] at e`. Rewrite `e` using `[integral_complex_ofReal, inner_self_eq_norm_sq_to_K]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Use `push_cast`. Take the linear combination `-e`. Establish `hsym : (fun k : KG ε => ‖⟪σ (toMK k) w, u⟫_ℂ‖ ^ 2) = (fun k : KG ε => ‖⟪u, σ (toMK k) w⟫_ℂ‖ ^ 2)` using `funext fun k => by rw [norm_inner_symm]`. Establish `hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X))`. Unfold `GlobalTheory.Dec.decHS`.

Check the signs of the components of the expression. Establish `hmain` using `weighted_bound (muK ε) (Module.finrank ℂ (lowKSub ε lam σ)) (fun k => Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k)) (fun k => ⟪v, σ (toMK k) w⟫_ℂ) (fun k => ⟪σ (toMK k) w, u⟫_ℂ) (decHS h (rkR ε) (Real.sqrt (hs X))) ‖u‖ ‖v‖ hM (norm_nonneg u) (norm_nonneg v) (fun k => norm_Ph …`. Rewrite using `[hform X hX u hu v hv]`. Conclude with `hmain`.
-/
lemma dec_exp (hF : FormulaGap) (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hlam : IsHCParam lam) (hDS : IsDS ε lam σ)
    (h : ℝ) (hgap : GapAtLeast ε lam h)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) (u : H) (hu : u ∈ lowKSub ε lam σ)
    (v : H) (hv : v ∈ lowKSub ε lam σ) :
    ‖⟪v, σ (NormedSpace.exp X) u⟫_ℂ‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) * ‖u‖ * ‖v‖ := by
  haveI : CompleteSpace H := hDS.1
  obtain ⟨w, hw⟩ := (GlobalTheory.LowKProj.lowK_projection n ε lam H σ hDS).1
  have hURep := hDS.2.2.1
  have hform := hF n ε lam H σ hlam hDS h hgap hh w hw
  have hK : ∀ k : KG ε, toMK k ∈ Kset ε := fun k => k.2
  have hUJ : ∀ k : KG ε, toMK k ∈ UJset ε := fun k => GlobalTheory.LowKProj.mem_UJset_of_Kset (hK k)
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ * toMK k = 1 := fun k =>
    Matrix.nonsing_inv_mul _
      (Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 (hK k).1))
  have hcont : ∀ x : H, Continuous (fun k : KG ε => σ (toMK k) x) := fun x =>
    (hURep.2.2 x).comp_continuous (continuous_toMK ε) hUJ
  have hnorm : ∀ (k : KG ε) (x : H), ‖σ (toMK k) x‖ = ‖x‖ := fun k x => hURep.2.1 _ (hUJ k) x

  have hint : ∀ x : H, Integrable (fun k : KG ε => ‖⟪x, σ (toMK k) w⟫_ℂ‖ ^ 2) (muK ε) := by
    intro x
    refine Integrable.of_bound ((continuous_const.inner (hcont w)).norm.pow 2).aestronglyMeasurable
      (‖x‖ ^ 2) (Filter.Eventually.of_forall fun k => ?_)
    have h1 : ‖⟪x, σ (toMK k) w⟫_ℂ‖ ≤ ‖x‖ := by
      calc ‖⟪x, σ (toMK k) w⟫_ℂ‖ ≤ ‖x‖ * ‖σ (toMK k) w‖ := norm_inner_le_norm _ _
        _ = ‖x‖ := by rw [hnorm, hw.1, mul_one]
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

  have h0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by simp [inP, inG]
  have horth : ∀ x ∈ lowKSub ε lam σ, (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) *
      ∫ k, ‖⟪x, σ (toMK k) w⟫_ℂ‖ ^ 2 ∂(muK ε) = ‖x‖ ^ 2 := by
    intro x hx
    have hpt : ∀ k : KG ε, ⟪x, σ (toMK k) w⟫_ℂ * ⟪σ (toMK k) w, x⟫_ℂ =
        ((‖⟪x, σ (toMK k) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [← inner_conj_symm (σ (toMK k) w) x, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e := hform 0 h0 x hx x hx
    simp only [NormedSpace.exp_zero, hURep.1.1, ContinuousLinearMap.one_apply, mul_one, hinv,
      Phi_one', one_mul, hpt] at e
    rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at e
    apply Complex.ofReal_injective
    push_cast
    linear_combination -e
  have hsym : (fun k : KG ε => ‖⟪σ (toMK k) w, u⟫_ℂ‖ ^ 2) =
      (fun k : KG ε => ‖⟪u, σ (toMK k) w⟫_ℂ‖ ^ 2) := funext fun k => by rw [norm_inner_symm]
  have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := by
    unfold GlobalTheory.Dec.decHS
    positivity
  have hmain := weighted_bound (muK ε) (Module.finrank ℂ (lowKSub ε lam σ))
    (fun k => Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k))
    (fun k => ⟪v, σ (toMK k) w⟫_ℂ) (fun k => ⟪σ (toMK k) w, u⟫_ℂ)
    (decHS h (rkR ε) (Real.sqrt (hs X))) ‖u‖ ‖v‖ hM (norm_nonneg u) (norm_nonneg v)
    (fun k => norm_Phi_le hlam hgap hX (hK k)) (hint v) (by rw [hsym]; exact hint u)
    (horth v hv) (by rw [hsym]; exact horth u hu)
  rw [hform X hX u hu v hv]
  exact hmain

/- English proof (translation)
Unfold `GlobalTheory.Dec.decHS GlobalTheory.Count.decE`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hs2 : 0 < Real.sqrt 2` using `by positivity`. Establish `h1 : 2 * d ^ 2 ≤ t ^ 2`. Establish `e : (Real.sqrt 2 * d) ^ 2 = 2 * d ^ 2`.

Rewrite using `[mul_pow, Real.sq_sqrt (by norm_num)]`. Rewrite using `[← e]`. Conclude with `pow_le_pow_left₀ (mul_nonneg hs2.le hd) hdt 2`. Establish `h2 : d / Real.sqrt q ≤ t / Real.sqrt (2 * q)`. Rewrite using `[Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← div_div]`.

Establish `hdt' : d ≤ t / Real.sqrt 2`. Rewrite using `[le_div_iff₀ hs2]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `div_le_div_of_nonneg_right hdt' (Real.sqrt_nonneg _)`. Conclude with `mul_le_mul_of_nonpos_left (min_le_min h1 h2) (by linarith)`.
-/
lemma decHS_le_decE {h d t : ℝ} (q : ℕ) (hh : 0 ≤ h) (hd : 0 ≤ d) (hdt : Real.sqrt 2 * d ≤ t) :
    decHS h q t ≤ decE q h d := by
  unfold GlobalTheory.Dec.decHS GlobalTheory.Count.decE
  apply Real.exp_le_exp.mpr
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have h1 : 2 * d ^ 2 ≤ t ^ 2 := by
    have e : (Real.sqrt 2 * d) ^ 2 = 2 * d ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    rw [← e]
    exact pow_le_pow_left₀ (mul_nonneg hs2.le hd) hdt 2
  have h2 : d / Real.sqrt q ≤ t / Real.sqrt (2 * q) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← div_div]
    have hdt' : d ≤ t / Real.sqrt 2 := by
      rw [le_div_iff₀ hs2]
      linarith
    exact div_le_div_of_nonneg_right hdt' (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonpos_left (min_le_min h1 h2) (by linarith)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `h0 : dOp g = 0`. Unfold `GlobalTheory.Count.dOp`. Establish `e : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g) = 0`. Use extensionality with `x i`.

Conclude with `i.elim0`. Rewrite using `[e, norm_zero, Real.log_zero]`. Establish `h1 : dHS g = 0`. Unfold `GlobalTheory.Count.dHS`. Simplify using the standard rewrite rules.

Rewrite using `[h0, h1]`. Simplify using the standard rewrite rules. Establish `hg' : inUJ ε g` using `hg`. Take `⟨h0, h1, -⟩` from `GlobalTheory.Count.Cartan.dOp_bounds hn (mul_exp_neg_polarLog_mem_compact hg').1 (polarLog_mem_hermitian_part hg')`. Rewrite `h0`, `h1` using `[← polar_decomposition_eq]`.

Rewrite using `[GlobalTheory.Count.Cartan.dHS_eq_log hg']`. Conclude with `⟨h0, h1⟩`.
-/
lemma dOp_facts {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    0 ≤ dOp g ∧ Real.sqrt 2 * dOp g ≤ dHS g := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : dOp g = 0 := by
      unfold GlobalTheory.Count.dOp
      have e : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g) = 0 := by
        ext x i
        exact i.elim0
      rw [e, norm_zero, Real.log_zero]
    have h1 : dHS g = 0 := by
      unfold GlobalTheory.Count.dHS
      simp
    rw [h0, h1]
    simp
  · have hg' : inUJ ε g := hg
    obtain ⟨h0, h1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn (mul_exp_neg_polarLog_mem_compact hg').1 (polarLog_mem_hermitian_part hg')
    rw [← polar_decomposition_eq] at h0 h1
    rw [GlobalTheory.Count.Cartan.dHS_eq_log hg']
    exact ⟨h0, h1⟩

end GlobalTheory.DecGapBound
