import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselZhatInvAndRegularIffStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationAbsoluteSidePieceBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBoundByDyadicSummationStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengthsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberMulTopMinorNormLeTwoPowStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairingsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopMinorAndGramNumberLeMajorantLengthsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberAndFibreSetsMeasurableStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsConv

variable {k r : ℕ}

/- English proof (translation)
Unfold `Dmin`. Rewrite using `[(GlobalTheory.T.besselZhat_inv_and_regular_iff k r z z' γ hγ).1, ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]`.
-/
theorem dmin_inv (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (hγ : γ ∈ GG k r) (l : Fin (r + 2)) :
    Dmin k r z' z γ⁻¹ l = star (Dmin k r z z' γ l) := by
  unfold Dmin
  rw [(GlobalTheory.T.besselZhat_inv_and_regular_iff k r z z' γ hγ).1, ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]

/- English proof (translation)
Unfold `Dr`. Rewrite using `[dmin_inv z z' hγ, norm_star]`.
-/
theorem dr_inv (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (hγ : γ ∈ GG k r) :
    Dr k r z' z γ⁻¹ = Dr k r z z' γ := by
  unfold Dr
  rw [dmin_inv z z' hγ, norm_star]

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7⟩` from `h`. Use `⟨h2, h1, h4, h3, isClosedSub_GG.2.2.2.2 _ h5, ?_, by rwa [dr_inv z z' h5]⟩` and prove the remaining obligations. Unfold `Gf at h6 ⊢`. Rewrite using `[dmin_inv z z' h5, dmin_inv z z' h5, mul_comm (Tz k r z')]`. Simplify `h6` using `only [Complex.star_def, Complex.normSq_conj]`.
-/
theorem twoFl_inv {z z' : Fin (2 * r + k + 1) → ℂ} {γ : Mat k r} (h : TwoFl k r z z' γ) : TwoFl k r z' z γ⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h2, h1, h4, h3, isClosedSub_GG.2.2.2.2 _ h5, ?_, by rwa [dr_inv z z' h5]⟩
  unfold Gf at h6 ⊢
  rw [dmin_inv z z' h5, dmin_inv z z' h5, mul_comm (Tz k r z')]
  simpa only [Complex.star_def, Complex.normSq_conj] using h6

/- English proof (translation)
Use `⟨h.1, fun l hl h0 => ?_⟩` and prove the remaining obligations. Rewrite `h0`, the goal using `[dmin_inv z z' hγ]`. Rewrite using `[norm_star]`. Conclude with `h.2 l hl fun h' => h0 (by rw [h', star_zero])`.
-/
theorem deOK_inv {z z' : Fin (2 * r + k + 1) → ℂ} {γ : Mat k r} {De : ℝ} (hγ : γ ∈ GG k r)
    (h : DeOK k r z z' γ De) : DeOK k r z' z γ⁻¹ De := by
  refine ⟨h.1, fun l hl h0 => ?_⟩
  rw [dmin_inv z z' hγ] at h0 ⊢
  rw [norm_star]
  exact h.2 l hl fun h' => h0 (by rw [h', star_zero])

/- English proof (translation)
The claim follows from `continuous_const.matrix_mul (continuous_id (X := Mat k r))`.
-/
theorem continuous_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

/- English proof (translation)
The claim follows from `(continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const`.
-/
theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

/- English proof (translation)
The claim follows from `Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)`.
-/
theorem lmul_inv_lmul {γ : Mat k r} (hγ : γ ∈ GG k r) (x : Mt k r) : lmulM γ⁻¹ (lmulM γ x) = x :=
  Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)

def lmulEquiv {γ : Mat k r} (hγ : γ ∈ GG k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM γ
  invFun := lmulM γ⁻¹
  left_inv := lmul_inv_lmul hγ
  right_inv x := Matrix.mul_nonsing_inv_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)
  measurable_toFun := (continuous_lmul γ).measurable
  measurable_invFun := (continuous_lmul γ⁻¹).measurable

/- English proof (translation)
Introduce `f hf`. Rewrite using `[lintegral_map_equiv]`. Establish `h1` using `h (fun x => f (lmulM γ x)) (hf.comp (continuous_lmul γ).measurable)`. Rewrite `h1` using `[← lintegral_map hf (continuous_lmul γ).measurable, hG.2.2.2 γ hγ]`. Rewrite using `[h1]`.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Establish `hm : Measurable fun s : Mt k r => f (rmulM (Matrix.of (lmulEquiv hγ x)) s)` using `hf.comp (continuous_rmulM _).measurable`. Use `Eq.trans ?_ (lintegral_map hm (continuous_conj γ).measurable).symm` and prove the remaining obligations. Use `lintegral_congr fun s => ?_` and prove the remaining obligations. Use `congr 1`.

Use `show γ * (Matrix.of s * Matrix.of x) = γ * Matrix.of s * γ⁻¹ * (γ * Matrix.of x)`. Rewrite using `[Matrix.mul_assoc _ γ⁻¹, Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ), Matrix.mul_assoc]`.
-/
theorem quot_map {γ : Mat k r} (hγ : γ ∈ GG k r) {μG μR ν : Measure (Mt k r)} (hG : IsHaarOn (GG k r) μG)
    (h : IsQuotMeas μG μR ν) : IsQuotMeas μG (μR.map (conjM γ)) (ν.map (lmulEquiv hγ)) := by
  intro f hf
  rw [lintegral_map_equiv]
  have h1 := h (fun x => f (lmulM γ x)) (hf.comp (continuous_lmul γ).measurable)
  rw [← lintegral_map hf (continuous_lmul γ).measurable, hG.2.2.2 γ hγ] at h1
  rw [h1]
  refine lintegral_congr fun x => ?_
  have hm : Measurable fun s : Mt k r => f (rmulM (Matrix.of (lmulEquiv hγ x)) s) :=
    hf.comp (continuous_rmulM _).measurable
  refine Eq.trans ?_ (lintegral_map hm (continuous_conj γ).measurable).symm
  refine lintegral_congr fun s => ?_
  congr 1
  show γ * (Matrix.of s * Matrix.of x) = γ * Matrix.of s * γ⁻¹ * (γ * Matrix.of x)
  rw [Matrix.mul_assoc _ γ⁻¹, Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ),
    Matrix.mul_assoc]

def Gs (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ GG k r}

def ext0 (f : Mat k r → ℝ) : Mt k r → ℝ := Set.indicator (Gs k r) fun x => f (Matrix.of x)

/- English proof (translation)
The claim follows from `Set.indicator_of_mem (s := Gs k r) hx _`.
-/
theorem cochainExtendByZeroSubgroup_of_mem (f : Mat k r → ℝ) {x : Mt k r} (hx : Matrix.of x ∈ GG k r) : ext0 f x = f (Matrix.of x) :=
  Set.indicator_of_mem (s := Gs k r) hx _

/- English proof (translation)
The claim follows from `Set.indicator_of_notMem (s := Gs k r) hx _`.
-/
theorem amplifierAbsConvExtendByZero_of_not_mem (f : Mat k r → ℝ) {x : Mt k r} (hx : Matrix.of x ∉ GG k r) : ext0 f x = 0 :=
  Set.indicator_of_notMem (s := Gs k r) hx _

/- English proof (translation)
Establish `hc : IsClosed (Gs k r)` using `isClosedSub_GG.2.1`. Establish `h1 : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) (Gs k r)` using `hf`. Use `ContinuousOn.measurable_piecewise (g := fun _ => (0 : ℝ)) h1 continuousOn_const hc.measurableSet` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Conclude with `(Set.piecewise_eq_indicator).symm`.
-/
theorem measurable_amplifierAbsConvExtendByZero {f : Mat k r → ℝ} (hf : ContinuousOn f (GG k r)) : Measurable (ext0 f) := by
  classical
  have hc : IsClosed (Gs k r) := isClosedSub_GG.2.1
  have h1 : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) (Gs k r) := hf
  have := ContinuousOn.measurable_piecewise (g := fun _ => (0 : ℝ)) h1 continuousOn_const hc.measurableSet
  convert this using 1
  exact (Set.piecewise_eq_indicator).symm

def Kc (k r : ℕ) (De : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) *
    4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))

/- English proof (translation)
Establish `p1 : (1 : ℝ) ≤ 2 ^ i` using `one_le_pow₀ one_le_two`. Establish `p2 : (1 : ℝ) ≤ 2 ^ i'` using `one_le_pow₀ one_le_two`. Establish `q1 : (2 : ℝ) ^ i * H₁ ≤ 2 ^ (i + i') * H₁`. Rewrite using `[pow_add]; gcongr; exact le_mul_of_one_le_right (by positivity) p2`. Establish `q2 : (2 : ℝ) ^ i' * H₁ ≤ 2 ^ (i + i') * H₁`.

Rewrite using `[pow_add]; gcongr; exact le_mul_of_one_le_left (by positivity) p1`. Establish `hR : (1 : ℝ) ≤ 2 ^ (i + i') * H₁` using `one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hH`. Establish `key` using `(GlobalTheory.T.amplification_absolute_side_piece_bound k r z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De _ hr hk hκ hs hH h1 h2 h3 h4 h5 h6).2 w hw i' _ y hR hy`. Use `le_trans (lintegral_mono' (Measure.restrict_mono ?_ le_rfl) fun x => ?_) (key.trans (le_of_eq ?_))` and prove the remaining obligations. Introduce and unpack `x ⟨a1, a2, a3, a4, a5⟩`.

Establish `hx : Matrix.of x ∈ GG k r`. Assume the negation of the conclusion as `hx`. Rewrite `a4` using `[amplifierAbsConvExtendByZero_of_not_mem _ hx]`. Conclude with `lt_asymm hy a4`. Establish `hx' : Matrix.of (lmulM γ x) ∈ GG k r` using `isClosedSub_GG.2.2.2.1 _ h3.2.2.2.2.1 _ hx`.

Rewrite `a1`, `a2`, `a4`, `a5` using `[cochainExtendByZeroSubgroup_of_mem _ hx]`. Rewrite `a3` using `[cochainExtendByZeroSubgroup_of_mem _ hx']`. Conclude with `⟨⟨hx, a1.trans q2, a3.trans q1, a4, a5⟩, a2⟩`. Distinguish the cases in `hx : Matrix.of x ∈ GG k r`. Simplify using `only [cochainExtendByZeroSubgroup_of_mem _ hx, le_refl]`.

Simplify using `[amplifierAbsConvExtendByZero_of_not_mem _ hx]`. Use `congr 1`. Unfold `fibVol Kc`. Rewrite using `[mul_pow 2 y, pow_mul (2 : ℝ) 2]`. Evaluate the numerical expressions using `only`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem side {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {z z' : Fin (2 * r + k + 1) → ℂ} {π' : Mat k r → (Wq →L[ℂ] Wq)} {ψ' : Mat k r → ℂ}
    {μG μW' νS' μR νR : Measure (Mt k r)} {Φ' : Mat k r → Wq} {γ : Mat k r} {c κ s H₁ De : ℝ}
    (hr : 1 ≤ r) (hk : 2 * r + 6 ≤ k) (hκ : 0 < κ) (hs : 0 < s) (hH : 1 ≤ H₁)
    (h1 : OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c) (h2 : MomBd z' νS' Φ' (24 * r ^ 3 + 1) H₁)
    (h3 : TwoFl k r z z' γ) (h4 : DeOK k r z z' γ De) (h5 : NormR k r γ s μR) (h6 : IsQuotMeas μG μR νR)
    (w : Wq) (hw : ‖w‖ = 1) (i i' : ℕ) (y : ℝ) (hy : 0 < y) :
    ∫⁻ x in {x | ext0 (Sg k r z') x ≤ 2 ^ i' * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ / 2 < ext0 (Sg k r z') x) ∧
        ext0 (Sg k r z) (lmulM γ x) ≤ 2 ^ i * H₁ ∧ y < ext0 (Yv k r z z' γ) x ∧ ext0 (Yv k r z z' γ) x ≤ 2 * y},
      ENNReal.ofReal (ext0 (fun g => ‖⟪w, Φ' g⟫_ℂ‖) x ^ 2) ∂νR ≤
    ENNReal.ofReal (κ / s * Kc k r De * c * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * (k - 2 - r)) *
      (((2 : ℝ) ^ i') ^ (2 * (24 * r ^ 3 + 1)))⁻¹) := by
  have p1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
  have p2 : (1 : ℝ) ≤ 2 ^ i' := one_le_pow₀ one_le_two
  have q1 : (2 : ℝ) ^ i * H₁ ≤ 2 ^ (i + i') * H₁ := by
    rw [pow_add]; gcongr; exact le_mul_of_one_le_right (by positivity) p2
  have q2 : (2 : ℝ) ^ i' * H₁ ≤ 2 ^ (i + i') * H₁ := by
    rw [pow_add]; gcongr; exact le_mul_of_one_le_left (by positivity) p1
  have hR : (1 : ℝ) ≤ 2 ^ (i + i') * H₁ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hH
  have key := (GlobalTheory.T.amplification_absolute_side_piece_bound k r z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De _ hr hk hκ hs hH h1 h2 h3 h4 h5 h6).2
    w hw i' _ y hR hy
  refine le_trans (lintegral_mono' (Measure.restrict_mono ?_ le_rfl) fun x => ?_) (key.trans (le_of_eq ?_))
  · rintro x ⟨a1, a2, a3, a4, a5⟩
    have hx : Matrix.of x ∈ GG k r := by
      by_contra hx
      rw [amplifierAbsConvExtendByZero_of_not_mem _ hx] at a4
      exact lt_asymm hy a4
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ h3.2.2.2.2.1 _ hx
    rw [cochainExtendByZeroSubgroup_of_mem _ hx] at a1 a2 a4 a5
    rw [cochainExtendByZeroSubgroup_of_mem _ hx'] at a3
    exact ⟨⟨hx, a1.trans q2, a3.trans q1, a4, a5⟩, a2⟩
  · by_cases hx : Matrix.of x ∈ GG k r
    · simp only [cochainExtendByZeroSubgroup_of_mem _ hx, le_refl]
    · simp [amplifierAbsConvExtendByZero_of_not_mem _ hx]
  · congr 1
    unfold fibVol Kc
    rw [mul_pow 2 y, pow_mul (2 : ℝ) 2]
    norm_num only
    ring

/- English proof (translation)
Establish `hM : 1 ≤ max S S'` using `hS.trans (le_max_left _ _)`. Establish `hr' : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `h1 : max S S' ≤ r * max S S' ^ (2 * r - 1)` using `(le_self_pow₀ hM (by omega)).trans (le_mul_of_one_le_left (by positivity) hr')`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hT'.trans h1`.

Conclude with `le_self_pow₀ hDe (by omega)`. Use `_ = _ := (mul_pow _ _ _).symm`.
-/
theorem max_bounds {r : ℕ} {S S' D De Y T : ℝ} (hr : 1 ≤ r) (hS : 1 ≤ S) (hDe : 1 ≤ De)
    (hD : D⁻¹ ≤ De) (hT : 0 ≤ T) (hT' : T ≤ max S S') (hY : Y ≤ T ^ r / D) :
    Y ≤ (r * max S S' ^ (2 * r - 1) * De) ^ r := by
  have hM : 1 ≤ max S S' := hS.trans (le_max_left _ _)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : max S S' ≤ r * max S S' ^ (2 * r - 1) :=
    (le_self_pow₀ hM (by omega)).trans (le_mul_of_one_le_left (by positivity) hr')
  calc Y ≤ T ^ r * De := hY.trans (by rw [div_eq_mul_inv]; gcongr)
    _ ≤ (r * max S S' ^ (2 * r - 1)) ^ r * De ^ r := by
        gcongr
        · exact hT'.trans h1
        · exact le_self_pow₀ hDe (by omega)
    _ = _ := (mul_pow _ _ _).symm

/- English proof (translation)
Introduce `k r Wp _ _ _ Wq _ _ _ z z' π π' ψ ψ' μG μW μW' νS νS' μR νR Φ Φ' γ c κ s H₁ De hr hk hκ hs hH o1 o2 m1 m2 tf de nr qm`. Establish `hγ : γ ∈ GG k r` using `tf.2.2.2.2.1`. Establish `hG : IsHaarOn (GG k r) μG` using `o1.2.2.2.2.2.1`. Establish `hc : 0 < c` using `o1.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `cΦ : ContinuousOn Φ (GG k r)` using `o1.2.2.2.2.2.2.2.2.2.2.2.2.1`.

Establish `cΦ' : ContinuousOn Φ' (GG k r)` using `o2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `tf'` using `twoFl_inv tf`. Establish `de'` using `deOK_inv hγ de`. Establish `nr'` using `(GlobalTheory.T.normalFormRootMeasure_haar_unimodular k r γ s μR hs nr).2.2.2`. Establish `qm'` using `quot_map hγ hG qm`.

Establish `hD0 : Dr k r z z' γ ≠ 0` using `tf.2.2.2.2.2.2`. Establish `hD : 0 < Dr k r z z' γ` using `lt_of_le_of_ne (norm_nonneg _) hD0.symm`. Establish `hDe : (Dr k r z z' γ)⁻¹ ≤ De` using `de.2 ⟨r, by omega⟩ le_rfl (norm_ne_zero_iff.1 hD0)`. Establish `hDe1 : 1 ≤ De` using `de.1`. Establish `n1` using `(GlobalTheory.T.amplification_absolute_side_piece_bound k r z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De _ hr hk hκ hs hH o2 m2 tf de nr qm).1`.

Establish `n2` using `(GlobalTheory.T.amplification_absolute_side_piece_bound k r z' z π ψ μG μW νS _ _ Φ γ⁻¹ c κ s H₁ De _ hr hk hκ hs hH o1 m1 tf' de' nr' qm').1`. Rewrite `n2` using `[MeasurableEquiv.map_apply]`. Establish `a1 : ∀ᵐ x ∂νR, Matrix.of x ∈ GG k r ∧ Yv k r z z' γ (Matrix.of x) ≠ 0` using `by filter_upwards [compl_mem_ae_iff.2 n1] with x hx`. Simplify `hx` using `only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not]`. Establish `a2 : ∀ᵐ x ∂νR, Yv k r z' z γ⁻¹ (γ * Matrix.of x) ≠ 0` using `by filter_upwards [compl_mem_ae_iff.2 n2] with x hx`.

Conclude with `fun h => hx (Or.inr h)`. Establish `n0 : νR {x | Matrix.of x ∉ GG k r} = 0` using `measure_mono_null (fun x hx => Or.inl hx) n1`. Establish `hkk : 1 ≤ k - 2 - r` using `by omega`. Establish `hK : 0 < κ / s * Kc k r De * c`. Establish `: (0 : ℝ) < r` using `by exact_mod_cast hr`.

Establish `: (0 : ℝ) < ((k - 2 - r : ℕ) : ℝ)` using `by exact_mod_cast hkk`. Unfold `Kc`. Check the signs of the components of the expression. Establish `me : Measurable (lmulM γ : Mt k r → Mt k r)` using `(continuous_lmul γ).measurable`. Establish `main` using `GlobalTheory.T.integrable_and_norm_amplitude_le_of_pairings k r νR Φ Φ' γ c (κ / s * Kc k r De * c * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / Dr k r z z' γ) ^ (k - 2 - r)) hγ n0 cΦ cΦ' hc (by positivity) ?_`.

Use `⟨main.1, main.2.trans ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.amplitudeOperatorNorm_finalArithmetic_le k r H₁ De _ hr hk hH hDe1 hD` as an intermediate fact. Use `le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ κ / s))` and prove the remaining obligations. Unfold `Kc`. Clear the denominators using the available nonvanishing facts.

Introduce `v w hv hw`. Establish `mA : Measurable (ext0 fun g => ‖⟪v, Φ g⟫_ℂ‖)` using `measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ).norm`. Establish `mB : Measurable (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖)` using `measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ').norm`. Establish `mS : ∀ z, Measurable (ext0 (Sg k r z))` using `fun z => measurable_amplifierAbsConvExtendByZero (GlobalTheory.T.continuousOn_majorantFlagLengths k r z).2`. Establish `mY : Measurable (ext0 (Yv k r z' z γ⁻¹))` using `(GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable k r z' z γ⁻¹ tf'.2.2.2.2.1).1`.

Establish `mY' : Measurable (ext0 (Yv k r z z' γ))` using `(GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable k r z z' γ hγ).1`. Establish `dy` using `GlobalTheory.T.lintegral_bound_by_dyadic_summation (Mt k r) νR (fun x => ext0 (fun g => ‖⟪v, Φ g⟫_ℂ‖) (lmulM γ x)) (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) (fun x => ext0 (Sg k r z) (lmulM γ x)) (ext0 (Sg k r z')) (fun x => ext0 (Yv k r z' z γ⁻¹) (lmulM γ x)) (ext0 (Yv k r z z' γ)) r (k - 2 …`. Rewrite `dy` using `[Real.sqrt_mul_self hK.le]`. Use `le_trans (le_of_eq (lintegral_congr_ae ?_)) dy` and prove the remaining obligations. Use `filter_upwards [a1] with x hx`.

Establish `hx' : Matrix.of (lmulM γ x) ∈ GG k r` using `isClosedSub_GG.2.2.2.1 _ hγ _ hx.1`. Rewrite using `[cochainExtendByZeroSubgroup_of_mem _ hx.1, cochainExtendByZeroSubgroup_of_mem _ hx']`. Both sides reduce to the same expression. Use `filter_upwards [a1, a2] with x hx hx2`. Establish `hx' : γ * Matrix.of x ∈ GG k r` using `isClosedSub_GG.2.2.2.1 _ hγ _ hx.1`.

Establish `e1 : ∀ f : Mat k r → ℝ, ext0 f (lmulM γ x) = f (γ * Matrix.of x)` using `fun f => cochainExtendByZeroSubgroup_of_mem f hx'`. Simplify using `only [e1, cochainExtendByZeroSubgroup_of_mem _ hx.1]`. Establish `s1 : 1 ≤ Sg k r z (γ * Matrix.of x)` using `((GlobalTheory.T.majorant_flag_lengths_invariance_torus_positivity k r z tf.1).2.2 _).1`. Establish `s2 : 1 ≤ Sg k r z' (Matrix.of x)` using `((GlobalTheory.T.majorant_flag_lengths_invariance_torus_positivity k r z' tf.2.1).2.2 _).1`. Take `⟨b1, b2, b3⟩` from `GlobalTheory.T.top_minor_and_gram_number_le_majorant_lengths k r z z' γ tf _ hx.1`.

Take `⟨-, b5, b6⟩` from `GlobalTheory.T.top_minor_and_gram_number_le_majorant_lengths k r z' z γ⁻¹ tf' _ hx'`. Rewrite `b6` using `[Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ), dr_inv z z' hγ]`. Use `⟨norm_nonneg _, norm_nonneg _, s1, s2, lt_of_le_of_ne b5 hx2.symm, lt_of_le_of_ne b2 hx.2.symm, ?_, ?_, max_bounds hr s1 hDe1 hDe (zero_le_one.trans s2) (le_max_right _ _) b6, max_bounds hr s1 hDe1 hDe (zero_le_one.trans s1) (le_max_left _ _) b3⟩` and prove the remaining obligations. Rewrite using `[mul_comm (Yv k r z' z γ⁻¹ _)]`. Conclude with `GlobalTheory.T.twoFlagsGramNumber_mul_topMinorNorm_le_two_pow k r z z' γ tf _ hx.1`.

Use `b1.trans ?_` and prove the remaining obligations. Rewrite using `[show ∀ t : ℝ, t ^ (2 * r) = t ^ r * t ^ r from fun t => by ring]`. Conclude with `mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans s2) (le_max_right _ _) _) (pow_le_pow_left₀ (zero_le_one.trans s1) (le_max_left _ _) _) (pow_nonneg (zero_le_one.trans s1) _) (pow_nonneg ((zero_le_one.trans s1).trans (le_max_left _ _)) _)`. Introduce `i i' y hy`. Establish `h` using `side hr hk hκ hs hH o1 m1 tf' de' nr' qm' v hv i' i y hy`.

Rewrite `h` using `[MeasurableEquiv.restrict_map, lintegral_map_equiv, add_comm i' i]`. Use `le_trans (le_of_eq ?_) h` and prove the remaining obligations. Use `congr 2`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`.

Rewrite using `[show lmulEquiv hγ x = lmulM γ x from rfl, lmul_inv_lmul hγ]`.
-/
theorem abs_core : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (z z' : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → MomBd z νS Φ (24 * r ^ 3 + 1) H₁ → MomBd z' νS' Φ' (24 * r ^ 3 + 1) H₁ → TwoFl k r z z' γ → DeOK k r z z' γ De → NormR k r γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * absBd k r H₁ De (Dr k r z z' γ) := by
  intro k r Wp _ _ _ Wq _ _ _ z z' π π' ψ ψ' μG μW μW' νS νS' μR νR Φ Φ' γ c κ s H₁ De hr hk hκ hs hH o1 o2 m1 m2
    tf de nr qm
  have hγ : γ ∈ GG k r := tf.2.2.2.2.1
  have hG : IsHaarOn (GG k r) μG := o1.2.2.2.2.2.1
  have hc : 0 < c := o1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ : ContinuousOn Φ (GG k r) := o1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ' : ContinuousOn Φ' (GG k r) := o2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have tf' := twoFl_inv tf
  have de' := deOK_inv hγ de
  have nr' := (GlobalTheory.T.normalFormRootMeasure_haar_unimodular k r γ s μR hs nr).2.2.2
  have qm' := quot_map hγ hG qm
  have hD0 : Dr k r z z' γ ≠ 0 := tf.2.2.2.2.2.2
  have hD : 0 < Dr k r z z' γ := lt_of_le_of_ne (norm_nonneg _) hD0.symm
  have hDe : (Dr k r z z' γ)⁻¹ ≤ De := de.2 ⟨r, by omega⟩ le_rfl (norm_ne_zero_iff.1 hD0)
  have hDe1 : 1 ≤ De := de.1
  have n1 := (GlobalTheory.T.amplification_absolute_side_piece_bound k r z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De _ hr hk hκ hs hH o2 m2 tf de nr qm).1
  have n2 := (GlobalTheory.T.amplification_absolute_side_piece_bound k r z' z π ψ μG μW νS _ _ Φ γ⁻¹ c κ s H₁ De _ hr hk hκ hs hH o1 m1 tf' de' nr' qm').1
  rw [MeasurableEquiv.map_apply] at n2
  have a1 : ∀ᵐ x ∂νR, Matrix.of x ∈ GG k r ∧ Yv k r z z' γ (Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n1] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] using hx
  have a2 : ∀ᵐ x ∂νR, Yv k r z' z γ⁻¹ (γ * Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n2] with x hx
    exact fun h => hx (Or.inr h)
  have n0 : νR {x | Matrix.of x ∉ GG k r} = 0 := measure_mono_null (fun x hx => Or.inl hx) n1
  have hkk : 1 ≤ k - 2 - r := by omega
  have hK : 0 < κ / s * Kc k r De * c := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    have : (0 : ℝ) < ((k - 2 - r : ℕ) : ℝ) := by exact_mod_cast hkk
    unfold Kc
    positivity
  have me : Measurable (lmulM γ : Mt k r → Mt k r) := (continuous_lmul γ).measurable
  have main := GlobalTheory.T.integrable_and_norm_amplitude_le_of_pairings k r νR Φ Φ' γ c (κ / s * Kc k r De * c * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) *
    De ^ (2 * r) * (2 ^ r / Dr k r z z' γ) ^ (k - 2 - r)) hγ n0 cΦ cΦ' hc (by positivity) ?_
  · refine ⟨main.1, main.2.trans ?_⟩
    have := GlobalTheory.T.amplitudeOperatorNorm_finalArithmetic_le k r H₁ De _ hr hk hH hDe1 hD
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ κ / s))
    unfold Kc
    field_simp
  intro v w hv hw
  have mA : Measurable (ext0 fun g => ‖⟪v, Φ g⟫_ℂ‖) := measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ).norm
  have mB : Measurable (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) := measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ').norm
  have mS : ∀ z, Measurable (ext0 (Sg k r z)) := fun z => measurable_amplifierAbsConvExtendByZero (GlobalTheory.T.continuousOn_majorantFlagLengths k r z).2
  have mY : Measurable (ext0 (Yv k r z' z γ⁻¹)) := (GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable k r z' z γ⁻¹ tf'.2.2.2.2.1).1
  have mY' : Measurable (ext0 (Yv k r z z' γ)) := (GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable k r z z' γ hγ).1
  have dy := GlobalTheory.T.lintegral_bound_by_dyadic_summation (Mt k r) νR (fun x => ext0 (fun g => ‖⟪v, Φ g⟫_ℂ‖) (lmulM γ x))
    (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) (fun x => ext0 (Sg k r z) (lmulM γ x)) (ext0 (Sg k r z'))
    (fun x => ext0 (Yv k r z' z γ⁻¹) (lmulM γ x)) (ext0 (Yv k r z z' γ)) r (k - 2 - r) H₁ De (Dr k r z z' γ) _ _
    (mA.comp me) mB ((mS z).comp me) (mS z') (mY.comp me) mY' hr hkk hH hDe1 hD hK hK ?_ ?_
    (fun i i' y hy => side hr hk hκ hs hH o2 m2 tf de nr qm w hw i i' y hy)
  · rw [Real.sqrt_mul_self hK.le] at dy
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) dy
    filter_upwards [a1] with x hx
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    rw [cochainExtendByZeroSubgroup_of_mem _ hx.1, cochainExtendByZeroSubgroup_of_mem _ hx']
    rfl
  · filter_upwards [a1, a2] with x hx hx2
    have hx' : γ * Matrix.of x ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    have e1 : ∀ f : Mat k r → ℝ, ext0 f (lmulM γ x) = f (γ * Matrix.of x) := fun f => cochainExtendByZeroSubgroup_of_mem f hx'
    simp only [e1, cochainExtendByZeroSubgroup_of_mem _ hx.1]
    have s1 : 1 ≤ Sg k r z (γ * Matrix.of x) := ((GlobalTheory.T.majorant_flag_lengths_invariance_torus_positivity k r z tf.1).2.2 _).1
    have s2 : 1 ≤ Sg k r z' (Matrix.of x) := ((GlobalTheory.T.majorant_flag_lengths_invariance_torus_positivity k r z' tf.2.1).2.2 _).1
    obtain ⟨b1, b2, b3⟩ := GlobalTheory.T.top_minor_and_gram_number_le_majorant_lengths k r z z' γ tf _ hx.1
    obtain ⟨-, b5, b6⟩ := GlobalTheory.T.top_minor_and_gram_number_le_majorant_lengths k r z' z γ⁻¹ tf' _ hx'
    rw [Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ), dr_inv z z' hγ] at b6
    refine ⟨norm_nonneg _, norm_nonneg _, s1, s2, lt_of_le_of_ne b5 hx2.symm, lt_of_le_of_ne b2 hx.2.symm, ?_, ?_,
      max_bounds hr s1 hDe1 hDe (zero_le_one.trans s2) (le_max_right _ _) b6,
      max_bounds hr s1 hDe1 hDe (zero_le_one.trans s1) (le_max_left _ _) b3⟩
    · rw [mul_comm (Yv k r z' z γ⁻¹ _)]
      exact GlobalTheory.T.twoFlagsGramNumber_mul_topMinorNorm_le_two_pow k r z z' γ tf _ hx.1
    · refine b1.trans ?_
      rw [show ∀ t : ℝ, t ^ (2 * r) = t ^ r * t ^ r from fun t => by ring]
      exact mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans s2) (le_max_right _ _) _)
        (pow_le_pow_left₀ (zero_le_one.trans s1) (le_max_left _ _) _) (pow_nonneg (zero_le_one.trans s1) _)
        (pow_nonneg ((zero_le_one.trans s1).trans (le_max_left _ _)) _)
  · intro i i' y hy
    have h := side hr hk hκ hs hH o1 m1 tf' de' nr' qm' v hv i' i y hy
    rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, add_comm i' i] at h
    refine le_trans (le_of_eq ?_) h
    congr 2
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [show lmulEquiv hγ x = lmulM γ x from rfl, lmul_inv_lmul hγ]

end GlobalTheory.Amp.AbsConv
