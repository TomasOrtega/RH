import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularGroup ModularForm Complex
open scoped Real Modular MatrixGroups

namespace EtaPeriodLatticeClass

/- English proof (translation)
Establish `h` using `congr_fun (SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant γ) τ`. Rewrite `h` using `[SL_slash_apply]`. Establish `hd : denom γ τ ≠ 0` using `denom_ne_zero γ τ`. Rewrite using `[← h, mul_comm (ModularForm.discriminant (γ • τ)), ← mul_assoc, ← zpow_add₀ hd]`. Simplify using the standard rewrite rules.
-/
theorem discriminant_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (γ • τ) = denom γ τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
  have h := congr_fun
    (SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant γ) τ
  rw [SL_slash_apply] at h
  have hd : denom γ τ ≠ 0 := denom_ne_zero γ τ
  rw [← h, mul_comm (ModularForm.discriminant (γ • τ)), ← mul_assoc, ← zpow_add₀ hd]
  simp

/- English proof (translation)
Establish `h` using `congr_arg norm (discriminant_smul γ τ)`. Simplify using `only [ModularForm.discriminant, norm_mul, norm_pow, norm_zpow] at h`. Establish `h6 : (‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4) ^ 6 = (‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6`. Rewrite using `[← pow_mul, mul_pow, ← pow_mul, ← pow_mul]`. Rewrite using `[show (4 : ℕ) * 6 = 24 from rfl, show (2 : ℕ) * 6 = 12 from rfl, h]`.

Use `norm_cast`. Conclude with `(pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h6`.
-/
theorem norm_eta_smul_pow_four (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4 = ‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4 := by
  have h := congr_arg norm (discriminant_smul γ τ)
  simp only [ModularForm.discriminant, norm_mul, norm_pow, norm_zpow] at h
  have h6 : (‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4) ^ 6 = (‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul]
    rw [show (4 : ℕ) * 6 = 24 from rfl, show (2 : ℕ) * 6 = 12 from rfl, h]
    norm_cast
  exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h6

/- English proof (translation)
Unfold `etaPeriod`. Rewrite using `[norm_eta_smul_pow_four, ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]`. Establish `: ‖denom γ τ‖ ≠ 0` using `norm_ne_zero_iff.mpr (denom_ne_zero γ τ)`. Clear the denominators using the available nonvanishing facts.
-/
theorem etaPeriod_smul (γ : SL(2, ℤ)) (τ : ℍ) : etaPeriod (γ • τ) = etaPeriod τ := by
  unfold etaPeriod
  rw [norm_eta_smul_pow_four, ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  have : ‖denom γ τ‖ ≠ 0 := norm_ne_zero_iff.mpr (denom_ne_zero γ τ)
  field_simp

/- English proof (translation)
Unfold `latticeOf`. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_pair]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨m, n, by simp [zsmul_eq_mul]⟩`.

Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨m, n, by simp [zsmul_eq_mul]⟩`.
-/
theorem mem_latticeOf {τ z : ℂ} : z ∈ latticeOf τ ↔ ∃ m n : ℤ, z = m + n * τ := by
  unfold latticeOf
  rw [SetLike.mem_coe, Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [zsmul_eq_mul]⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [zsmul_eq_mul]⟩

/- English proof (translation)
Establish `him` using `congr_arg Complex.im h`. Establish `hre` using `congr_arg Complex.re h`. Simplify using `at him hre`. Establish `hn : n = n'`. Break down `him with h | h` into its components or cases.

Conclude with `h` after adjusting the coercions. Conclude with `absurd h τ.im_pos.ne'`. Substitute `hn` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Conclude with `(by linarith : (m : ℝ) = m')` after adjusting the coercions.
-/
theorem coord_unique {τ : ℍ} {m n m' n' : ℤ}
    (h : (m : ℂ) + n * (τ : ℂ) = m' + n' * (τ : ℂ)) : m = m' ∧ n = n' := by
  have him := congr_arg Complex.im h
  have hre := congr_arg Complex.re h
  simp at him hre
  have hn : n = n' := by
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h τ.im_pos.ne'
  subst hn
  refine ⟨?_, rfl⟩
  exact_mod_cast (by linarith : (m : ℝ) = m')

/- English proof (translation)
Take `⟨d, c, hdc⟩` from `mem_latticeOf.mp (h2 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))`. Take `⟨b, a, hba⟩` from `mem_latticeOf.mp (h2 τ' (mem_latticeOf.mpr ⟨0, 1, by simp⟩))`. Take `⟨h, g, hhg⟩` from `mem_latticeOf.mp (h1 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))`. Take `⟨f, e, hfe⟩` from `mem_latticeOf.mp (h1 τ (mem_latticeOf.mpr ⟨0, 1, by simp⟩))`. Rewrite `hdc`, `hhg` using `[mul_one]`.

Establish `k1 : ((d * h + c * f : ℤ) : ℂ) + ((d * g + c * e : ℤ) : ℂ) * (τ' : ℂ) = ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ' : ℂ)`. Establish `hinv : μ * μ⁻¹ = 1` using `mul_inv_cancel₀ hμ`. Use `push_cast`. Take the linear combination `hinv - μ * hdc - (d : ℂ) * hhg - (c : ℂ) * hfe`. Establish `k2 : ((b * h + a * f : ℤ) : ℂ) + ((b * g + a * e : ℤ) : ℂ) * (τ' : ℂ) = ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ' : ℂ)`.

Establish `hinv : μ * μ⁻¹ = 1` using `mul_inv_cancel₀ hμ`. Use `push_cast`. Take the linear combination `(τ' : ℂ) * hinv - μ * hba - (b : ℂ) * hhg - (a : ℂ) * hfe`. Take `⟨E4, E3⟩` from `coord_unique k1`. Take `⟨E2, E1⟩` from `coord_unique k2`.

Establish `hdet1 : (a * d - b * c) * (e * h - f * g) = 1`. Take the linear combination `(c * f + d * h) * E1 + E4 - (c * e + d * g) * E2`. Establish `hw : (c : ℂ) * τ + d ≠ 0`. Rewrite using `[add_comm, ← hdc]`. Conclude with `inv_ne_zero hμ`.

Establish `hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / ((c : ℂ) * τ + d)`. Rewrite using `[eq_div_iff hw, add_comm ((c : ℂ) * τ), ← hdc, add_comm ((a : ℂ) * τ), ← hba]`. Clear the denominators using the available nonvanishing facts. Establish `hdetpos : 0 < a * d - b * c`. Establish `him` using `congr_arg Complex.im hτ'`.

Rewrite `him` using `[Complex.div_im]`. Establish `hN : 0 < Complex.normSq ((c : ℂ) * τ + d)` using `Complex.normSq_pos.mpr hw`. Establish `key : (τ' : ℂ).im * Complex.normSq ((c : ℂ) * τ + d) = ((a * d - b * c : ℤ) : ℝ) * τ.im`. Rewrite using `[him, sub_mul, div_mul_cancel₀ _ hN.ne', div_mul_cancel₀ _ hN.ne']`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish `: (0 : ℝ) < ((a * d - b * c : ℤ) : ℝ) * τ.im`. Rewrite using `[← key]`. Conclude with `mul_pos τ'.im_pos hN`. Use `(pos_of_mul_pos_left this τ.im_pos.le)` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Establish `hdet : a * d - b * c = 1` using `Int.eq_one_of_mul_eq_one_right hdetpos.le hdet1`. Set `γ : SL(2, ℤ)` to `⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet⟩`. Use `⟨γ, UpperHalfPlane.ext ?_⟩` and prove the remaining obligations. Rewrite using `[coe_specialLinearGroup_apply, hτ']`.

Simplify using `[γ]`.
-/
theorem exists_SL_smul_eq {τ τ' : ℍ} {μ : ℂ} (hμ : μ ≠ 0)
    (h1 : ∀ z ∈ latticeOf (τ : ℂ), μ * z ∈ latticeOf (τ' : ℂ))
    (h2 : ∀ w ∈ latticeOf (τ' : ℂ), μ⁻¹ * w ∈ latticeOf (τ : ℂ)) :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by

  obtain ⟨d, c, hdc⟩ := mem_latticeOf.mp (h2 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))
  obtain ⟨b, a, hba⟩ := mem_latticeOf.mp (h2 τ' (mem_latticeOf.mpr ⟨0, 1, by simp⟩))

  obtain ⟨h, g, hhg⟩ := mem_latticeOf.mp (h1 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))
  obtain ⟨f, e, hfe⟩ := mem_latticeOf.mp (h1 τ (mem_latticeOf.mpr ⟨0, 1, by simp⟩))
  rw [mul_one] at hdc hhg

  have k1 : ((d * h + c * f : ℤ) : ℂ) + ((d * g + c * e : ℤ) : ℂ) * (τ' : ℂ) =
      ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ' : ℂ) := by
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    push_cast
    linear_combination hinv - μ * hdc - (d : ℂ) * hhg - (c : ℂ) * hfe
  have k2 : ((b * h + a * f : ℤ) : ℂ) + ((b * g + a * e : ℤ) : ℂ) * (τ' : ℂ) =
      ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ' : ℂ) := by
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    push_cast
    linear_combination (τ' : ℂ) * hinv - μ * hba - (b : ℂ) * hhg - (a : ℂ) * hfe
  obtain ⟨E4, E3⟩ := coord_unique k1
  obtain ⟨E2, E1⟩ := coord_unique k2
  have hdet1 : (a * d - b * c) * (e * h - f * g) = 1 := by
    linear_combination (c * f + d * h) * E1 + E4 - (c * e + d * g) * E2

  have hw : (c : ℂ) * τ + d ≠ 0 := by
    rw [add_comm, ← hdc]; exact inv_ne_zero hμ
  have hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / ((c : ℂ) * τ + d) := by
    rw [eq_div_iff hw, add_comm ((c : ℂ) * τ), ← hdc, add_comm ((a : ℂ) * τ), ← hba]
    field_simp

  have hdetpos : 0 < a * d - b * c := by
    have him := congr_arg Complex.im hτ'
    rw [Complex.div_im] at him
    have hN : 0 < Complex.normSq ((c : ℂ) * τ + d) := Complex.normSq_pos.mpr hw
    have key : (τ' : ℂ).im * Complex.normSq ((c : ℂ) * τ + d) = ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      rw [him, sub_mul, div_mul_cancel₀ _ hN.ne', div_mul_cancel₀ _ hN.ne']
      simp
      ring
    have : (0 : ℝ) < ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      rw [← key]; exact mul_pos τ'.im_pos hN
    have := (pos_of_mul_pos_left this τ.im_pos.le)
    exact_mod_cast this
  have hdet : a * d - b * c = 1 :=
    Int.eq_one_of_mul_eq_one_right hdetpos.le hdet1
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine ⟨γ, UpperHalfPlane.ext ?_⟩
  rw [coe_specialLinearGroup_apply, hτ']
  simp [γ]

/- English proof (translation)
Introduce and unpack `Λ τ τ' ⟨c, hc, hΛ⟩ ⟨c', hc', hΛ'⟩`. Establish `h1 : ∀ z ∈ latticeOf (τ : ℂ), c' / c * z ∈ latticeOf (τ' : ℂ)`. Introduce `z hz`. Rewrite `hz` using `[← hΛ]`. Take `⟨x, hx, rfl⟩` from `hz`.

Rewrite using `[← hΛ']`. Conclude with `⟨x, hx, by field_simp⟩`. Establish `h2 : ∀ w ∈ latticeOf (τ' : ℂ), (c' / c)⁻¹ * w ∈ latticeOf (τ : ℂ)`. Introduce `w hw`. Rewrite `hw` using `[← hΛ']`.

Take `⟨x, hx, rfl⟩` from `hw`. Rewrite using `[← hΛ]`. Conclude with `⟨x, hx, by field_simp⟩`. Take `⟨γ, hγ⟩` from `exists_SL_smul_eq (div_ne_zero hc' hc) h1 h2`. Rewrite using `[← hγ, hinv]`.
-/
theorem of_EtaPeriodModularInvariant (hinv : EtaPeriodModularInvariant.Statement) :
    EtaPeriodLatticeClass.Statement := by
  rintro Λ τ τ' ⟨c, hc, hΛ⟩ ⟨c', hc', hΛ'⟩
  have h1 : ∀ z ∈ latticeOf (τ : ℂ), c' / c * z ∈ latticeOf (τ' : ℂ) := by
    intro z hz
    rw [← hΛ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [← hΛ']
    exact ⟨x, hx, by field_simp⟩
  have h2 : ∀ w ∈ latticeOf (τ' : ℂ), (c' / c)⁻¹ * w ∈ latticeOf (τ : ℂ) := by
    intro w hw
    rw [← hΛ'] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [← hΛ]
    exact ⟨x, hx, by field_simp⟩
  obtain ⟨γ, hγ⟩ := exists_SL_smul_eq (div_ne_zero hc' hc) h1 h2
  rw [← hγ, hinv]

/- English proof (translation)
The claim follows from `of_EtaPeriodModularInvariant etaPeriod_smul`.
-/
theorem proof : EtaPeriodLatticeClass.Statement :=
  of_EtaPeriodModularInvariant etaPeriod_smul

end EtaPeriodLatticeClass

/- English proof (translation)
The claim follows from `EtaPeriodLatticeClass.etaPeriod_smul _ _`.
-/
example : etaPeriod (ModularGroup.T • UpperHalfPlane.I) = etaPeriod UpperHalfPlane.I :=
  EtaPeriodLatticeClass.etaPeriod_smul _ _

end GroundTheory.Heights₂.Theta
