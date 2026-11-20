import Mathlib
import Formalism.PeriodIntegrals.DiscrNe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NonzeroDiscriminants.DiscLat

open ModularForm EisensteinSeries UpperHalfPlane

noncomputable section

namespace DiscrNeWork

/- English proof (translation)
Establish `h5 : bernoulli' 5 = 0`. Rewrite using `[bernoulli'_def]`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four]`. Evaluate the numerical expressions using `[Nat.choose]`. Rewrite using `[bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]`.

Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, h5]`. Evaluate the numerical expressions using `[Nat.choose]`.
-/
theorem bern6 : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four]
    norm_num [Nat.choose]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, h5]
  norm_num [Nat.choose]

/- English proof (translation)
Establish `h` using `riemannZeta_two_mul_nat (show (3 : ℕ) ≠ 0 by norm_num)`. Rewrite using `[show (6 : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, h, bern6]`. Evaluate the numerical expressions using `[Nat.factorial]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zeta6 : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (show (3 : ℕ) ≠ 0 by norm_num)
  rw [show (6 : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, h, bern6]
  norm_num [Nat.factorial]
  ring

/- English proof (translation)
Rewrite using `[AddSubgroup.mem_closure_pair]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Use `⟨![n, m], ?_⟩` and prove the remaining obligations. Simplify using `[zsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨v, rfl⟩`. Conclude with `⟨v 1, v 0, by simp [zsmul_eq_mul]; ring⟩`.
-/
private lemma mem_closure_pair_iff_exists_int (a z w : ℂ) :
    w ∈ AddSubgroup.closure ({a, a * z} : Set ℂ) ↔ ∃ v : Fin 2 → ℤ, w = a * ((v 0 : ℂ) * z + v 1) := by
  rw [AddSubgroup.mem_closure_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨![n, m], ?_⟩
    simp [zsmul_eq_mul]
    ring
  · rintro ⟨v, rfl⟩
    exact ⟨v 1, v 0, by simp [zsmul_eq_mul]; ring⟩

/- English proof (translation)
Introduce `v w h`. Establish `him` using `congrArg Complex.im h`. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero] at him`. Establish `h0r : ((v 0 : ℤ) : ℝ) = ((w 0 : ℤ) : ℝ)` using `mul_right_cancel₀ hz.ne' him`. Establish `h0 : v 0 = w 0` using `by exact_mod_cast h0r`.

Establish `hre` using `congrArg Complex.re h`. Simplify using `only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero] at hre`. Rewrite `hre` using `[h0r]`. Establish `h1 : v 1 = w 1`. Establish `h2 : ((v 1 : ℤ) : ℝ) = ((w 1 : ℤ) : ℝ)` using `by linarith`.

Conclude with `h2` after adjusting the coercions. Use extensionality with `i`. Use `fin_cases i`. Conclude with `h0`. Conclude with `h1`.
-/
private lemma injective_int_pair_mul_add_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    Function.Injective (fun v : Fin 2 → ℤ => (v 0 : ℂ) * z + v 1) := by
  intro v w h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero] at him
  have h0r : ((v 0 : ℤ) : ℝ) = ((w 0 : ℤ) : ℝ) := mul_right_cancel₀ hz.ne' him
  have h0 : v 0 = w 0 := by exact_mod_cast h0r
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
    sub_zero] at hre
  rw [h0r] at hre
  have h1 : v 1 = w 1 := by
    have h2 : ((v 1 : ℤ) : ℝ) = ((w 1 : ℤ) : ℝ) := by linarith
    exact_mod_cast h2
  ext i
  fin_cases i
  · exact h0
  · exact h1

/- English proof (translation)
Unfold `PI.eisG PI.lat2`. Establish `hinj` using `injective_int_pair_mul_add_of_im_pos z hz`. Set `f : {v : Fin 2 → ℤ // v ≠ 0} → {w : ℂ // w ∈ AddSubgroup.closure ({a, a * z} : Set ℂ) ∧ w ≠ 0}` to `fun v => ⟨a * ((v.1 0 : ℂ) * z + v.1 1), (mem_closure_pair_iff_exists_int a z _).mpr ⟨v.1, rfl⟩, mul_ne_zero ha (fun h => v.2 (hinj (by simpa using h)))⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion.

Introduce `v w h`. Establish `h1` using `congrArg Subtype.val h`. Conclude with `Subtype.ext (hinj (mul_left_cancel₀ ha h1))`. Introduce and unpack `⟨w, hw, hw0⟩`. Take `⟨v, rfl⟩` from `(mem_closure_pair_iff_exists_int a z w).mp hw`.

Use `⟨⟨v, fun hv => hw0 (by simp [hv])⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← (Equiv.ofBijective f hf).tsum_eq]`. Establish `hsupp : Function.support (fun v : Fin 2 → ℤ => EisensteinSeries.eisSummand ((2 * k : ℕ) : ℤ) v (⟨z, hz⟩ : UpperHalfPlane)) ⊆ {v | v ≠ 0}`. Introduce `v hv`. Assume the negation of the conclusion as `hv0`.

Simplify using `only [Set.mem_setOf_eq, not_not] at hv0`. Apply `hv` to reduce the goal to its premises. Substitute `hv0` using the available equality. Simplify using `[EisensteinSeries.eisSummand]`. Conclude with `zero_zpow _ (by omega)`.

Rewrite using `[← tsum_subtype_eq_of_support_subset hsupp, ← tsum_mul_left]`. Use `tsum_congr fun v => ?_` and prove the remaining obligations. Simplify using `only [Equiv.ofBijective_apply, f, EisensteinSeries.eisSummand, UpperHalfPlane.coe_mk, zpow_natCast]`. Rewrite using `[mul_pow, one_div, mul_inv, zpow_neg, zpow_natCast]`.
-/
private lemma eisG_lat2_eq_inv_pow_mul_tsum (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) (k : ℕ) (hk : k ≠ 0) :
    PI.eisG (PI.lat2 a (a * z)) k =
      (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ,
        EisensteinSeries.eisSummand ((2 * k : ℕ) : ℤ) v (⟨z, hz⟩ : UpperHalfPlane) := by
  unfold PI.eisG PI.lat2
  have hinj := injective_int_pair_mul_add_of_im_pos z hz
  let f : {v : Fin 2 → ℤ // v ≠ 0} → {w : ℂ // w ∈ AddSubgroup.closure ({a, a * z} : Set ℂ) ∧ w ≠ 0} :=
    fun v => ⟨a * ((v.1 0 : ℂ) * z + v.1 1), (mem_closure_pair_iff_exists_int a z _).mpr ⟨v.1, rfl⟩,
      mul_ne_zero ha (fun h => v.2 (hinj (by simpa using h)))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      have h1 := congrArg Subtype.val h
      exact Subtype.ext (hinj (mul_left_cancel₀ ha h1))
    · rintro ⟨w, hw, hw0⟩
      obtain ⟨v, rfl⟩ := (mem_closure_pair_iff_exists_int a z w).mp hw
      refine ⟨⟨v, fun hv => hw0 (by simp [hv])⟩, rfl⟩
  rw [← (Equiv.ofBijective f hf).tsum_eq]
  have hsupp : Function.support (fun v : Fin 2 → ℤ =>
      EisensteinSeries.eisSummand ((2 * k : ℕ) : ℤ) v (⟨z, hz⟩ : UpperHalfPlane)) ⊆ {v | v ≠ 0} := by
    intro v hv
    by_contra hv0
    simp only [Set.mem_setOf_eq, not_not] at hv0
    apply hv
    subst hv0
    simp [EisensteinSeries.eisSummand]
    exact zero_zpow _ (by omega)
  rw [← tsum_subtype_eq_of_support_subset hsupp, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  simp only [Equiv.ofBijective_apply, f, EisensteinSeries.eisSummand, UpperHalfPlane.coe_mk, zpow_natCast]
  rw [mul_pow, one_div, mul_inv, zpow_neg, zpow_natCast]

/- English proof (translation)
Rewrite using `[eisG_lat2_eq_inv_pow_mul_tsum a τ ha τ.2 2 (by norm_num)]`. Establish `h2` using `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 4) (by norm_num) τ`. Establish `hE : E₄ τ = 1 / 2 * _root_.eisensteinSeries (N` using `1) 0 (4 : ℕ) τ := rfl`. Rewrite using `[show ((2 * 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num, show (⟨(τ : ℂ), τ.2⟩ : UpperHalfPlane) = τ from rfl, h2, hE, show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four, show a ^ (2 * 2) = a ^ 4 by norm_num]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eisenstein_four_lattice_eq (a : ℂ) (ha : a ≠ 0) (τ : ℍ) :
    PI.eisG (PI.lat2 a (a * τ)) 2 = (a ^ 4)⁻¹ * ((Real.pi : ℂ) ^ 4 / 90 * (2 * E₄ τ)) := by
  rw [eisG_lat2_eq_inv_pow_mul_tsum a τ ha τ.2 2 (by norm_num)]
  have h2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 4) (by norm_num) τ
  have hE : E₄ τ = 1 / 2 * _root_.eisensteinSeries (N := 1) 0 (4 : ℕ) τ := rfl
  rw [show ((2 * 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num, show (⟨(τ : ℂ), τ.2⟩ : UpperHalfPlane) = τ from rfl,
    h2, hE, show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four, show a ^ (2 * 2) = a ^ 4 by norm_num]
  ring

/- English proof (translation)
Rewrite using `[eisG_lat2_eq_inv_pow_mul_tsum a τ ha τ.2 3 (by norm_num)]`. Establish `h2` using `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 6) (by norm_num) τ`. Establish `hE : E₆ τ = 1 / 2 * _root_.eisensteinSeries (N` using `1) 0 (6 : ℕ) τ := rfl`. Rewrite using `[show ((2 * 3 : ℕ) : ℤ) = ((6 : ℕ) : ℤ) by norm_num, show (⟨(τ : ℂ), τ.2⟩ : UpperHalfPlane) = τ from rfl, h2, hE, show ((6 : ℕ) : ℂ) = 6 by norm_num, zeta6, show a ^ (2 * 3) = a ^ 6 by norm_num]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eisenstein_six_lattice_eq (a : ℂ) (ha : a ≠ 0) (τ : ℍ) :
    PI.eisG (PI.lat2 a (a * τ)) 3 = (a ^ 6)⁻¹ * ((Real.pi : ℂ) ^ 6 / 945 * (2 * E₆ τ)) := by
  rw [eisG_lat2_eq_inv_pow_mul_tsum a τ ha τ.2 3 (by norm_num)]
  have h2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 6) (by norm_num) τ
  have hE : E₆ τ = 1 / 2 * _root_.eisensteinSeries (N := 1) 0 (6 : ℕ) τ := rfl
  rw [show ((2 * 3 : ℕ) : ℤ) = ((6 : ℕ) : ℤ) by norm_num, show (⟨(τ : ℂ), τ.2⟩ : UpperHalfPlane) = τ from rfl,
    h2, hE, show ((6 : ℕ) : ℂ) = 6 by norm_num, zeta6, show a ^ (2 * 3) = a ^ 6 by norm_num]
  ring

/- English proof (translation)
Establish `hΔ` using `ModularForm.discriminant_ne_zero τ`. Rewrite `hΔ` using `[discriminant_eq_E₄_cube_sub_E₆_sq]`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `key : PI.discr (PI.lat2 a (a * τ)) = (a ^ 12)⁻¹ * (64 / 27 * (Real.pi : ℂ) ^ 12) * (E₄ τ ^ 3 - E₆ τ ^ 2)`. Rewrite using `[PI.discr, PI.g2, PI.g3, eisenstein_four_lattice_eq a ha τ, eisenstein_six_lattice_eq a ha τ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Establish `h1 : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0`. Introduce `h`. Apply `hΔ` to reduce the goal to its premises.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Conclude with `mul_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ ha)) (mul_ne_zero (by norm_num) (pow_ne_zero _ hpi))) h1`.
-/
theorem discr_scaled (a : ℂ) (ha : a ≠ 0) (τ : ℍ) : PI.discr (PI.lat2 a (a * τ)) ≠ 0 := by
  have hΔ := ModularForm.discriminant_ne_zero τ
  rw [discriminant_eq_E₄_cube_sub_E₆_sq] at hΔ
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : PI.discr (PI.lat2 a (a * τ)) =
      (a ^ 12)⁻¹ * (64 / 27 * (Real.pi : ℂ) ^ 12) * (E₄ τ ^ 3 - E₆ τ ^ 2) := by
    rw [PI.discr, PI.g2, PI.g3, eisenstein_four_lattice_eq a ha τ, eisenstein_six_lattice_eq a ha τ]
    ring
  rw [key]
  have h1 : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := by
    intro h; apply hΔ; rw [h]; simp
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ ha))
    (mul_ne_zero (by norm_num) (pow_ne_zero _ hpi))) h1

/- English proof (translation)
Establish `hw : w₁ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Establish `hτ : 0 < (w₂ / w₁).im`. Establish `e : (w₂ / w₁).im = ((starRingEnd ℂ) w₁ * w₂).im / Complex.normSq w₁`.

Rewrite using `[Complex.div_im]`. Simplify using `only [Complex.mul_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `div_pos h (Complex.normSq_pos.mpr hw)`.

Establish `h3` using `discr_scaled w₁ hw ⟨w₂ / w₁, hτ⟩`. Rewrite using `[show w₁ * ((⟨w₂ / w₁, hτ⟩ : UpperHalfPlane) : ℂ) = w₂ by` and apply the resulting hypothesis. Rewrite using `[UpperHalfPlane.coe_mk]`. Use the proof step `field_simp] at h3`.
-/
theorem discr_ne_of_pos (w₁ w₂ : ℂ) (h : 0 < ((starRingEnd ℂ) w₁ * w₂).im) :
    PI.discr (PI.lat2 w₁ w₂) ≠ 0 := by
  have hw : w₁ ≠ 0 := by
    rintro rfl
    simp at h
  have hτ : 0 < (w₂ / w₁).im := by
    have e : (w₂ / w₁).im = ((starRingEnd ℂ) w₁ * w₂).im / Complex.normSq w₁ := by
      rw [Complex.div_im]
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [e]
    exact div_pos h (Complex.normSq_pos.mpr hw)
  have h3 := discr_scaled w₁ hw ⟨w₂ / w₁, hτ⟩
  rwa [show w₁ * ((⟨w₂ / w₁, hτ⟩ : UpperHalfPlane) : ℂ) = w₂ by
    rw [UpperHalfPlane.coe_mk]
    field_simp] at h3

/- English proof (translation)
Introduce `w₁ w₂ h`. Break down `lt_or_gt_of_ne h with hlt | hgt` into its components or cases. Establish `h2 : 0 < ((starRingEnd ℂ) w₂ * w₁).im`. Establish `e : ((starRingEnd ℂ) w₂ * w₁).im = -((starRingEnd ℂ) w₁ * w₂).im`. Simplify using `only [Complex.mul_im, Complex.conj_re, Complex.conj_im]`.

Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hswap : PI.lat2 w₁ w₂ = PI.lat2 w₂ w₁`. Unfold `PI.lat2`. Rewrite using `[Set.pair_comm]`.

Rewrite using `[hswap]`. Conclude with `discr_ne_of_pos w₂ w₁ h2`. Conclude with `discr_ne_of_pos w₁ w₂ hgt`.
-/
theorem discrNe_all : PI.DiscrNe := by
  intro w₁ w₂ h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have h2 : 0 < ((starRingEnd ℂ) w₂ * w₁).im := by
      have e : ((starRingEnd ℂ) w₂ * w₁).im = -((starRingEnd ℂ) w₁ * w₂).im := by
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
      linarith
    have hswap : PI.lat2 w₁ w₂ = PI.lat2 w₂ w₁ := by
      unfold PI.lat2
      rw [Set.pair_comm]
    rw [hswap]
    exact discr_ne_of_pos w₂ w₁ h2
  · exact discr_ne_of_pos w₁ w₂ hgt

end DiscrNeWork

end
