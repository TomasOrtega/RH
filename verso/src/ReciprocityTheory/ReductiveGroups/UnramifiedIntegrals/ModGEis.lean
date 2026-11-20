import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def latMap {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) (v : Fin 2 → ℤ) : L.lattice :=
  ⟨c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)), (h.2 _).2 ⟨v 0, v 1, rfl⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `v w hvw`. Establish `h1 : c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)) = c * ((w 0 : ℂ) * (τ : ℂ) + (w 1 : ℂ))` using `congrArg Subtype.val hvw`. Establish `h2` using `mul_left_cancel₀ h.1 h1`. Establish `him` using `congrArg Complex.im h2`.

Establish `hre` using `congrArg Complex.re h2`. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him hre`. Establish `hτ : (τ : ℂ).im ≠ 0` using `τ.im_ne_zero`. Establish `h0 : (v 0 : ℝ) = w 0` using `mul_right_cancel₀ hτ him`. Rewrite `hre` using `[h0]`.

Establish `h1' : (v 1 : ℝ) = w 1` using `add_left_cancel hre`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `h0` after adjusting the coercions. Conclude with `h1'` after adjusting the coercions.

Introduce and unpack `⟨x, hx⟩`. Take `⟨u, v, rfl⟩` from `(h.2 x).1 hx`. Conclude with `⟨![u, v], by simp [latMap]⟩`.
-/
theorem latMap_bijective {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    Function.Bijective (latMap h) := by
  constructor
  · intro v w hvw
    have h1 : c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)) = c * ((w 0 : ℂ) * (τ : ℂ) + (w 1 : ℂ)) :=
      congrArg Subtype.val hvw
    have h2 := mul_left_cancel₀ h.1 h1
    have him := congrArg Complex.im h2
    have hre := congrArg Complex.re h2
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him hre
    have hτ : (τ : ℂ).im ≠ 0 := τ.im_ne_zero
    have h0 : (v 0 : ℝ) = w 0 := mul_right_cancel₀ hτ him
    rw [h0] at hre
    have h1' : (v 1 : ℝ) = w 1 := add_left_cancel hre
    funext i
    fin_cases i
    · exact_mod_cast h0
    · exact_mod_cast h1'
  · rintro ⟨x, hx⟩
    obtain ⟨u, v, rfl⟩ := (h.2 x).1 hx
    exact ⟨![u, v], by simp [latMap]⟩

/- English proof (translation)
Establish `hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N` using `1) 0 k τ := by`. Rewrite using `[show E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl, eisensteinSeriesSIF_apply 0 k τ, smul_eq_mul]`. Establish `H` using `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ`. Establish `h1 : L.G k = ∑' v : Fin 2 → ℤ, (c ^ k)⁻¹ * eisSummand k v τ`. Rewrite using `[PeriodPair.G, ← (Equiv.ofBijective _ (latMap_bijective h)).tsum_eq]`.

Use `tsum_congr fun v => ?_` and prove the remaining obligations. Simplify using `[latMap, eisSummand, mul_pow, mul_comm]`. Rewrite using `[h1, tsum_mul_left, H, hE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem G_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    L.G k = (c ^ k)⁻¹ * (2 * riemannZeta k) * E hk τ := by
  have hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := by
    rw [show E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
      eisensteinSeriesSIF_apply 0 k τ, smul_eq_mul]
  have H := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  have h1 : L.G k = ∑' v : Fin 2 → ℤ, (c ^ k)⁻¹ * eisSummand k v τ := by
    rw [PeriodPair.G, ← (Equiv.ofBijective _ (latMap_bijective h)).tsum_eq]
    refine tsum_congr fun v => ?_
    simp [latMap, eisSummand, mul_pow, mul_comm]
  rw [h1, tsum_mul_left, H, hE]
  ring

/- English proof (translation)
Establish `h5 : bernoulli' 5 = 0`. Rewrite using `[bernoulli'_def]`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four]`. Evaluate the numerical expressions using `[Nat.choose]`. Establish `h6 : bernoulli' 6 = 1 / 42`.

Rewrite using `[bernoulli'_def]`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, h5]`. Evaluate the numerical expressions using `[Nat.choose]`. Establish `hB : bernoulli 6 = 1 / 42`. Rewrite using `[bernoulli_eq_bernoulli'_of_ne_one (by norm_num), h6]`.

Establish `h` using `riemannZeta_two_mul_nat (k := 3) (by norm_num)`. Evaluate the numerical expressions using `[Nat.factorial, hB] at h`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sixVal : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four]
    norm_num [Nat.choose]
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four, h5]
    norm_num [Nat.choose]
  have hB : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), h6]
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [Nat.factorial, hB] at h
  rw [h]
  ring

/- English proof (translation)
Rewrite using `[PeriodPair.g₂, G_eq h (k := 4) (by norm_num) ⟨2, rfl⟩, show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]`. Establish `hE : E (k` using `4) (by norm_num) τ = E₄ τ := rfl`. Rewrite using `[hE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem g₂_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ = (c ^ 4)⁻¹ * (4 * (Real.pi : ℂ) ^ 4 / 3) * E₄ τ := by
  rw [PeriodPair.g₂, G_eq h (k := 4) (by norm_num) ⟨2, rfl⟩,
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
  have hE : E (k := 4) (by norm_num) τ = E₄ τ := rfl
  rw [hE]
  ring

/- English proof (translation)
Rewrite using `[PeriodPair.g₃, G_eq h (k := 6) (by norm_num) ⟨3, rfl⟩, show ((6 : ℕ) : ℂ) = 6 by norm_num, sixVal]`. Establish `hE : E (k` using `6) (by norm_num) τ = E₆ τ := rfl`. Rewrite using `[hE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem g₃_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₃ = (c ^ 6)⁻¹ * (8 * (Real.pi : ℂ) ^ 6 / 27) * E₆ τ := by
  rw [PeriodPair.g₃, G_eq h (k := 6) (by norm_num) ⟨3, rfl⟩,
    show ((6 : ℕ) : ℂ) = 6 by norm_num, sixVal]
  have hE : E (k := 6) (by norm_num) τ = E₆ τ := rfl
  rw [hE]
  ring

end ReciprocityTheory.ChartRestriction.L1
