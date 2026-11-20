import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.HsTrace

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

/- English proof (translation)
Simplify using `only [Jm, dotProduct, mulVec_diagonal, star_sum, star_mul', star_star, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp <;> ring`.
-/
private theorem star_dotProduct_Jm_mulVec_comm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n → ℂ) :
    star (star a ⬝ᵥ (Jm ε *ᵥ b)) = star b ⬝ᵥ (Jm ε *ᵥ a) := by
  simp only [Jm, dotProduct, mulVec_diagonal, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

/- English proof (translation)
Take `⟨w, hw⟩ : ∃ w : Fin n → ℂ, w = y - z` from `⟨_, rfl⟩`. Rewrite using `[← hw]`. Establish `hzy : star z ⬝ᵥ (Jm ε *ᵥ y) = c`. Rewrite using `[← star_dotProduct_Jm_mulVec_comm, hyz, Complex.star_def, Complex.conj_ofReal]`. Establish `hq : star w ⬝ᵥ (Jm ε *ᵥ w) = 2 - 2 * (c : ℂ)`.

Rewrite using `[hw, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hy, hz, hyz, hzy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwz : star w ⬝ᵥ (Jm ε *ᵥ z) = c - 1`. Rewrite using `[hw, star_sub, sub_dotProduct, hyz, hz]`. Establish `hpos : (0 : ℝ) < 2 - 2 * c` using `by linarith`.

Take `⟨k, hkdef⟩ : ∃ k : ℝ, k = 2 / (2 - 2 * c)` from `⟨_, rfl⟩`. Establish `hk : k * (2 - 2 * c) = 2` using `by rw [hkdef, div_mul_cancel₀ _ (ne_of_gt hpos)]`. Establish `hk0 : 0 < k` using `by rw [hkdef]; exact div_pos (by norm_num) hpos`. Establish `hk1 : k ≤ 1` using `by nlinarith`. Establish `hkC : (k : ℂ) * (2 - 2 * (c : ℂ)) = 2` using `by exact_mod_cast hk`.

Establish `hq' : (star w ᵥ* Jm ε) ⬝ᵥ w = 2 - 2 * (c : ℂ)` using `by rw [← dotProduct_mulVec, hq]`. Establish `hbj : ∀ j, ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖ ^ 2 = k ^ 2 * ‖w j‖ ^ 2`. Introduce `j`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Jm, vecMul_diagonal, norm_mul, Pi.star_apply, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0]`. Apply the tactic sequence `split_ifs <;> simp <;> ring`.

Establish `h1 : ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = n`. Simplify using `[Matrix.one_apply, apply_ite]`. Establish `h2 : ∑ i : Fin n, ∑ j : Fin n, ‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2) = k ^ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2`. Simplify using `only [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, ← Finset.mul_sum, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)))ᴴ * Jm ε * (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε))) = Jm ε`. Establish `hsb : star ((k : ℂ) • (star w ᵥ* Jm ε)) = (k : ℂ) • (Jm ε *ᵥ w)`. Rewrite using `[star_smul, Matrix.star_vecMul, star_star, Jm_conjTranspose, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[conjTranspose_sub, conjTranspose_one, conjTranspose_vecMulVec, hsb]`.

Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, hq']`. Use extensionality with `i j`. Simplify using `only [Matrix.sub_apply, vecMulVec_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Take the linear combination `((k : ℂ) * ((Jm ε *ᵥ w) i * (star w ᵥ* Jm ε) j)) * hkC`. Establish `hkc : (k : ℂ) * ((c : ℂ) - 1) = -1` using `by linear_combination (-1 / 2 : ℂ) * hkC`.

Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_dotProduct, ← dotProduct_mulVec, hwz, smul_eq_mul, hkc, hw]`. Use extensionality with `i`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.sub_apply, vecMulVec_apply]`.

Establish `h3` using `norm_sub_le ((1 : Matrix (Fin n) (Fin n) ℂ) i j) (w i * ((k : ℂ) • (star w ᵥ* Jm ε)) j)`. Rewrite `h3` using `[norm_mul]`. Establish `h4` using `pow_le_pow_left₀ (norm_nonneg _) h3 2`. Establish `hp : (‖w i‖ * ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖) ^ 2 = ‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2)`. Rewrite using `[mul_pow, hbj]`.

Use polynomial arithmetic with `[sq_nonneg (‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ - ‖w i‖ * ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖)]`. Use `_ = 2 * n + 2 * (k ^ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2) := by`. Rewrite using `[← h1, ← h2]`. Simplify using `only [Finset.sum_add_distrib, Finset.mul_sum]`. Use `_ ≤ 2 * n + 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2 := by`.

Establish `hk2 : k ^ 2 ≤ 1` using `by nlinarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hk2 (sq_nonneg (GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w))]`.
-/
theorem refl_ex {n : ℕ} (ε : Fin n → Bool) (z y : Fin n → ℂ) (hz : star z ⬝ᵥ (Jm ε *ᵥ z) = 1) (hy : star y ⬝ᵥ (Jm ε *ᵥ y) = 1)
    (c : ℝ) (hc : c ≤ 0) (hyz : star y ⬝ᵥ (Jm ε *ᵥ z) = c) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, inUJ ε R ∧ R *ᵥ z = y ∧ hs R ≤ 2 * n + 2 * nsq (y - z) ^ 2 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ℂ, w = y - z := ⟨_, rfl⟩
  rw [← hw]
  have hzy : star z ⬝ᵥ (Jm ε *ᵥ y) = c := by
    rw [← star_dotProduct_Jm_mulVec_comm, hyz, Complex.star_def, Complex.conj_ofReal]
  have hq : star w ⬝ᵥ (Jm ε *ᵥ w) = 2 - 2 * (c : ℂ) := by
    rw [hw, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hy, hz, hyz, hzy]
    ring
  have hwz : star w ⬝ᵥ (Jm ε *ᵥ z) = c - 1 := by
    rw [hw, star_sub, sub_dotProduct, hyz, hz]
  have hpos : (0 : ℝ) < 2 - 2 * c := by linarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = 2 / (2 - 2 * c) := ⟨_, rfl⟩
  have hk : k * (2 - 2 * c) = 2 := by rw [hkdef, div_mul_cancel₀ _ (ne_of_gt hpos)]
  have hk0 : 0 < k := by rw [hkdef]; exact div_pos (by norm_num) hpos
  have hk1 : k ≤ 1 := by nlinarith
  have hkC : (k : ℂ) * (2 - 2 * (c : ℂ)) = 2 := by exact_mod_cast hk
  have hq' : (star w ᵥ* Jm ε) ⬝ᵥ w = 2 - 2 * (c : ℂ) := by rw [← dotProduct_mulVec, hq]
  have hbj : ∀ j, ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖ ^ 2 = k ^ 2 * ‖w j‖ ^ 2 := by
    intro j
    simp only [Pi.smul_apply, smul_eq_mul, Jm, vecMul_diagonal, norm_mul, Pi.star_apply, norm_star,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0]
    split_ifs <;> simp <;> ring
  have h1 : ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = n := by
    simp [Matrix.one_apply, apply_ite]
  have h2 : ∑ i : Fin n, ∑ j : Fin n, ‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2) = k ^ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2 := by
    simp only [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  refine ⟨1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)), ?_, ?_, ?_⟩
  · show (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)))ᴴ * Jm ε * (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε))) = Jm ε
    have hsb : star ((k : ℂ) • (star w ᵥ* Jm ε)) = (k : ℂ) • (Jm ε *ᵥ w) := by
      rw [star_smul, Matrix.star_vecMul, star_star, Jm_conjTranspose, Complex.star_def, Complex.conj_ofReal]
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_vecMulVec, hsb]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul,
      Matrix.mul_vecMulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, hq']
    ext i j
    simp only [Matrix.sub_apply, vecMulVec_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination ((k : ℂ) * ((Jm ε *ᵥ w) i * (star w ᵥ* Jm ε) j)) * hkC
  · have hkc : (k : ℂ) * ((c : ℂ) - 1) = -1 := by linear_combination (-1 / 2 : ℂ) * hkC
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_dotProduct,
      ← dotProduct_mulVec, hwz, smul_eq_mul, hkc, hw]
    ext i
    simp
  · calc hs (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)))
        = ∑ i, ∑ j, ‖(1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε))) i j‖ ^ 2 := rfl
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (2 * ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
            + 2 * (‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2))) := by
        gcongr with i _ j _
        rw [Matrix.sub_apply, vecMulVec_apply]
        have h3 := norm_sub_le ((1 : Matrix (Fin n) (Fin n) ℂ) i j) (w i * ((k : ℂ) • (star w ᵥ* Jm ε)) j)
        rw [norm_mul] at h3
        have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        have hp : (‖w i‖ * ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖) ^ 2 = ‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2) := by
          rw [mul_pow, hbj]
        nlinarith [sq_nonneg (‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ - ‖w i‖ * ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖)]
      _ = 2 * n + 2 * (k ^ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2) := by
        rw [← h1, ← h2]
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * n + 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2 := by
        have hk2 : k ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hk2 (sq_nonneg (GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w))]

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `gcongr with i _`. Simplify using `only [Pi.sub_apply]`. Establish `h` using `norm_sub_le (a i) (b i)`.

Establish `h4` using `pow_le_pow_left₀ (norm_nonneg _) h 2`. Use polynomial arithmetic with `[sq_nonneg (‖a i‖ - ‖b i‖)]`.
-/
private theorem nsq_sub_le_two_mul_add {n : ℕ} (a b : Fin n → ℂ) :
    GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (a - b) ≤ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq a + 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq b := by
  unfold GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  gcongr with i _
  simp only [Pi.sub_apply]
  have h := norm_sub_le (a i) (b i)
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun i _ => by positivity`.
-/
private theorem nsq_nonneg_hilbert_schmidt_traces {n : ℕ} (a : Fin n → ℂ) : 0 ≤ GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq a :=
  Finset.sum_nonneg fun i _ => by positivity

/- English proof (translation)
Introduce `n ε z y hz hnz hy`. Establish `hn : 1 ≤ n`. Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `at hz`.

Conclude with `h`. Take `⟨a, ha⟩ : ∃ a : ℂ, a = star y ⬝ᵥ (Jm ε *ᵥ z)` from `⟨_, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu1, hua⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ star u * a = -(‖a‖ : ℂ) := by`. Distinguish the cases in `h0 : a = 0`. Conclude with `⟨1, by simp, by simp [h0]⟩`.

Establish `hn0 : (‖a‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.mpr h0`. Establish `hsq : star a * a = (‖a‖ : ℂ) ^ 2` using `by rw [Complex.star_def, Complex.conj_mul']`. Use `⟨-(a / (‖a‖ : ℂ)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr h0)]`. Rewrite using `[star_neg, star_div₀, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, neg_mul, div_mul_eq_mul_div, hsq, sq, mul_div_assoc, div_self hn0, mul_one]`.

Establish `hu2 : star u * u = 1`. Rewrite using `[Complex.star_def, Complex.conj_mul', hu1]`. Simplify using the standard rewrite rules. Establish `hy' : star (u • y) ⬝ᵥ (Jm ε *ᵥ (u • y)) = 1`. Rewrite using `[star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hy, smul_eq_mul, smul_eq_mul, mul_one, hu2]`.

Establish `hyz' : star (u • y) ⬝ᵥ (Jm ε *ᵥ z) = ((-‖a‖ : ℝ) : ℂ)`. Rewrite using `[star_smul, smul_dotProduct, ← ha, smul_eq_mul, hua]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨R, hR, hRz, hRs⟩` from `refl_ex ε z (u • y) hz hy' (-‖a‖) (by simp) hyz'`.

Establish `hR' : Rᴴ * Jm ε * R = Jm ε` using `hR`. Establish `hg : (star u • R)ᴴ * Jm ε * (star u • R) = Jm ε`. Rewrite using `[conjTranspose_smul, star_star]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, hR', smul_smul]`. Rewrite using `[hu2, one_smul]`.

Establish `hinv : (Jm ε * (star u • R)ᴴ * Jm ε) * (star u • R) = 1`. Rewrite using `[show Jm ε * (star u • R)ᴴ * Jm ε * (star u • R) = Jm ε * ((star u • R)ᴴ * Jm ε * (star u • R)) by simp only [Matrix.mul_assoc], hg, Jm_mul_self]`. Use `⟨⟨⟨star u • R, Jm ε * (star u • R)ᴴ * Jm ε, mul_eq_one_comm.mp hinv, hinv⟩, hg⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show (star u • R) *ᵥ z = y`. Rewrite using `[Matrix.smul_mulVec, hRz, smul_smul, hu2, one_smul]`.

Use `show hs (star u • R) ≤ 16 * ((n : ℝ) + GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y) ^ 2`. Establish `hsu : hs (star u • R) = hs R`. Simplify using `[hs, Matrix.smul_apply, norm_mul, norm_star, hu1]`. Establish `hnu : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (u • y) = GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y`. Simplify using `[GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, norm_mul, hu1]`.

Establish `hD` using `nsq_sub_le_two_mul_add (u • y) z`. Rewrite `hD` using `[hnu, hnz]`. Establish `hD0` using `nsq_nonneg_hilbert_schmidt_traces (u • y - z)`. Establish `hs0` using `nsq_nonneg_hilbert_schmidt_traces y`. Establish `hn' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`.

Establish `hsq : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (u • y - z) ^ 2 ≤ (2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y + 2 * 1) ^ 2` using `pow_le_pow_left₀ hD0 hD 2`. Rewrite using `[hsu]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem boost : ∀ {n : ℕ} (ε : Fin n → Bool) (z y : Fin n → ℂ), star z ⬝ᵥ (Jm ε *ᵥ z) = 1 → nsq z = 1 → star y ⬝ᵥ (Jm ε *ᵥ y) = 1 → ∃ g : UJ ε, umat g *ᵥ z = y ∧ hs (umat g) ≤ 16 * ((n : ℝ) + nsq y) ^ 2 := by
  classical
  intro n ε z y hz hnz hy
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hz
    · exact h
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = star y ⬝ᵥ (Jm ε *ᵥ z) := ⟨_, rfl⟩
  obtain ⟨u, hu1, hua⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ star u * a = -(‖a‖ : ℂ) := by
    by_cases h0 : a = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn0 : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      have hsq : star a * a = (‖a‖ : ℂ) ^ 2 := by rw [Complex.star_def, Complex.conj_mul']
      refine ⟨-(a / (‖a‖ : ℂ)), ?_, ?_⟩
      · rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_ne_zero_iff.mpr h0)]
      · rw [star_neg, star_div₀, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, neg_mul,
          div_mul_eq_mul_div, hsq, sq, mul_div_assoc, div_self hn0, mul_one]
  have hu2 : star u * u = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hu1]
    simp
  have hy' : star (u • y) ⬝ᵥ (Jm ε *ᵥ (u • y)) = 1 := by
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hy, smul_eq_mul,
      smul_eq_mul, mul_one, hu2]
  have hyz' : star (u • y) ⬝ᵥ (Jm ε *ᵥ z) = ((-‖a‖ : ℝ) : ℂ) := by
    rw [star_smul, smul_dotProduct, ← ha, smul_eq_mul, hua]
    push_cast
    ring
  obtain ⟨R, hR, hRz, hRs⟩ := refl_ex ε z (u • y) hz hy' (-‖a‖) (by simp) hyz'
  have hR' : Rᴴ * Jm ε * R = Jm ε := hR
  have hg : (star u • R)ᴴ * Jm ε * (star u • R) = Jm ε := by
    rw [conjTranspose_smul, star_star]
    simp only [Matrix.smul_mul, Matrix.mul_smul, hR', smul_smul]
    rw [hu2, one_smul]
  have hinv : (Jm ε * (star u • R)ᴴ * Jm ε) * (star u • R) = 1 := by
    rw [show Jm ε * (star u • R)ᴴ * Jm ε * (star u • R)
        = Jm ε * ((star u • R)ᴴ * Jm ε * (star u • R)) by simp only [Matrix.mul_assoc], hg, Jm_mul_self]
  refine ⟨⟨⟨star u • R, Jm ε * (star u • R)ᴴ * Jm ε, mul_eq_one_comm.mp hinv, hinv⟩, hg⟩, ?_, ?_⟩
  · show (star u • R) *ᵥ z = y
    rw [Matrix.smul_mulVec, hRz, smul_smul, hu2, one_smul]
  · show hs (star u • R) ≤ 16 * ((n : ℝ) + GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y) ^ 2
    have hsu : hs (star u • R) = hs R := by
      simp [hs, Matrix.smul_apply, norm_mul, norm_star, hu1]
    have hnu : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (u • y) = GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y := by
      simp [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, norm_mul, hu1]
    have hD := nsq_sub_le_two_mul_add (u • y) z
    rw [hnu, hnz] at hD
    have hD0 := nsq_nonneg_hilbert_schmidt_traces (u • y - z)
    have hs0 := nsq_nonneg_hilbert_schmidt_traces y
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (u • y - z) ^ 2 ≤ (2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y + 2 * 1) ^ 2 :=
      pow_le_pow_left₀ hD0 hD 2
    rw [hsu]
    nlinarith

end PositivityTheory.UnitaryDecomposition.X4
