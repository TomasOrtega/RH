import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `f j k r a cs e hf hj hk hN hlie I hI c Q₀ Q hQ hterm φ`. Use `choose εf δf hεf hlief using hlie`. Use `⟨fun p n τ => (φ p n τ).1, fun p n τ m => εf (m - 1) (φ p n τ), fun p n τ m => hεf _ _, ?_⟩` and prove the remaining obligations. Introduce `vol p`. Establish `hN2 : 2 ≤ j + k` using `by omega`.

Establish `hDm : j + k - 1 ≤ flagDim f j k`. Establish `h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1)`. Rewrite using `[mul_comm]`. Conclude with `Nat.mul_le_mul_right _ hN2`. Establish `h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2` using `(Nat.le_div_iff_mul_le (by norm_num)).2 h1`.

Unfold `flagDim`. Conclude with `h2.trans (Nat.le_mul_of_pos_left _ hf)`. Establish `key : ∀ τ : Fin f, ∀ m ∈ Finset.Icc 2 (r + a), ∀ n : ℕ, ((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m) = c * (((p : ℝ) ^ ((n + 1) * m))⁻¹ * ((εf (m - 1) (φ p (n + 1) τ) * RestTerms.restTerm f (r + a) Q₀ m τ (RestTerms.smallPowerSum f r a cs ( …`. Introduce `τ m hm n`. Rewrite `hm` using `[Finset.mem_Icc]`.

Use `set σ := φ p (n + 1) τ`. Establish `hkill : I (rootPsum f j k (m - 1) σ.1 * Q τ m) = 0`. Use `hI.kills (m - 1) σ.1 (Q τ m) (by omega) (by omega) ?_` and prove the remaining obligations. Use `hQ.1 τ m (by omega) (by omega)` as an intermediate fact. Rewrite `this` using `[show flagDim f j k + 1 - m = flagDim f j k - (m - 1) by omega]`. Then use the resulting hypothesis.

Establish `ht` using `hterm m hm.1 hm.2 τ σ.1`. Establish `hI' : I (lieClass f j k (m - 1) σ * Q τ m) = (εf (m - 1) σ : ℝ) * (c * (RestTerms.flagIntegral f (r + a) (RestTerms.smallPowerSum f r a cs (m - 1) σ.1 * Q₀ m τ) : ℝ))`. Rewrite using `[hlief, add_mul, mul_assoc, mul_assoc, C_mul', C_mul', map_add, LinearMap.map_smul, LinearMap.map_smul, hkill, ht, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]`. Rewrite using `[hI', RestTerms.restTerm]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Unfold `restAt RestTerms.restPrimeModel`. Rewrite using `[← hN]`. Establish `: ∀ τ : Fin f, ∑ m ∈ Finset.Icc 2 (r + a), ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m) = c * ∑ m ∈ Finset.Icc 2 (r + a), ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * m))⁻¹ * ((εf (m - 1) (φ p (n + 1) τ) * RestTerms.restTerm f (r + a) Q₀ m τ ( …`. Introduce `τ`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[← tsum_mul_left]`. Conclude with `tsum_congr fun n => key τ m hm n`. Repeatedly rewrite using `[this, ← Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem RestCutPrimeEq.proof : RestCutPrimeEq.Statement := by
  intro f j k r a cs e hf hj hk hN hlie I hI c Q₀ Q hQ hterm φ
  choose εf δf hεf hlief using hlie
  refine ⟨fun p n τ => (φ p n τ).1, fun p n τ m => εf (m - 1) (φ p n τ),
    fun p n τ m => hεf _ _, ?_⟩
  intro vol p
  have hN2 : 2 ≤ j + k := by omega
  have hDm : j + k - 1 ≤ flagDim f j k := by
    have h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1) := by
      rw [mul_comm]; exact Nat.mul_le_mul_right _ hN2
    have h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h1
    unfold flagDim
    exact h2.trans (Nat.le_mul_of_pos_left _ hf)
  have key : ∀ τ : Fin f, ∀ m ∈ Finset.Icc 2 (r + a), ∀ n : ℕ,
      ((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m) =
        c * (((p : ℝ) ^ ((n + 1) * m))⁻¹ *
          ((εf (m - 1) (φ p (n + 1) τ) * RestTerms.restTerm f (r + a) Q₀ m τ
            (RestTerms.smallPowerSum f r a cs (m - 1) (φ p (n + 1) τ).1) : ℚ) : ℝ)) := by
    intro τ m hm n
    rw [Finset.mem_Icc] at hm
    set σ := φ p (n + 1) τ
    have hkill : I (rootPsum f j k (m - 1) σ.1 * Q τ m) = 0 := by
      refine hI.kills (m - 1) σ.1 (Q τ m) (by omega) (by omega) ?_
      have := hQ.1 τ m (by omega) (by omega)
      rwa [show flagDim f j k + 1 - m = flagDim f j k - (m - 1) by omega] at this
    have ht := hterm m hm.1 hm.2 τ σ.1
    have hI' : I (lieClass f j k (m - 1) σ * Q τ m) = (εf (m - 1) σ : ℝ) *
        (c * (RestTerms.flagIntegral f (r + a)
          (RestTerms.smallPowerSum f r a cs (m - 1) σ.1 * Q₀ m τ) : ℝ)) := by
      rw [hlief, add_mul, mul_assoc, mul_assoc, C_mul', C_mul', map_add, LinearMap.map_smul,
        LinearMap.map_smul, hkill, ht, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
    rw [hI', RestTerms.restTerm]
    push_cast
    ring
  unfold restAt RestTerms.restPrimeModel
  rw [← hN]
  have : ∀ τ : Fin f, ∑ m ∈ Finset.Icc 2 (r + a), ∑' n : ℕ,
      ((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m) =
      c * ∑ m ∈ Finset.Icc 2 (r + a), ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * m))⁻¹ *
          ((εf (m - 1) (φ p (n + 1) τ) * RestTerms.restTerm f (r + a) Q₀ m τ
            (RestTerms.smallPowerSum f r a cs (m - 1) (φ p (n + 1) τ).1) : ℚ) : ℝ) := by
    intro τ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun n => key τ m hm n
  simp_rw [this, ← Finset.mul_sum]
  ring

end GroundTheory.Heights₂.Heights
