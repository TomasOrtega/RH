import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `κ M L t c c1 c2 σ ρ hκ hM hL ht0 ht1 hc0 hc1 h1 h2 h3 hσ hσ2 hρ`. Establish `hL0 : 0 < L` using `by linarith`. Establish `hi0 : 0 < L⁻¹` using `inv_pos.mpr hL0`. Establish `hi : L⁻¹ ≤ 2`. Rewrite using `[inv_le_comm₀ hL0 (by norm_num)]; linarith`.

Establish `hi2 : L⁻¹ ^ 2 ≤ 4` using `by nlinarith`. Establish `ha : |c1 / L| ≤ 2 * M`. Rewrite using `[div_eq_mul_inv, abs_mul, abs_of_pos hi0, mul_comm 2 M]`. Conclude with `mul_le_mul h1 hi hi0.le hM`. Establish `hb : |c2 / L ^ 2| ≤ 4 * M`.

Rewrite using `[div_eq_mul_inv, ← inv_pow, abs_mul, abs_of_pos (pow_pos hi0 2), mul_comm 4 M]`. Conclude with `mul_le_mul h2 hi2 (pow_pos hi0 2).le hM`. Establish `ha2 : (c1 / L) ^ 2 ≤ 4 * M * c`. Rewrite using `[div_eq_mul_inv, mul_pow]`. Combine the equalities or inequalities in the displayed calculation.

Generalize the expression as in `c1 / L = a at *`. Generalize the expression as in `c2 / L ^ 2 = b at *`. Establish `hs0 : 0 ≤ 1 - σ` using `by linarith`. Establish `hs1 : 1 - σ ≤ 1` using `by linarith`. Establish `hcs0 : 0 ≤ c * (1 - σ)` using `mul_nonneg hc0 hs0`.

Establish `hcs1 : c * (1 - σ) ≤ c` using `mul_le_of_le_one_right hc0 hs1`. Establish `hts0 : 0 ≤ t * σ` using `mul_nonneg ht0 hσ.le`. Establish `hts1 : t * σ ≤ σ` using `mul_le_of_le_one_left hσ.le ht1`. Establish `eA : t * (a * σ + c * (-κ * σ * (1 - σ))) = (t * σ) * (a - κ * (c * (1 - σ)))` using `by ring`. Establish `eB : t * (b * σ + 2 * a * (-κ * σ * (1 - σ)) + c * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ))) = (t * σ) * (b - 2 * κ * (a * (1 - σ)) + κ ^ 2 * (c * (1 - σ) * (1 - 2 * σ)))` using `by ring`.

Rewrite using `[eA, eB]`. Establish `hA : |a - κ * (c * (1 - σ))| ≤ 2 * M + κ`. Use `abs_le.mp ha` as an intermediate fact. Establish `h5 : κ * (c * (1 - σ)) ≤ κ` using `mul_le_of_le_one_right hκ.le (hcs1.trans hc1)`. Establish `h6 : 0 ≤ κ * (c * (1 - σ))` using `mul_nonneg hκ.le hcs0`.

Apply the tactic sequence `rw [abs_le]; constructor <;> linarith [this.1, this.2]`. Establish `hB : |b - 2 * κ * (a * (1 - σ)) + κ ^ 2 * (c * (1 - σ) * (1 - 2 * σ))| ≤ 4 * M + 4 * M * κ + κ ^ 2`. Establish `hb'` using `abs_le.mp hb`. Establish `h5 : |a * (1 - σ)| ≤ 2 * M`. Rewrite using `[abs_mul, abs_of_nonneg hs0]`.

Conclude with `(mul_le_of_le_one_right (abs_nonneg a) hs1).trans ha`. Establish `h5'` using `abs_le.mp h5`. Establish `h6 : 0 ≤ c * (1 - σ) * (1 - 2 * σ)` using `mul_nonneg hcs0 (by linarith)`. Establish `h7 : c * (1 - σ) * (1 - 2 * σ) ≤ 1` using `(mul_le_of_le_one_right hcs0 (by linarith)).trans (hcs1.trans hc1)`. Establish `h8` using `mul_le_mul_of_nonneg_left h5'.1 hκ.le`.

Establish `h9` using `mul_le_mul_of_nonneg_left h5'.2 hκ.le`. Establish `h10` using `mul_le_mul_of_nonneg_left h7 (sq_nonneg κ)`. Establish `h11` using `mul_nonneg (sq_nonneg κ) h6`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith [hb'.1, hb'.2, sq_nonneg κ]`. Establish `hf0 : 0 ≤ t * (c * σ)` using `mul_nonneg ht0 (mul_nonneg hc0 hσ.le)`.

Establish `hf1 : t * (c * σ) ≤ σ` using `(mul_le_of_le_one_left (mul_nonneg hc0 hσ.le) ht1).trans (mul_le_of_le_one_left hσ.le hc1)`. Establish `hMκ : 0 ≤ M * κ` using `mul_nonneg hM hκ.le`. Establish `hMκ2 : 0 ≤ M * κ ^ 2` using `mul_nonneg hM (sq_nonneg κ)`. Take `⟨K, hK⟩ : ∃ K : ℝ, K = (M + 1) * (κ + 1) ^ 2` from `⟨_, rfl⟩`. Establish `hK0 : 0 ≤ K` using `by rw [hK]; positivity`.

Establish `hK1 : 2 * M + κ + (4 * M + 4 * M * κ + κ ^ 2) ≤ 6 * K`. Rewrite using `[hK]`. Combine the linear relations using `[sq_nonneg κ]`. Establish `hK2 : 8 * M + 2 * κ ^ 2 ≤ 8 * K`. Rewrite using `[hK]`.

Combine the linear relations using `[sq_nonneg κ]`. Establish `eK : 100 * (M + 1) * (κ + 1) ^ 2 = 100 * K` using `by rw [hK]; ring`. Rewrite using `[eK]`. Establish `hsum : |t * σ * (a - κ * (c * (1 - σ)))| + |t * σ * (b - 2 * κ * (a * (1 - σ)) + κ ^ 2 * (c * (1 - σ) * (1 - 2 * σ)))| ≤ σ * (6 * K)`. Rewrite using `[abs_mul (t * σ), abs_mul (t * σ), abs_of_nonneg hts0, ← mul_add]`.

Conclude with `mul_le_mul hts1 (by linarith) (by positivity) hσ.le`. Establish `hD : σ ≤ 2 * (t * (c * σ) + ρ * (1 - t * (c * σ)))`. Establish `: ρ * (1 / 2) ≤ ρ * (1 - t * (c * σ))` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE : σ ≤ 1 - t * (c * σ)` using `by linarith`.

Establish `hsq : (a - κ * (c * (1 - σ))) ^ 2 ≤ c * (8 * K)`. Establish `h5 : (c * (1 - σ)) ^ 2 ≤ c`. Rewrite using `[sq]`. Conclude with `(mul_le_of_le_one_right hcs0 (hcs1.trans hc1)).trans hcs1`. Establish `h6` using `mul_le_mul_of_nonneg_left h5 (sq_nonneg κ)`.

Establish `h7` using `mul_le_mul_of_nonneg_left hK2 hc0`. Combine the linear relations using `[sq_nonneg (a + κ * (c * (1 - σ)))]`. Establish `hKσ : 0 ≤ K * σ` using `mul_nonneg hK0 hσ.le`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left hE hK0` as an intermediate fact.

Generalize the expression as in `1 - t * (c * σ) = D at *`. Combine the linear equalities and inequalities to obtain the conclusion. Use `mul_le_mul_of_nonneg_left hD hK0` as an intermediate fact. Generalize the expression as in `t * (c * σ) + ρ * (1 - t * (c * σ)) = D at *`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hKf : 0 ≤ K * (t * (c * σ))` using `mul_nonneg hK0 hf0`. Establish `h5` using `mul_le_mul_of_nonneg_left hD hKf`. Establish `h6 : (t * σ * (a - κ * (c * (1 - σ)))) ^ 2 ≤ (t * σ) * σ * (c * (8 * K))`. Rewrite using `[mul_pow]`. Use `mul_le_mul ?_ hsq (sq_nonneg _) (mul_nonneg hts0 hσ.le)` and prove the remaining obligations.

Rewrite using `[sq]`. Conclude with `mul_le_mul_of_nonneg_left hts1 hts0`. Establish `h7 : 0 ≤ K * (t * (c * σ)) * σ` using `mul_nonneg hKf hσ.le`. Establish `h8 : (t * σ) * σ * (c * (8 * K)) = 8 * (K * (t * (c * σ)) * σ)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem profile_deriv_bounds_of_le_half :
    ∀ (κ M L t c c1 c2 σ ρ : ℝ), 0 < κ → 0 ≤ M → 1 / 2 ≤ L → 0 ≤ t → t ≤ 1 → 0 ≤ c → c ≤ 1 → |c1| ≤ M → |c2| ≤ M → c1 ^ 2 ≤ M * c → 0 < σ → σ ≤ 1 / 2 → σ ≤ ρ → |t * (c1 / L * σ + c * (-κ * σ * (1 - σ)))| + |t * (c2 / L ^ 2 * σ + 2 * (c1 / L) * (-κ * σ * (1 - σ)) + c * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ)))| ≤ 100 * (M + 1) * (κ + 1) ^ 2 * (1 - t * (c * σ)) ∧ |t * (c1 / L * σ + c * (-κ * σ * (1 - σ)))| + |t * (c2 / L ^ 2 * σ + 2 * (c1 / L) * (-κ * σ * (1 - σ)) + c * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ)))| ≤ 100 * (M + 1) * (κ + 1) ^ 2 * (t * (c * σ) + ρ * (1 - t * (c * σ))) ∧ (t * (c1 / L * σ + c * (-κ * σ * (1 - σ)))) ^ 2 ≤ 100 * (M + 1) * (κ + 1) ^ 2 * (t * (c * σ)) * (t * (c * σ) + ρ * (1 - t * (c * σ))) := by
  intro κ M L t c c1 c2 σ ρ hκ hM hL ht0 ht1 hc0 hc1 h1 h2 h3 hσ hσ2 hρ
  have hL0 : 0 < L := by linarith
  have hi0 : 0 < L⁻¹ := inv_pos.mpr hL0
  have hi : L⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hL0 (by norm_num)]; linarith
  have hi2 : L⁻¹ ^ 2 ≤ 4 := by nlinarith
  have ha : |c1 / L| ≤ 2 * M := by
    rw [div_eq_mul_inv, abs_mul, abs_of_pos hi0, mul_comm 2 M]
    exact mul_le_mul h1 hi hi0.le hM
  have hb : |c2 / L ^ 2| ≤ 4 * M := by
    rw [div_eq_mul_inv, ← inv_pow, abs_mul, abs_of_pos (pow_pos hi0 2), mul_comm 4 M]
    exact mul_le_mul h2 hi2 (pow_pos hi0 2).le hM
  have ha2 : (c1 / L) ^ 2 ≤ 4 * M * c := by
    rw [div_eq_mul_inv, mul_pow]
    calc c1 ^ 2 * L⁻¹ ^ 2 ≤ (M * c) * 4 :=
          mul_le_mul h3 hi2 (pow_pos hi0 2).le (mul_nonneg hM hc0)
      _ = 4 * M * c := by ring
  generalize c1 / L = a at *
  generalize c2 / L ^ 2 = b at *
  have hs0 : 0 ≤ 1 - σ := by linarith
  have hs1 : 1 - σ ≤ 1 := by linarith
  have hcs0 : 0 ≤ c * (1 - σ) := mul_nonneg hc0 hs0
  have hcs1 : c * (1 - σ) ≤ c := mul_le_of_le_one_right hc0 hs1
  have hts0 : 0 ≤ t * σ := mul_nonneg ht0 hσ.le
  have hts1 : t * σ ≤ σ := mul_le_of_le_one_left hσ.le ht1
  have eA : t * (a * σ + c * (-κ * σ * (1 - σ))) = (t * σ) * (a - κ * (c * (1 - σ))) := by ring
  have eB : t * (b * σ + 2 * a * (-κ * σ * (1 - σ)) + c * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ)))
      = (t * σ) * (b - 2 * κ * (a * (1 - σ)) + κ ^ 2 * (c * (1 - σ) * (1 - 2 * σ))) := by ring
  rw [eA, eB]
  have hA : |a - κ * (c * (1 - σ))| ≤ 2 * M + κ := by
    have := abs_le.mp ha
    have h5 : κ * (c * (1 - σ)) ≤ κ := mul_le_of_le_one_right hκ.le (hcs1.trans hc1)
    have h6 : 0 ≤ κ * (c * (1 - σ)) := mul_nonneg hκ.le hcs0
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hB : |b - 2 * κ * (a * (1 - σ)) + κ ^ 2 * (c * (1 - σ) * (1 - 2 * σ))|
      ≤ 4 * M + 4 * M * κ + κ ^ 2 := by
    have hb' := abs_le.mp hb
    have h5 : |a * (1 - σ)| ≤ 2 * M := by
      rw [abs_mul, abs_of_nonneg hs0]
      exact (mul_le_of_le_one_right (abs_nonneg a) hs1).trans ha
    have h5' := abs_le.mp h5
    have h6 : 0 ≤ c * (1 - σ) * (1 - 2 * σ) := mul_nonneg hcs0 (by linarith)
    have h7 : c * (1 - σ) * (1 - 2 * σ) ≤ 1 :=
      (mul_le_of_le_one_right hcs0 (by linarith)).trans (hcs1.trans hc1)
    have h8 := mul_le_mul_of_nonneg_left h5'.1 hκ.le
    have h9 := mul_le_mul_of_nonneg_left h5'.2 hκ.le
    have h10 := mul_le_mul_of_nonneg_left h7 (sq_nonneg κ)
    have h11 := mul_nonneg (sq_nonneg κ) h6
    rw [abs_le]; constructor <;> linarith [hb'.1, hb'.2, sq_nonneg κ]
  have hf0 : 0 ≤ t * (c * σ) := mul_nonneg ht0 (mul_nonneg hc0 hσ.le)
  have hf1 : t * (c * σ) ≤ σ :=
    (mul_le_of_le_one_left (mul_nonneg hc0 hσ.le) ht1).trans (mul_le_of_le_one_left hσ.le hc1)
  have hMκ : 0 ≤ M * κ := mul_nonneg hM hκ.le
  have hMκ2 : 0 ≤ M * κ ^ 2 := mul_nonneg hM (sq_nonneg κ)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (M + 1) * (κ + 1) ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hK1 : 2 * M + κ + (4 * M + 4 * M * κ + κ ^ 2) ≤ 6 * K := by
    rw [hK]; linarith [sq_nonneg κ]
  have hK2 : 8 * M + 2 * κ ^ 2 ≤ 8 * K := by
    rw [hK]; linarith [sq_nonneg κ]
  have eK : 100 * (M + 1) * (κ + 1) ^ 2 = 100 * K := by rw [hK]; ring
  rw [eK]
  have hsum : |t * σ * (a - κ * (c * (1 - σ)))| +
      |t * σ * (b - 2 * κ * (a * (1 - σ)) + κ ^ 2 * (c * (1 - σ) * (1 - 2 * σ)))|
      ≤ σ * (6 * K) := by
    rw [abs_mul (t * σ), abs_mul (t * σ), abs_of_nonneg hts0, ← mul_add]
    exact mul_le_mul hts1 (by linarith) (by positivity) hσ.le
  have hD : σ ≤ 2 * (t * (c * σ) + ρ * (1 - t * (c * σ))) := by
    have : ρ * (1 / 2) ≤ ρ * (1 - t * (c * σ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hE : σ ≤ 1 - t * (c * σ) := by linarith
  have hsq : (a - κ * (c * (1 - σ))) ^ 2 ≤ c * (8 * K) := by
    have h5 : (c * (1 - σ)) ^ 2 ≤ c := by
      rw [sq]; exact (mul_le_of_le_one_right hcs0 (hcs1.trans hc1)).trans hcs1
    have h6 := mul_le_mul_of_nonneg_left h5 (sq_nonneg κ)
    have h7 := mul_le_mul_of_nonneg_left hK2 hc0
    linarith [sq_nonneg (a + κ * (c * (1 - σ)))]
  have hKσ : 0 ≤ K * σ := mul_nonneg hK0 hσ.le
  refine ⟨?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hE hK0
    generalize 1 - t * (c * σ) = D at *
    linarith
  · have := mul_le_mul_of_nonneg_left hD hK0
    generalize t * (c * σ) + ρ * (1 - t * (c * σ)) = D at *
    linarith
  · have hKf : 0 ≤ K * (t * (c * σ)) := mul_nonneg hK0 hf0
    have h5 := mul_le_mul_of_nonneg_left hD hKf
    have h6 : (t * σ * (a - κ * (c * (1 - σ)))) ^ 2 ≤ (t * σ) * σ * (c * (8 * K)) := by
      rw [mul_pow]
      refine mul_le_mul ?_ hsq (sq_nonneg _) (mul_nonneg hts0 hσ.le)
      rw [sq]; exact mul_le_mul_of_nonneg_left hts1 hts0
    have h7 : 0 ≤ K * (t * (c * σ)) * σ := mul_nonneg hKf hσ.le
    have h8 : (t * σ) * σ * (c * (8 * K)) = 8 * (K * (t * (c * σ)) * σ) := by ring
    linarith

end GlobalTheory
