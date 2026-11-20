import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagRadicalLowersLeviKeepsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceLoweringMulKeepingIsotropicFlagStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwNear

open GlobalTheory.FlagLeviGroup

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem J_sq : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `nrm Formalism.REAL.hs`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem nrm_J_conj (X : Matrix (Fin n) (Fin n) ℂ) : nrm (Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) = nrm X := by
  unfold nrm Formalism.REAL.hs
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp

/- English proof (translation)
Establish `hg : (uMat g)ᴴ * (Formalism.REAL.Jm ε * uMat g) = Formalism.REAL.Jm ε`. Rewrite using `[← Matrix.mul_assoc]`. Conclude with `g.2`. Establish `h1 : uMat g * uMat g⁻¹ = 1` using `by simp [uMat]`. Establish `h2 : Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = 1`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hg, J_sq]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, Matrix.one_mul]`. Use `_ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := Matrix.mul_assoc _ _ _`. Use `_ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h1, Matrix.mul_one]`.
-/
private theorem uMat_inv_eq_Jm_conjTranspose_Jm (g : Formalism.REAL.UJ ε) :
    uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hg : (uMat g)ᴴ * (Formalism.REAL.Jm ε * uMat g) = Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc]
    exact g.2
  have h1 : uMat g * uMat g⁻¹ = 1 := by simp [uMat]
  have h2 : Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, J_sq]
  calc uMat g⁻¹ = (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by
        rw [h2, Matrix.one_mul]
    _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := Matrix.mul_assoc _ _ _
    _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h1, Matrix.mul_one]

/- English proof (translation)
Establish `e : uMat g⁻¹ - 1 = Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε`. Rewrite using `[uMat_inv_eq_Jm_conjTranspose_Jm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, J_sq]`. Rewrite using `[e, nrm_J_conj, nrm_conjTranspose]`.
-/
theorem nrm_inv (g : Formalism.REAL.UJ ε) : nrm (uMat g⁻¹ - 1) = nrm (uMat g - 1) := by
  have e : uMat g⁻¹ - 1 = Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε := by
    rw [uMat_inv_eq_Jm_conjTranspose_Jm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, J_sq]
  rw [e, nrm_J_conj, nrm_conjTranspose]

/- English proof (translation)
Establish `e : uMat (g * h) - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1)`. Rewrite using `[show uMat (g * h) = uMat g * uMat h from rfl]`. Use `noncomm_ring`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `nrm_add_le _ _`. Use `_ ≤ _ := by gcongr`. Conclude with `nrm_mul_le _ _`.
-/
theorem nrm_mul_sub_one (g h : Formalism.REAL.UJ ε) :
    nrm (uMat (g * h) - 1) ≤ nrm (uMat g - 1) * nrm (uMat h - 1) + nrm (uMat g - 1) + nrm (uMat h - 1) := by
  have e : uMat (g * h) - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
    rw [show uMat (g * h) = uMat g * uMat h from rfl]
    noncomm_ring
  rw [e]
  calc _ ≤ nrm ((uMat g - 1) * (uMat h - 1) + (uMat g - 1)) + nrm (uMat h - 1) := nrm_add_le _ _
    _ ≤ nrm ((uMat g - 1) * (uMat h - 1)) + nrm (uMat g - 1) + nrm (uMat h - 1) := by
        gcongr
        exact nrm_add_le _ _
    _ ≤ _ := by
        gcongr
        exact nrm_mul_le _ _

/- English proof (translation)
Take `⟨hN, hM⟩` from `GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps n ε a j W hW`. Take `⟨htr, -, -, hmul⟩` from `GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag n ε a j W hW`. Establish `hX` using `hN u hu`. Take `⟨hm1, hm2⟩` from `hM m hm`. Establish `hY : uMat m * (uMat m)ᴴ - uMat m ∈ keeps ε W` using `sub_mem (hmul _ hm1 _ hm2) hm1`.

Establish `e : uMat (u * m) - 1 = (uMat u - 1) * uMat m + (uMat m - 1)`. Rewrite using `[show uMat (u * m) = uMat u * uMat m from rfl]`. Use `noncomm_ring`. Establish `key : ((((uMat u - 1) * uMat m) * (uMat m - 1)ᴴ).trace).re = 0`. Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, htr _ hX _ hY, Complex.zero_re]`.

Establish `hh : Formalism.REAL.hs (uMat m - 1) ≤ Formalism.REAL.hs (uMat (u * m) - 1)`. Rewrite using `[e, hs_add, key]`. Combine the linear relations using `[hs_nonneg ((uMat u - 1) * uMat m)]`. Conclude with `Real.sqrt_le_sqrt hh`.
-/
theorem nrm_levi_le {a : ℕ} {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (hW : IsIsoFlag ε j W)
    {u m : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε W) (hm : m ∈ flagM ε W) :
    nrm (uMat m - 1) ≤ nrm (uMat (u * m) - 1) := by

  obtain ⟨hN, hM⟩ := GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps n ε a j W hW
  obtain ⟨htr, -, -, hmul⟩ := GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag n ε a j W hW
  have hX := hN u hu
  obtain ⟨hm1, hm2⟩ := hM m hm
  have hY : uMat m * (uMat m)ᴴ - uMat m ∈ keeps ε W := sub_mem (hmul _ hm1 _ hm2) hm1
  have e : uMat (u * m) - 1 = (uMat u - 1) * uMat m + (uMat m - 1) := by
    rw [show uMat (u * m) = uMat u * uMat m from rfl]
    noncomm_ring
  have key : ((((uMat u - 1) * uMat m) * (uMat m - 1)ᴴ).trace).re = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
      htr _ hX _ hY, Complex.zero_re]
  have hh : Formalism.REAL.hs (uMat m - 1) ≤ Formalism.REAL.hs (uMat (u * m) - 1) := by
    rw [e, hs_add, key]
    linarith [hs_nonneg ((uMat u - 1) * uMat m)]
  exact Real.sqrt_le_sqrt hh

/- English proof (translation)
Introduce `n ε a j W hW t ht`. Take `⟨ρ, hρ0, hρ1, hρt⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 3 ∧ ρ ≤ t / 10` from `⟨min (1 / 3) (t / 10), lt_min (by norm_num) (by linarith), min_le_left _ _, min_le_right _ _⟩`. Use `⟨ρ, hρ0, ?_⟩` and prove the remaining obligations. Introduce `u hu m hm k hx hk`. Establish `hK0` using `nrm_nonneg (uMat k - 1)`.

Establish `hA : nrm (uMat (u * m) - 1) ≤ ρ * ρ + 2 * ρ`. Establish `h` using `nrm_mul_sub_one (u * m * k) k⁻¹`. Rewrite `h` using `[mul_inv_cancel_right, nrm_inv]`. Establish `: nrm (uMat (u * m * k) - 1) * nrm (uMat k - 1) ≤ ρ * ρ` using `mul_le_mul hx hk.le hK0 hρ0.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hM : nrm (uMat m - 1) ≤ nrm (uMat (u * m) - 1)` using `nrm_levi_le hW hu hm`. Establish `hM0` using `nrm_nonneg (uMat m - 1)`. Establish `hU : nrm (uMat u - 1) ≤ nrm (uMat (u * m) - 1) * nrm (uMat m - 1) + nrm (uMat (u * m) - 1) + nrm (uMat m - 1)`. Establish `h` using `nrm_mul_sub_one (u * m) m⁻¹`. Rewrite `h` using `[mul_inv_cancel_right, nrm_inv]`. Then use the resulting hypothesis.

Establish `hρρ : ρ * ρ ≤ ρ / 3` using `by nlinarith`. Establish `hs0 : 0 ≤ ρ * ρ + 2 * ρ` using `by positivity`. Establish `hs1 : ρ * ρ + 2 * ρ ≤ 1` using `by linarith`. Establish `hprod : nrm (uMat (u * m) - 1) * nrm (uMat m - 1) ≤ ρ * ρ + 2 * ρ`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `⟨by linarith, by linarith, by linarith⟩`.
-/
theorem near : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k : Formalism.REAL.UJ ε, nrm (uMat (u * m * k) - 1) ≤ ρ → nrm (uMat k - 1) < ρ → nrm (uMat u - 1) < t ∧ nrm (uMat m - 1) < t ∧ nrm (uMat k - 1) < t := by
  intro n ε a j W hW t ht
  obtain ⟨ρ, hρ0, hρ1, hρt⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 3 ∧ ρ ≤ t / 10 :=
    ⟨min (1 / 3) (t / 10), lt_min (by norm_num) (by linarith), min_le_left _ _, min_le_right _ _⟩
  refine ⟨ρ, hρ0, ?_⟩
  intro u hu m hm k hx hk
  have hK0 := nrm_nonneg (uMat k - 1)

  have hA : nrm (uMat (u * m) - 1) ≤ ρ * ρ + 2 * ρ := by
    have h := nrm_mul_sub_one (u * m * k) k⁻¹
    rw [mul_inv_cancel_right, nrm_inv] at h
    have : nrm (uMat (u * m * k) - 1) * nrm (uMat k - 1) ≤ ρ * ρ := mul_le_mul hx hk.le hK0 hρ0.le
    linarith

  have hM : nrm (uMat m - 1) ≤ nrm (uMat (u * m) - 1) := nrm_levi_le hW hu hm
  have hM0 := nrm_nonneg (uMat m - 1)
  have hU : nrm (uMat u - 1) ≤
      nrm (uMat (u * m) - 1) * nrm (uMat m - 1) + nrm (uMat (u * m) - 1) + nrm (uMat m - 1) := by
    have h := nrm_mul_sub_one (u * m) m⁻¹
    rwa [mul_inv_cancel_right, nrm_inv] at h
  have hρρ : ρ * ρ ≤ ρ / 3 := by nlinarith
  have hs0 : 0 ≤ ρ * ρ + 2 * ρ := by positivity
  have hs1 : ρ * ρ + 2 * ρ ≤ 1 := by linarith
  have hprod : nrm (uMat (u * m) - 1) * nrm (uMat m - 1) ≤ ρ * ρ + 2 * ρ :=
    calc _ ≤ (ρ * ρ + 2 * ρ) * (ρ * ρ + 2 * ρ) := mul_le_mul hA (hM.trans hA) hM0 hs0
      _ ≤ ρ * ρ + 2 * ρ := mul_le_of_le_one_left hs0 hs1
  exact ⟨by linarith, by linarith, by linarith⟩

end GlobalTheory.IwNear
