import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.BoundsY
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MCBounds
open scoped ComplexOrder

noncomputable section

/- English proof (translation)
Use extensionality with `j k`. Apply the tactic sequence `by_cases h : j = k <;> simp [h]`.
-/
theorem MCBounds.map_smul_one_sub {g : ℕ} (s : ℝ) (A : Matrix (Fin g) (Fin g) ℝ) :
    (s • (1 : Matrix (Fin g) (Fin g) ℝ) - A).map (fun x : ℝ => (x : ℂ)) =
      (s : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ) - A.map (fun x : ℝ => (x : ℂ)) := by
  ext j k
  by_cases h : j = k <;> simp [h]

/- English proof (translation)
Use extensionality with `j k`. Apply the tactic sequence `by_cases h : j = k <;> simp [h]`.
-/
theorem MCBounds.map_sub_smul_one {g : ℕ} (s : ℝ) (A : Matrix (Fin g) (Fin g) ℝ) :
    (A - s • (1 : Matrix (Fin g) (Fin g) ℝ)).map (fun x : ℝ => (x : ℂ)) =
      A.map (fun x : ℝ => (x : ℂ)) - (s : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  ext j k
  by_cases h : j = k <;> simp [h]

/- English proof (translation)
Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]`.
-/
theorem MCBounds.conj_smul_one_sub {g k : ℕ} (F : Matrix (Fin g) (Fin k) ℂ) (s : ℂ)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    Fᴴ * (s • (1 : Matrix (Fin g) (Fin g) ℂ) - Z) * F = s • (Fᴴ * F) - Fᴴ * Z * F := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/- English proof (translation)
Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]`.
-/
theorem MCBounds.conj_sub_smul_one {g k : ℕ} (F : Matrix (Fin g) (Fin k) ℂ) (s : ℂ)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    Fᴴ * (Z - s • (1 : Matrix (Fin g) (Fin g) ℂ)) * F = Fᴴ * Z * F - s • (Fᴴ * F) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/- English proof (translation)
Rewrite using `[det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]`.
-/
theorem MCBounds.re_det_ofReal_smul {k : ℕ} (s : ℝ) (H : Matrix (Fin k) (Fin k) ℂ) :
    ((s : ℂ) • H).det.re = s ^ k * H.det.re := by
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

/- English proof (translation)
Introduce `D`. Take `⟨C1, hC1, hY⟩` from `exists_Y_le D`. Take `⟨δ, M, hδ, hM, hG⟩` from `exists_gram_bounds D`. Use `set C2 : ℝ := (D.rk : ℝ) * (|Real.log C1| + 1) + |Real.log δ| with hC2`. Use `set C3 : ℝ := |Real.log (D.c⁻¹ ^ D.rk * M)| with hC3`.

Establish `hCC1 : C1 ≤ max C1 (max C2 (max C3 1))` using `le_max_left _ _`. Establish `hCC2 : C2 ≤ max C1 (max C2 (max C3 1))` using `(le_max_left _ _).trans (le_max_right _ _)`. Establish `hCC3 : C3 ≤ max C1 (max C2 (max C3 1))` using `((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)`. Use `set C := max C1 (max C2 (max C3 1)) with hC`. Use `⟨C, by linarith, fun p hp hps => ?_⟩` and prove the remaining obligations.

Establish `hz : p.1 ∈ D.U` using `(D.K_subset hp).1`. Establish `hr1 : 1 ≤ D.radius p.1` using `one_le_radius D hz`. Establish `hlog1 : 1 ≤ Real.log (D.radius p.1)` using `one_le_log_radius D hz`. Use `set r := D.radius p.1 with hr`. Establish `hYc : (D.Y p.1 - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)).PosSemidef` using `D.Y_ge p.1 hps`.

Establish `hYpd : (D.Y p.1).PosDef` using `posDef_of_ge D.c_pos hYc`. Establish `hYle1` using `hY p hp`. Establish `hYle : ((C * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef`. Establish `e : (C * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1 = ((C1 * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1) + ((C - C1) * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)`. Rewrite using `[sub_mul, sub_smul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `hYle1.add (PosSemidef.one.smul (by nlinarith))`. Use `set F := D.f p with hF`. Use `set Yc := (D.Y p.1)⁻¹.map (fun x : ℝ => (x : ℂ)) with hYcdef`.

Establish `hYcPSD : Yc.PosSemidef` using `posSemidef_map_ofReal hYpd.inv.posSemidef`. Establish `hGPSD : (Fᴴ * Yc * F).PosSemidef` using `hYcPSD.conjTranspose_mul_mul_same F`. Establish `hHPSD : (Fᴴ * F).PosSemidef` using `posSemidef_conjTranspose_mul_self F`. Establish `hup : (((D.c⁻¹ : ℝ) : ℂ) • (Fᴴ * F) - Fᴴ * Yc * F).PosSemidef`. Establish `h1` using `posSemidef_map_ofReal (inv_le_of_ge D.c_pos hYc)`.

Rewrite `h1` using `[map_smul_one_sub]`. Use `h1.conjTranspose_mul_mul_same F` as an intermediate fact. Rewrite `this` using `[conj_smul_one_sub]`. Then use the resulting hypothesis. Establish `hdup : (Fᴴ * Yc * F).det.re ≤ D.c⁻¹ ^ D.rk * (Fᴴ * F).det.re`. Use `MCDet.re_det_mono hGPSD hup` as an intermediate fact.

Simplify using `only [RCLike.re_to_complex] at this`. Rewrite `this` using `[re_det_ofReal_smul]`. Then use the resulting hypothesis. Establish `hlow : ∀ l : ℝ, 0 < l → (l • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef → l⁻¹ ^ D.rk * (Fᴴ * F).det.re ≤ (Fᴴ * Yc * F).det.re`. Introduce `l hl hle`. Establish `h1` using `posSemidef_map_ofReal (inv_ge_of_le hl hYpd hle)`.

Rewrite `h1` using `[map_sub_smul_one]`. Establish `h2` using `h1.conjTranspose_mul_mul_same F`. Rewrite `h2` using `[conj_sub_smul_one]`. Establish `h3 : (((l⁻¹ : ℝ) : ℂ) • (Fᴴ * F)).PosSemidef` using `hHPSD.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hl.le))`. Use `MCDet.re_det_mono h3 h2` as an intermediate fact.

Simplify using `only [RCLike.re_to_complex] at this`. Rewrite `this` using `[re_det_ofReal_smul]`. Then use the resulting hypothesis. Establish `hδp` using `(hG p hp).1`. Establish `hMp` using `(hG p hp).2`. Establish `hl1 : 0 < C1 * r` using `by positivity`.

Establish `hdlow1` using `hlow (C1 * r) hl1 hYle1`. Establish `hdlowC` using `hlow (C * r) (by nlinarith) hYle`. Establish `hμpos : 0 < (C1 * r)⁻¹ ^ D.rk * δ` using `by positivity`. Establish `hμ : (C1 * r)⁻¹ ^ D.rk * δ ≤ (Fᴴ * Yc * F).det.re` using `le_trans (mul_le_mul_of_nonneg_left hδp (by positivity)) hdlow1`. Establish `hdpos : 0 < (Fᴴ * Yc * F).det.re` using `lt_of_lt_of_le hμpos hμ`.

Establish `hu : D.u p = Real.log (Fᴴ * Yc * F).det.re` using `rfl`. Use `⟨hYc, hYle, hdlowC, hdup, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hu]`. Establish `h1` using `Real.log_le_log hμpos hμ`. Rewrite `h1` using `[Real.log_mul (by positivity) hδ.ne', Real.log_pow, Real.log_inv, Real.log_mul hC1.ne' (by linarith)]`.

Establish `a1 : Real.log C1 ≤ |Real.log C1| * Real.log r` using `(le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog1)`. Establish `a2 : -Real.log δ ≤ |Real.log δ| * Real.log r` using `(neg_le_abs _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog1)`. Establish `hk : (0 : ℝ) ≤ D.rk` using `Nat.cast_nonneg _`. Establish `b1` using `mul_le_mul_of_nonneg_left a1 hk`. Establish `b2` using `mul_le_mul_of_nonneg_right hCC2 (by linarith : (0 : ℝ) ≤ Real.log r)`.

Rewrite `b2` using `[hC2]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hu]`. Establish `h1` using `Real.log_le_log hdpos (hdup.trans (mul_le_mul_of_nonneg_left hMp (pow_nonneg (inv_nonneg.mpr D.c_pos.le) _)))`. Conclude with `h1.trans ((le_abs_self _).trans hCC3)`.
-/
theorem ChartBounds.proof : ChartBounds.Statement := by
  intro D
  obtain ⟨C1, hC1, hY⟩ := exists_Y_le D
  obtain ⟨δ, M, hδ, hM, hG⟩ := exists_gram_bounds D
  set C2 : ℝ := (D.rk : ℝ) * (|Real.log C1| + 1) + |Real.log δ| with hC2
  set C3 : ℝ := |Real.log (D.c⁻¹ ^ D.rk * M)| with hC3
  have hCC1 : C1 ≤ max C1 (max C2 (max C3 1)) := le_max_left _ _
  have hCC2 : C2 ≤ max C1 (max C2 (max C3 1)) := (le_max_left _ _).trans (le_max_right _ _)
  have hCC3 : C3 ≤ max C1 (max C2 (max C3 1)) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  set C := max C1 (max C2 (max C3 1)) with hC
  refine ⟨C, by linarith, fun p hp hps => ?_⟩
  have hz : p.1 ∈ D.U := (D.K_subset hp).1
  have hr1 : 1 ≤ D.radius p.1 := one_le_radius D hz
  have hlog1 : 1 ≤ Real.log (D.radius p.1) := one_le_log_radius D hz
  set r := D.radius p.1 with hr
  have hYc : (D.Y p.1 - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)).PosSemidef := D.Y_ge p.1 hps
  have hYpd : (D.Y p.1).PosDef := posDef_of_ge D.c_pos hYc
  have hYle1 := hY p hp
  have hYle : ((C * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef := by
    have e : (C * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1 =
        ((C1 * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1) +
          ((C - C1) * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) := by
      rw [sub_mul, sub_smul]; abel
    rw [e]
    exact hYle1.add (PosSemidef.one.smul (by nlinarith))
  set F := D.f p with hF
  set Yc := (D.Y p.1)⁻¹.map (fun x : ℝ => (x : ℂ)) with hYcdef
  have hYcPSD : Yc.PosSemidef := posSemidef_map_ofReal hYpd.inv.posSemidef
  have hGPSD : (Fᴴ * Yc * F).PosSemidef := hYcPSD.conjTranspose_mul_mul_same F
  have hHPSD : (Fᴴ * F).PosSemidef := posSemidef_conjTranspose_mul_self F
  have hup : (((D.c⁻¹ : ℝ) : ℂ) • (Fᴴ * F) - Fᴴ * Yc * F).PosSemidef := by
    have h1 := posSemidef_map_ofReal (inv_le_of_ge D.c_pos hYc)
    rw [map_smul_one_sub] at h1
    have := h1.conjTranspose_mul_mul_same F
    rwa [conj_smul_one_sub] at this
  have hdup : (Fᴴ * Yc * F).det.re ≤ D.c⁻¹ ^ D.rk * (Fᴴ * F).det.re := by
    have := MCDet.re_det_mono hGPSD hup
    simp only [RCLike.re_to_complex] at this
    rwa [re_det_ofReal_smul] at this
  have hlow : ∀ l : ℝ, 0 < l → (l • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef →
      l⁻¹ ^ D.rk * (Fᴴ * F).det.re ≤ (Fᴴ * Yc * F).det.re := by
    intro l hl hle
    have h1 := posSemidef_map_ofReal (inv_ge_of_le hl hYpd hle)
    rw [map_sub_smul_one] at h1
    have h2 := h1.conjTranspose_mul_mul_same F
    rw [conj_sub_smul_one] at h2
    have h3 : (((l⁻¹ : ℝ) : ℂ) • (Fᴴ * F)).PosSemidef :=
      hHPSD.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hl.le))
    have := MCDet.re_det_mono h3 h2
    simp only [RCLike.re_to_complex] at this
    rwa [re_det_ofReal_smul] at this
  have hδp := (hG p hp).1
  have hMp := (hG p hp).2
  have hl1 : 0 < C1 * r := by positivity
  have hdlow1 := hlow (C1 * r) hl1 hYle1
  have hdlowC := hlow (C * r) (by nlinarith) hYle
  have hμpos : 0 < (C1 * r)⁻¹ ^ D.rk * δ := by positivity
  have hμ : (C1 * r)⁻¹ ^ D.rk * δ ≤ (Fᴴ * Yc * F).det.re :=
    le_trans (mul_le_mul_of_nonneg_left hδp (by positivity)) hdlow1
  have hdpos : 0 < (Fᴴ * Yc * F).det.re := lt_of_lt_of_le hμpos hμ
  have hu : D.u p = Real.log (Fᴴ * Yc * F).det.re := rfl
  refine ⟨hYc, hYle, hdlowC, hdup, ?_, ?_⟩
  · rw [hu]
    have h1 := Real.log_le_log hμpos hμ
    rw [Real.log_mul (by positivity) hδ.ne', Real.log_pow, Real.log_inv,
      Real.log_mul hC1.ne' (by linarith)] at h1
    have a1 : Real.log C1 ≤ |Real.log C1| * Real.log r :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog1)
    have a2 : -Real.log δ ≤ |Real.log δ| * Real.log r :=
      (neg_le_abs _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog1)
    have hk : (0 : ℝ) ≤ D.rk := Nat.cast_nonneg _
    have b1 := mul_le_mul_of_nonneg_left a1 hk
    have b2 := mul_le_mul_of_nonneg_right hCC2 (by linarith : (0 : ℝ) ≤ Real.log r)
    rw [hC2] at b2
    nlinarith
  · rw [hu]
    have h1 := Real.log_le_log hdpos (hdup.trans (mul_le_mul_of_nonneg_left hMp
      (pow_nonneg (inv_nonneg.mpr D.c_pos.le) _)))
    exact h1.trans ((le_abs_self _).trans hCC3)

end

end GroundTheory.Heights₂.Heights
