import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InfRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmB

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

/- English proof (translation)
Take `⟨U0, hU0o, hpos0, hΩ, hdiff, hfd⟩` from `psM_holo (μ := μ) T`. Use `⟨{z | ∃ x : Matrix (Fin n) (Fin n) ℂ, x.PosDef ∧ ∃ r : ℝ, 0 < r ∧ ‖z - x‖ < r ∧ (∀ w : Matrix (Fin n) (Fin n) ℂ, ‖w - x‖ < 3 * r → w ∈ U0) ∧ (∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → ‖H‖ < 3 * r → (x + H).PosDef)}, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Metric.isOpen_iff.mpr ?_` and prove the remaining obligations. Introduce and unpack `z ⟨x, hx, r, hr, hzx, hU, hP⟩`. Use `⟨r - ‖z - x‖, sub_pos.mpr hzx, fun z' hz' => ⟨x, hx, r, hr, ?_, hU, hP⟩⟩` and prove the remaining obligations.

Rewrite `hz'` using `[Metric.mem_ball, dist_eq_norm]`. Establish `h1 : z' - x = (z' - z) + (z - x)` using `by abel`. Rewrite using `[h1]`. Establish `h2` using `norm_add_le (z' - z) (z - x)`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `x hx`. Establish `hx' : x.PosDef` using `hx`. Take `⟨δ, hδ, hδP⟩` from `IdB.posDef_nhd hx'`. Take `⟨e, he, heU⟩` from `Metric.isOpen_iff.mp hU0o x (hpos0 hx)`. Establish `hm : 0 < min δ e / 3` using `div_pos (lt_min hδ he) (by norm_num)`.

Use `⟨x, hx', min δ e / 3, hm, by rw [sub_self, norm_zero]; exact hm, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Apply `heU` to reduce the goal to its premises. Rewrite using `[Metric.mem_ball, dist_eq_norm]`. Establish `: min δ e ≤ e` using `min_le_right δ e`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `H hH hHn`. Apply `hδP H hH` to reduce the goal to its premises. Establish `: min δ e ≤ δ` using `min_le_left δ e`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `hdiff.mono ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨x, hx, r, hr, hzx, hU, hP⟩` from `hz`. Conclude with `hU z (by linarith)`. Introduce and unpack `z ⟨x, hx, r, hr, hzx, hU, hP⟩ Y hY`.

Establish `hxH : xᴴ = x` using `hx.1.eq`. Establish `h12 : star (1 / 2 : ℂ) = 1 / 2`. Establish `h` using `Complex.conj_ofReal (1 / 2 : ℝ)`. Move the coercions through the operations in `at h`. Conclude with `h`.

Establish `hsI : star Complex.I = -Complex.I` using `Complex.conj_I`. Establish `hn12 : ‖(1 / 2 : ℂ)‖ = 1 / 2` using `by simp`. Take `⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ, A = (1 / 2 : ℂ) • (z + zᴴ)` from `⟨_, rfl⟩`. Take `⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, B = (1 / 2 : ℂ) • (Complex.I • (zᴴ - z))` from `⟨_, rfl⟩`. Establish `hAH : A.IsHermitian`.

Rewrite using `[Matrix.IsHermitian, hA]`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, star_mul', star_add, star_star, h12]`. Expand and normalize the polynomial expressions, which then agree. Establish `hBH : B.IsHermitian`.

Rewrite using `[Matrix.IsHermitian, hB]`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, star_mul', star_sub, star_star, h12, hsI]`. Expand and normalize the polynomial expressions, which then agree. Establish `hAB : A + Complex.I • B = z`.

Rewrite using `[hA, hB]`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, smul_eq_mul]`. Take the linear combination `((1 / 2 : ℂ) * (star (z j i) - z i j)) * Complex.I_sq`. Establish `hAx : A - x = (1 / 2 : ℂ) • ((z - x) + (z - x)ᴴ)`.

Rewrite using `[hA, Matrix.conjTranspose_sub, hxH]`. Use `module`. Establish `hBx : B = (1 / 2 : ℂ) • (Complex.I • ((z - x)ᴴ - (z - x)))`. Rewrite using `[hB, Matrix.conjTranspose_sub, hxH]`. Use `module`.

Establish `hAn : ‖A - x‖ ≤ ‖z - x‖`. Establish `h` using `norm_add_le (z - x) (z - x)ᴴ`. Rewrite `h` using `[Matrix.norm_conjTranspose]`. Rewrite using `[hAx, norm_smul, hn12]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hBn : ‖B‖ ≤ ‖z - x‖`. Establish `h` using `norm_sub_le (z - x)ᴴ (z - x)`. Rewrite `h` using `[Matrix.norm_conjTranspose]`. Rewrite using `[hBx, norm_smul, norm_smul, hn12, Complex.norm_I]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hbound : ∀ s : ℂ, ‖s‖ < 2 → ‖A + s • B - x‖ < 3 * r`. Introduce `s hs`. Establish `e1 : A + s • B - x = (A - x) + s • B` using `by abel`. Rewrite using `[e1]`. Establish `h1` using `norm_add_le (A - x) (s • B)`.

Rewrite `h1` using `[norm_smul]`. Establish `h2 : ‖s‖ * ‖B‖ ≤ 2 * ‖z - x‖` using `mul_le_mul hs.le hBn (norm_nonneg _) (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : ∀ s : ℂ, ‖s‖ < 2 → A + s • B ∈ U0` using `fun s hs => hU _ (hbound s hs)`. Establish `hposR : ∀ t : ℝ, |t| < 2 → (A + (t : ℂ) • B).PosDef`.

Introduce `t ht`. Establish `hs : ‖(t : ℂ)‖ < 2` using `by rwa [Complex.norm_real, Real.norm_eq_abs]`. Establish `hBt : ((t : ℂ) • B).IsHermitian`. Rewrite using `[Matrix.IsHermitian, Matrix.conjTranspose_smul, hBH.eq]`. Rewrite using `[show star (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t]`.

Establish `hH : (A + (t : ℂ) • B - x).IsHermitian` using `(hAH.add hBt).sub hx.1`. Use `hP _ hH (hbound _ hs)` as an intermediate fact. Simplify using `using this`. Establish `hI : ‖Complex.I‖ < 2` using `by rw [Complex.norm_I]; norm_num`. Prove the components needed by the constructor for the conclusion.

Set `g : ℂ → (T.V →L[ℂ] T.V)` to `fun s => ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) • (∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (A + s • B) * toMK k, toMK k⁻¹ * (A * Y + s • (B * Y)) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)) + T.dτ Y * psM T μ (A + s • B)`. Establish `hgeq : ∀ s : ℂ, A + s • B ∈ U0 → g s = fderiv ℂ (psM T μ) (A + s • B) ((A + s • B) * Y) + T.dτ Y * psM T μ (A + s • B)`. Introduce `s hs`. Rewrite using `[hfd _ hs]`. Apply the tactic sequence `simp only [g, add_mul, Matrix.smul_mul] <;> rfl`.

Establish `hgd : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s`. Introduce `s hs`. Establish `hw : DifferentiableAt ℂ (fun y : ℂ => A + y • B) s` using `(differentiableAt_const A).add (differentiableAt_id.smul_const B)`. Establish `hψ` using `(hdiff.differentiableAt (hU0o.mem_nhds (key s hs))).comp s hw`. Conclude with `((line_int_differentiableAt T μ hU0o hΩ A B (A * Y) (B * Y) (key s hs)).const_smul ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).add (hψ.const_mul (T.dτ Y))`.

Establish `hgr : ∀ t : ℝ, |t| < 2 → g t = 0`. Introduce `t ht`. Establish `hs : ‖(t : ℂ)‖ < 2` using `by rwa [Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[hgeq _ (key _ hs), (psM_inf_right T μ hμ (hposR t ht) hY).1]`. Simplify using the standard rewrite rules.

Establish `h0` using `IdB.line_zero g hgd hgr`. Rewrite `h0` using `[hgeq _ (key _ hI), hAB]`. Conclude with `eq_neg_of_add_eq_zero_left h0`. Set `g : ℂ → (T.V →L[ℂ] T.V)` to `fun s => ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) • (∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (A + s • B) * toMK k, toMK k⁻¹ * (Y * A + s • (Y * B)) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)) + psM T μ (A + s • B) * T.dτ Y`. Establish `hgeq : ∀ s : ℂ, A + s • B ∈ U0 → g s = fderiv ℂ (psM T μ) (A + s • B) (Y * (A + s • B)) + psM T μ (A + s • B) * T.dτ Y`.

Introduce `s hs`. Rewrite using `[hfd _ hs]`. Apply the tactic sequence `simp only [g, mul_add, Matrix.mul_smul] <;> rfl`. Establish `hgd : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s`. Introduce `s hs`.

Establish `hw : DifferentiableAt ℂ (fun y : ℂ => A + y • B) s` using `(differentiableAt_const A).add (differentiableAt_id.smul_const B)`. Establish `hψ` using `(hdiff.differentiableAt (hU0o.mem_nhds (key s hs))).comp s hw`. Conclude with `((line_int_differentiableAt T μ hU0o hΩ A B (Y * A) (Y * B) (key s hs)).const_smul ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).add (hψ.mul_const (T.dτ Y))`. Establish `hgr : ∀ t : ℝ, |t| < 2 → g t = 0`. Introduce `t ht`.

Establish `hs : ‖(t : ℂ)‖ < 2` using `by rwa [Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[hgeq _ (key _ hs), (psM_inf_right T μ hμ (hposR t ht) hY).2]`. Simplify using the standard rewrite rules. Establish `h0` using `IdB.line_zero g hgd hgr`. Rewrite `h0` using `[hgeq _ (key _ hI), hAB]`.

Conclude with `eq_neg_of_add_eq_zero_left h0`.
-/
theorem psM_inf_nhd (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      ∀ z ∈ U, ∀ Y : Matrix (Fin n) (Fin n) ℂ, IsBlock ε Y →
        fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z) ∧
          fderiv ℂ (psM T μ) z (Y * z) = -(psM T μ z * T.dτ Y) := by
  obtain ⟨U0, hU0o, hpos0, hΩ, hdiff, hfd⟩ := psM_holo (μ := μ) T
  refine ⟨{z | ∃ x : Matrix (Fin n) (Fin n) ℂ, x.PosDef ∧ ∃ r : ℝ, 0 < r ∧ ‖z - x‖ < r ∧
      (∀ w : Matrix (Fin n) (Fin n) ℂ, ‖w - x‖ < 3 * r → w ∈ U0) ∧
      (∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → ‖H‖ < 3 * r → (x + H).PosDef)},
      ?_, ?_, ?_, ?_⟩
  · refine Metric.isOpen_iff.mpr ?_
    rintro z ⟨x, hx, r, hr, hzx, hU, hP⟩
    refine ⟨r - ‖z - x‖, sub_pos.mpr hzx, fun z' hz' => ⟨x, hx, r, hr, ?_, hU, hP⟩⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz'
    have h1 : z' - x = (z' - z) + (z - x) := by abel
    rw [h1]
    have h2 := norm_add_le (z' - z) (z - x)
    linarith
  · intro x hx
    have hx' : x.PosDef := hx
    obtain ⟨δ, hδ, hδP⟩ := IdB.posDef_nhd hx'
    obtain ⟨e, he, heU⟩ := Metric.isOpen_iff.mp hU0o x (hpos0 hx)
    have hm : 0 < min δ e / 3 := div_pos (lt_min hδ he) (by norm_num)
    refine ⟨x, hx', min δ e / 3, hm, by rw [sub_self, norm_zero]; exact hm, ?_, ?_⟩
    · intro w hw
      apply heU
      rw [Metric.mem_ball, dist_eq_norm]
      have : min δ e ≤ e := min_le_right δ e
      linarith
    · intro H hH hHn
      apply hδP H hH
      have : min δ e ≤ δ := min_le_left δ e
      linarith
  · refine hdiff.mono ?_
    intro z hz
    obtain ⟨x, hx, r, hr, hzx, hU, hP⟩ := hz
    exact hU z (by linarith)
  · rintro z ⟨x, hx, r, hr, hzx, hU, hP⟩ Y hY
    have hxH : xᴴ = x := hx.1.eq
    have h12 : star (1 / 2 : ℂ) = 1 / 2 := by
      have h := Complex.conj_ofReal (1 / 2 : ℝ)
      push_cast at h
      exact h
    have hsI : star Complex.I = -Complex.I := Complex.conj_I
    have hn12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ, A = (1 / 2 : ℂ) • (z + zᴴ) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ,
        B = (1 / 2 : ℂ) • (Complex.I • (zᴴ - z)) := ⟨_, rfl⟩
    have hAH : A.IsHermitian := by
      rw [Matrix.IsHermitian, hA]
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
        star_mul', star_add, star_star, h12]
      ring
    have hBH : B.IsHermitian := by
      rw [Matrix.IsHermitian, hB]
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        star_mul', star_sub, star_star, h12, hsI]
      ring
    have hAB : A + Complex.I • B = z := by
      rw [hA, hB]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
        smul_eq_mul]
      linear_combination ((1 / 2 : ℂ) * (star (z j i) - z i j)) * Complex.I_sq
    have hAx : A - x = (1 / 2 : ℂ) • ((z - x) + (z - x)ᴴ) := by
      rw [hA, Matrix.conjTranspose_sub, hxH]; module
    have hBx : B = (1 / 2 : ℂ) • (Complex.I • ((z - x)ᴴ - (z - x))) := by
      rw [hB, Matrix.conjTranspose_sub, hxH]; module
    have hAn : ‖A - x‖ ≤ ‖z - x‖ := by
      have h := norm_add_le (z - x) (z - x)ᴴ
      rw [Matrix.norm_conjTranspose] at h
      rw [hAx, norm_smul, hn12]
      linarith
    have hBn : ‖B‖ ≤ ‖z - x‖ := by
      have h := norm_sub_le (z - x)ᴴ (z - x)
      rw [Matrix.norm_conjTranspose] at h
      rw [hBx, norm_smul, norm_smul, hn12, Complex.norm_I]
      linarith
    have hbound : ∀ s : ℂ, ‖s‖ < 2 → ‖A + s • B - x‖ < 3 * r := by
      intro s hs
      have e1 : A + s • B - x = (A - x) + s • B := by abel
      rw [e1]
      have h1 := norm_add_le (A - x) (s • B)
      rw [norm_smul] at h1
      have h2 : ‖s‖ * ‖B‖ ≤ 2 * ‖z - x‖ := mul_le_mul hs.le hBn (norm_nonneg _) (by norm_num)
      linarith
    have key : ∀ s : ℂ, ‖s‖ < 2 → A + s • B ∈ U0 := fun s hs => hU _ (hbound s hs)
    have hposR : ∀ t : ℝ, |t| < 2 → (A + (t : ℂ) • B).PosDef := by
      intro t ht
      have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
      have hBt : ((t : ℂ) • B).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hBH.eq]
        rw [show star (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t]
      have hH : (A + (t : ℂ) • B - x).IsHermitian := (hAH.add hBt).sub hx.1
      have := hP _ hH (hbound _ hs)
      simpa using this
    have hI : ‖Complex.I‖ < 2 := by rw [Complex.norm_I]; norm_num
    constructor
    · let g : ℂ → (T.V →L[ℂ] T.V) := fun s =>
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          (∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (A + s • B) * toMK k,
            toMK k⁻¹ * (A * Y + s • (B * Y)) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
          + T.dτ Y * psM T μ (A + s • B)
      have hgeq : ∀ s : ℂ, A + s • B ∈ U0 →
          g s = fderiv ℂ (psM T μ) (A + s • B) ((A + s • B) * Y) + T.dτ Y * psM T μ (A + s • B) := by
        intro s hs
        rw [hfd _ hs]
        simp only [g, add_mul, Matrix.smul_mul] <;> rfl
      have hgd : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s := by
        intro s hs
        have hw : DifferentiableAt ℂ (fun y : ℂ => A + y • B) s :=
          (differentiableAt_const A).add (differentiableAt_id.smul_const B)
        have hψ := (hdiff.differentiableAt (hU0o.mem_nhds (key s hs))).comp s hw
        exact ((line_int_differentiableAt T μ hU0o hΩ A B (A * Y) (B * Y) (key s hs)).const_smul
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).add (hψ.const_mul (T.dτ Y))
      have hgr : ∀ t : ℝ, |t| < 2 → g t = 0 := by
        intro t ht
        have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
        rw [hgeq _ (key _ hs), (psM_inf_right T μ hμ (hposR t ht) hY).1]
        simp
      have h0 := IdB.line_zero g hgd hgr
      rw [hgeq _ (key _ hI), hAB] at h0
      exact eq_neg_of_add_eq_zero_left h0
    · let g : ℂ → (T.V →L[ℂ] T.V) := fun s =>
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          (∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (A + s • B) * toMK k,
            toMK k⁻¹ * (Y * A + s • (Y * B)) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
          + psM T μ (A + s • B) * T.dτ Y
      have hgeq : ∀ s : ℂ, A + s • B ∈ U0 →
          g s = fderiv ℂ (psM T μ) (A + s • B) (Y * (A + s • B)) + psM T μ (A + s • B) * T.dτ Y := by
        intro s hs
        rw [hfd _ hs]
        simp only [g, mul_add, Matrix.mul_smul] <;> rfl
      have hgd : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s := by
        intro s hs
        have hw : DifferentiableAt ℂ (fun y : ℂ => A + y • B) s :=
          (differentiableAt_const A).add (differentiableAt_id.smul_const B)
        have hψ := (hdiff.differentiableAt (hU0o.mem_nhds (key s hs))).comp s hw
        exact ((line_int_differentiableAt T μ hU0o hΩ A B (Y * A) (Y * B) (key s hs)).const_smul
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).add (hψ.mul_const (T.dτ Y))
      have hgr : ∀ t : ℝ, |t| < 2 → g t = 0 := by
        intro t ht
        have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
        rw [hgeq _ (key _ hs), (psM_inf_right T μ hμ (hposR t ht) hY).2]
        simp
      have h0 := IdB.line_zero g hgd hgr
      rw [hgeq _ (key _ hI), hAB] at h0
      exact eq_neg_of_add_eq_zero_left h0

end ReciprocityTheory.ChartRestriction.DS.S7
