import Formalism.HermitianCurvature.StatementKB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces

open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBB.K8

noncomputable section

def dw (c : ℂ) : ℝ := ((1 + ‖c‖) ^ 3)⁻¹

/- English proof (translation)
The claim follows from `((continuous_const.add continuous_norm).pow 3).inv₀ fun c => pow_ne_zero _ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg c)).ne'`.
-/
theorem dw_cont : Continuous dw :=
  ((continuous_const.add continuous_norm).pow 3).inv₀ fun c => pow_ne_zero _ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg c)).ne'

/- English proof (translation)
Unfold `dw`. Check the signs of the components of the expression.
-/
theorem dw_nonneg (c : ℂ) : 0 ≤ dw c := by unfold dw; positivity

/- English proof (translation)
Establish `hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ)))` using `integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)`. Use `hi.congr (Eventually.of_forall fun c => ?_)` and prove the remaining obligations. Use `show (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹`. Rewrite using `[Real.rpow_neg (by positivity)]`. Use `norm_cast`.
-/
theorem dw_integrable : Integrable dw := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  show (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast

/- English proof (translation)
Establish `hs : IsClosed {c : ℂ | ‖f c‖ ≤ C * dw c}` using `isClosed_le (continuous_norm.comp hf) (continuous_const.mul dw_cont)`. Establish `hsub : ({0}ᶜ : Set ℂ) ⊆ {c | ‖f c‖ ≤ C * dw c}` using `fun c hc => h c hc`. Use `hs.closure_subset_iff.mpr hsub` as an intermediate fact. Rewrite `this` using `[(dense_compl_singleton (0 : ℂ)).closure_eq]`. Conclude with `this (Set.mem_univ c)`.
-/
theorem bound_all {f : ℂ → ℂ} (hf : Continuous f) {C : ℝ} (h : ∀ c, c ≠ 0 → ‖f c‖ ≤ C * dw c) (c : ℂ) :
    ‖f c‖ ≤ C * dw c := by
  have hs : IsClosed {c : ℂ | ‖f c‖ ≤ C * dw c} :=
    isClosed_le (continuous_norm.comp hf) (continuous_const.mul dw_cont)
  have hsub : ({0}ᶜ : Set ℂ) ⊆ {c | ‖f c‖ ≤ C * dw c} := fun c hc => h c hc
  have := hs.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at this
  exact this (Set.mem_univ c)

/- English proof (translation)
The claim follows from `VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf`.
-/
theorem fourier_cont {f : ℂ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

/- English proof (translation)
Simplify using `[ae_iff]`.
-/
theorem ae_ne_zero : ∀ᵐ c : ℂ ∂volume, c ≠ 0 := by
  simp [ae_iff]

/- English proof (translation)
Establish `hφb : ∀ n c, ‖φ n c‖ ≤ C * dw c` using `fun n => bound_all (hφc n) fun c hc => by rw [hφg n c hc]; exact hb n c hc`. Establish `hBi : Integrable (fun c => C * dw c)` using `dw_integrable.const_mul C`. Establish `hB'i : Integrable (fun c => C' * dw c)` using `dw_integrable.const_mul C'`. Establish `hφi : ∀ n, Integrable (φ n)` using `fun n => hBi.mono' (hφc n).aestronglyMeasurable (Eventually.of_forall (hφb n))`. Establish `hFt : ∀ w, Tendsto (fun n => 𝓕 (φ n) w) atTop (𝓝 (𝓕 g0 w))`.

Introduce `w`. Use `show Tendsto (fun n => ∫ v, 𝐞 (-⟪v, w⟫) • φ n v) atTop (𝓝 (∫ v, 𝐞 (-⟪v, w⟫) • g0 v))`. Use `tendsto_integral_of_dominated_convergence (fun c => C * dw c) (fun n => ?_) hBi (fun n => ?_) ?_` and prove the remaining obligations. Conclude with `((Real.fourierIntegral_convergent_iff w).mpr (hφi n)).aestronglyMeasurable`. Conclude with `Eventually.of_forall fun c => by rw [Circle.norm_smul]; exact hφb n c`.

Use `filter_upwards [ae_ne_zero] with c hc`. Simplify using `only [hφg _ c hc]`. Conclude with `(hconv c).const_smul _`. Establish `hGm : AEStronglyMeasurable (𝓕 g0) volume` using `aestronglyMeasurable_of_tendsto_ae atTop (fun n => (fourier_cont (hφi n)).aestronglyMeasurable) (ae_of_all _ hFt)`. Establish `hGb : ∀ w, ‖𝓕 g0 w‖ ≤ C' * dw w` using `fun w => le_of_tendsto' (hFt w).norm fun n => hT n w`.

Establish `hGi : Integrable (𝓕 g0)` using `hB'i.mono' hGm (Eventually.of_forall hGb)`. Establish `hinv : ∀ n, 𝓕⁻ (𝓕 (φ n)) = φ n` using `fun n => (hφc n).fourierInv_fourier_eq (hφi n) (hB'i.mono' (fourier_cont (hφi n)).aestronglyMeasurable (Eventually.of_forall (hT n)))`. Use `set ψ : ℂ → ℂ := 𝓕⁻ (𝓕 g0) with hψ`. Establish `hψlim : ∀ c, Tendsto (fun n => φ n c) atTop (𝓝 (ψ c))`. Introduce `c`.

Establish `: (fun n => φ n c) = fun n => 𝓕⁻ (𝓕 (φ n)) c` using `funext fun n => by rw [hinv n]`. Rewrite using `[this, hψ]`. Simplify using `only [Real.fourierInv_eq]`. Use `tendsto_integral_of_dominated_convergence (fun w => C' * dw w) (fun n => ?_) hB'i (fun n => ?_) ?_` and prove the remaining obligations. Conclude with `((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul (fourier_cont (hφi n))).aestronglyMeasurable`.

Conclude with `Eventually.of_forall fun w => by rw [Circle.norm_smul]; exact hT n w`. Conclude with `ae_of_all _ fun w => (hFt w).const_smul _`. Use `⟨ψ, ?_, fun c hc => ?_, fun c => le_of_tendsto' (hψlim c).norm fun n => hφb n c, ?_⟩` and prove the remaining obligations. Establish `: ψ = fun c => 𝓕 (𝓕 g0) (-c)` using `funext fun c => Real.fourierInv_eq_fourier_neg _ c`. Rewrite using `[this]`.

Conclude with `(fourier_cont hGi).comp continuous_neg`. Use `tendsto_nhds_unique (hψlim c) ?_` and prove the remaining obligations. Establish `: (fun n => φ n c) = fun n => g n c` using `funext fun n => hφg n c hc`. Rewrite using `[this]`. Conclude with `hconv c`.

Conclude with `tendsto_integral_of_dominated_convergence (fun c => C * dw c) (fun n => (hφc n).aestronglyMeasurable) hBi (fun n => ae_of_all _ (hφb n)) (ae_of_all _ hψlim)`.
-/
theorem limit_fourier (g : ℕ → ℂ → ℂ) (g0 : ℂ → ℂ) (φ : ℕ → ℂ → ℂ) (C C' : ℝ)
    (hφc : ∀ n, Continuous (φ n)) (hφg : ∀ n c, c ≠ 0 → φ n c = g n c)
    (hconv : ∀ c, Tendsto (fun n => g n c) atTop (𝓝 (g0 c)))
    (hb : ∀ n c, c ≠ 0 → ‖g n c‖ ≤ C * dw c)
    (hT : ∀ n w, ‖𝓕 (φ n) w‖ ≤ C' * dw w) :
    ∃ ψ : ℂ → ℂ, Continuous ψ ∧ (∀ c, c ≠ 0 → ψ c = g0 c) ∧ (∀ c, ‖ψ c‖ ≤ C * dw c) ∧
      Tendsto (fun n => ∫ c, φ n c) atTop (𝓝 (∫ c, ψ c)) := by
  have hφb : ∀ n c, ‖φ n c‖ ≤ C * dw c := fun n =>
    bound_all (hφc n) fun c hc => by rw [hφg n c hc]; exact hb n c hc
  have hBi : Integrable (fun c => C * dw c) := dw_integrable.const_mul C
  have hB'i : Integrable (fun c => C' * dw c) := dw_integrable.const_mul C'
  have hφi : ∀ n, Integrable (φ n) := fun n =>
    hBi.mono' (hφc n).aestronglyMeasurable (Eventually.of_forall (hφb n))
  have hFt : ∀ w, Tendsto (fun n => 𝓕 (φ n) w) atTop (𝓝 (𝓕 g0 w)) := by
    intro w
    show Tendsto (fun n => ∫ v, 𝐞 (-⟪v, w⟫) • φ n v) atTop (𝓝 (∫ v, 𝐞 (-⟪v, w⟫) • g0 v))
    refine tendsto_integral_of_dominated_convergence (fun c => C * dw c) (fun n => ?_) hBi (fun n => ?_) ?_
    · exact ((Real.fourierIntegral_convergent_iff w).mpr (hφi n)).aestronglyMeasurable
    · exact Eventually.of_forall fun c => by rw [Circle.norm_smul]; exact hφb n c
    · filter_upwards [ae_ne_zero] with c hc
      simp only [hφg _ c hc]
      exact (hconv c).const_smul _
  have hGm : AEStronglyMeasurable (𝓕 g0) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (fourier_cont (hφi n)).aestronglyMeasurable)
      (ae_of_all _ hFt)
  have hGb : ∀ w, ‖𝓕 g0 w‖ ≤ C' * dw w := fun w => le_of_tendsto' (hFt w).norm fun n => hT n w
  have hGi : Integrable (𝓕 g0) := hB'i.mono' hGm (Eventually.of_forall hGb)
  have hinv : ∀ n, 𝓕⁻ (𝓕 (φ n)) = φ n := fun n =>
    (hφc n).fourierInv_fourier_eq (hφi n)
      (hB'i.mono' (fourier_cont (hφi n)).aestronglyMeasurable (Eventually.of_forall (hT n)))
  set ψ : ℂ → ℂ := 𝓕⁻ (𝓕 g0) with hψ
  have hψlim : ∀ c, Tendsto (fun n => φ n c) atTop (𝓝 (ψ c)) := by
    intro c
    have : (fun n => φ n c) = fun n => 𝓕⁻ (𝓕 (φ n)) c := funext fun n => by rw [hinv n]
    rw [this, hψ]
    simp only [Real.fourierInv_eq]
    refine tendsto_integral_of_dominated_convergence (fun w => C' * dw w) (fun n => ?_) hB'i (fun n => ?_) ?_
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        (fourier_cont (hφi n))).aestronglyMeasurable
    · exact Eventually.of_forall fun w => by rw [Circle.norm_smul]; exact hT n w
    · exact ae_of_all _ fun w => (hFt w).const_smul _
  refine ⟨ψ, ?_, fun c hc => ?_, fun c => le_of_tendsto' (hψlim c).norm fun n => hφb n c, ?_⟩
  · have : ψ = fun c => 𝓕 (𝓕 g0) (-c) := funext fun c => Real.fourierInv_eq_fourier_neg _ c
    rw [this]
    exact (fourier_cont hGi).comp continuous_neg
  · refine tendsto_nhds_unique (hψlim c) ?_
    have : (fun n => φ n c) = fun n => g n c := funext fun n => hφg n c hc
    rw [this]
    exact hconv c
  · exact tendsto_integral_of_dominated_convergence (fun c => C * dw c)
      (fun n => (hφc n).aestronglyMeasurable) hBi (fun n => ae_of_all _ (hφb n)) (ae_of_all _ hψlim)

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def Lm (g : ℕ) (l : ℂ) : ℂ := -(((2 / (g : ℝ) : ℝ)) : ℂ) * conj l

/- English proof (translation)
Rewrite using `[Circle.smul_def, Real.fourierChar_apply, KB.psiL, mul_comm z]`. Use `congr 2`. Establish `hi : ⟪c, Lm S.g l⟫ = -(2 / (S.g : ℝ)) * (l * c).re`. Simplify using `[Lm, Complex.inner, Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hi]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psiL_eq (S : C.HidaSetting E Wp Wq) (l c z : ℂ) :
    z * KB.psiL S l c = 𝐞 (-⟪c, Lm S.g l⟫) • z := by
  rw [Circle.smul_def, Real.fourierChar_apply, KB.psiL, mul_comm z]
  congr 2
  have hi : ⟪c, Lm S.g l⟫ = -(2 / (S.g : ℝ)) * (l * c).re := by
    simp [Lm, Complex.inner, Complex.mul_re]
    ring
  rw [hi]
  push_cast
  ring

/- English proof (translation)
Simplify using `only [Lm, map_mul, Complex.conj_ofReal, Complex.conj_conj]`. Rewrite using `[← mul_assoc, ← Complex.ofReal_neg, ← Complex.ofReal_mul]`. Establish `: (-(2 / (g : ℝ)) * (-(g : ℝ) / 2)) = 1` using `by field_simp`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem Lm_inv (g : ℕ) (hg : (g : ℝ) ≠ 0) (w : ℂ) : Lm g ((((-(g : ℝ) / 2 : ℝ)) : ℂ) * conj w) = w := by
  simp only [Lm, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  rw [← mul_assoc, ← Complex.ofReal_neg, ← Complex.ofReal_mul]
  have : (-(2 / (g : ℝ)) * (-(g : ℝ) / 2)) = 1 := by field_simp
  rw [this]
  simp

/- English proof (translation)
Establish `hn : ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖ = g / 2 * ‖w‖`. Rewrite using `[norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by linarith : (0:ℝ) < g)]`. Evaluate the numerical expressions. Rewrite using `[hn]`. Establish `h0 : 0 < (1 + ‖w‖) / 2` using `by positivity`.

Establish `h1 : (1 + ‖w‖) / 2 ≤ 1 + g / 2 * ‖w‖` using `by nlinarith [norm_nonneg w]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decay_scale (g : ℝ) (hg : 1 ≤ g) (w : ℂ) :
    ((1 + ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖) ^ 3)⁻¹ ≤ 8 * dw w := by
  have hn : ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖ = g / 2 * ‖w‖ := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (by linarith : (0:ℝ) < g)]
    norm_num
  rw [hn]
  have h0 : 0 < (1 + ‖w‖) / 2 := by positivity
  have h1 : (1 + ‖w‖) / 2 ≤ 1 + g / 2 * ‖w‖ := by nlinarith [norm_nonneg w]
  calc ((1 + g / 2 * ‖w‖) ^ 3)⁻¹ ≤ (((1 + ‖w‖) / 2) ^ 3)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le h1 3)
    _ = 8 * dw w := by unfold dw; field_simp; ring

/- English proof (translation)
Establish `: 1 ≤ S.g` using `Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hg1.ne' hg2.ne')`. Conclude with `this` after adjusting the coercions.
-/
theorem g_ge_one (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : (1 : ℝ) ≤ S.g := by
  have : 1 ≤ S.g := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hg1.ne' hg2.ne')
  exact_mod_cast this

/- English proof (translation)
The claim follows from `(hconv v ε hε i _ ⟨w, rfl⟩ p q).const_mul _`.
-/
theorem gramLoc_tendsto (S : C.HidaSetting E Wp Wq)
    (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    (v : Fin S.f) {ε : ℝ} (hε : 0 < ε) (i : ℕ) (w : S.W) (p q : C.LPt) :
    Tendsto (fun n => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) p q) atTop
      (𝓝 (S.gramLoc v ε i (w.1 v) p q)) :=
  (hconv v ε hε i _ ⟨w, rfl⟩ p q).const_mul _

/- English proof (translation)
Introduce `v ε hε i hi1 hi2 w h h' hh hh'`. Take `⟨C, hC⟩` from `hB v ε hε i hi1 hi2 (w.1 v) ⟨w, rfl⟩ h h' hh hh'`. Establish `hC0 : 0 ≤ C`. Use `((hC 0).2 0).trans' (norm_nonneg _)` as an intermediate fact. Simplify using `using this`.

Establish `H` using `fun n => hInt n v ε hε i hi1 hi2 w h h' hh hh'`. Use `choose φ hφc hφe hφb hφi using H`. Establish `hg` using `g_ge_one S hg1 hg2`. Establish `hT : ∀ n w', ‖𝓕 (φ n) w'‖ ≤ 8 * C * dw w'`. Introduce `n w'`.

Use `set l : ℂ := (((-(S.g : ℝ) / 2 : ℝ)) : ℂ) * conj w' with hl`. Establish `hLm : Lm S.g l = w'` using `Lm_inv S.g (by linarith) w'`. Establish `he : 𝓕 (φ n) w' = ∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S l c`. Rewrite using `[Real.fourier_eq]`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [ae_ne_zero] with c hc`. Rewrite using `[psiL_eq, hLm, hφe n c hc]`. Rewrite using `[he]`. Establish `h8` using `mul_le_mul_of_nonneg_left (decay_scale S.g hg w') hC0`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨ψ, hψc, hψe, hψb, hψi⟩` from `limit_fourier (fun n c => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) (fun c => S.gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) φ C (8 * C) hφc hφe (fun c => gramLoc_tendsto S RR hconv v hε i w _ _) (fun n c hc => (hC n).1 c hc) hT`. Use `⟨ψ, hψc, hψe, ⟨C, hψb⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : Tendsto (fun n => ∫ c, φ n c) atTop (𝓝 (((KB.dlB S i 1 : ℝ) : ℂ) * S.gramLoc v ε (i - 1) (w.1 v) h h'))`. Establish `: (fun n => ∫ c, φ n c) = fun n => ((KB.dlB S i 1 : ℝ) : ℂ) * (KB.withRR S (RR n)).gramLoc v ε (i - 1) (w.1 v) h h'`. Use function extensionality and compare the values at `fun n => hφi n`.

Rewrite using `[this]`. Conclude with `(gramLoc_tendsto S RR hconv v hε (i - 1) w h h').const_mul _`. Conclude with `tendsto_nhds_unique hψi h1`.
-/
theorem intAll_limit (S : C.HidaSetting E Wp Wq)
    (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2)
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    (hInt : ∀ n, KB.IntAll (KB.withRR S (RR n)))
    (hB : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 →
      D.ptSize h' = i - 1 →
      ∃ C : ℝ, ∀ n, (∀ c : ℂ, c ≠ 0 →
          ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
        ∀ l : ℂ, ‖∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S l c‖ ≤
          C * ((1 + ‖l‖) ^ 3)⁻¹) :
    KB.IntAll S := by
  intro v ε hε i hi1 hi2 w h h' hh hh'
  obtain ⟨C, hC⟩ := hB v ε hε i hi1 hi2 (w.1 v) ⟨w, rfl⟩ h h' hh hh'
  have hC0 : 0 ≤ C := by
    have := ((hC 0).2 0).trans' (norm_nonneg _)
    simpa using this
  have H := fun n => hInt n v ε hε i hi1 hi2 w h h' hh hh'
  choose φ hφc hφe hφb hφi using H
  have hg := g_ge_one S hg1 hg2
  have hT : ∀ n w', ‖𝓕 (φ n) w'‖ ≤ 8 * C * dw w' := by
    intro n w'
    set l : ℂ := (((-(S.g : ℝ) / 2 : ℝ)) : ℂ) * conj w' with hl
    have hLm : Lm S.g l = w' := Lm_inv S.g (by linarith) w'
    have he : 𝓕 (φ n) w' = ∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) *
        KB.psiL S l c := by
      rw [Real.fourier_eq]
      refine integral_congr_ae ?_
      filter_upwards [ae_ne_zero] with c hc
      rw [psiL_eq, hLm, hφe n c hc]
    rw [he]
    have h8 := mul_le_mul_of_nonneg_left (decay_scale S.g hg w') hC0
    calc _ ≤ C * ((1 + ‖l‖) ^ 3)⁻¹ := (hC n).2 l
      _ ≤ C * (8 * dw w') := h8
      _ = 8 * C * dw w' := by ring
  obtain ⟨ψ, hψc, hψe, hψb, hψi⟩ := limit_fourier
    (fun n c => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]))
    (fun c => S.gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) φ C (8 * C) hφc hφe
    (fun c => gramLoc_tendsto S RR hconv v hε i w _ _) (fun n c hc => (hC n).1 c hc) hT
  refine ⟨ψ, hψc, hψe, ⟨C, hψb⟩, ?_⟩
  have h1 : Tendsto (fun n => ∫ c, φ n c) atTop
      (𝓝 (((KB.dlB S i 1 : ℝ) : ℂ) * S.gramLoc v ε (i - 1) (w.1 v) h h')) := by
    have : (fun n => ∫ c, φ n c) =
        fun n => ((KB.dlB S i 1 : ℝ) : ℂ) * (KB.withRR S (RR n)).gramLoc v ε (i - 1) (w.1 v) h h' :=
      funext fun n => hφi n
    rw [this]
    exact (gramLoc_tendsto S RR hconv v hε (i - 1) w h h').const_mul _
  exact tendsto_nhds_unique hψi h1

end setting

end

end Formalism.FourierDecayAlt.P.PBB.K8
