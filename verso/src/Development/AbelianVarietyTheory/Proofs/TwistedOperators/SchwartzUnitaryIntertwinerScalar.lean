import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

open scoped Matrix

noncomputable section

open MeasureTheory Complex
open scoped Real RealInnerProductSpace ComplexConjugate FourierTransform SchwartzMap

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

def modPt (q : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim 0 fun i => q i

def trPt (p : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim (fun i => p i) 0

/- English proof (translation)
Use extensionality with `i`. Simplify using `[pPart, modPt]`.
-/
theorem pPart_modPt (q : EuclideanSpace ℝ l) : pPart (modPt q) = 0 := by
  ext i; simp [pPart, modPt]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[qPart, modPt]`.
-/
theorem qPart_modPt (q : EuclideanSpace ℝ l) : qPart (modPt q) = q := by
  ext i; simp [qPart, modPt]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[pPart, trPt]`.
-/
theorem pPart_trPt (p : EuclideanSpace ℝ l) : pPart (trPt p) = p := by
  ext i; simp [pPart, trPt]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[qPart, trPt]`.
-/
theorem qPart_trPt (p : EuclideanSpace ℝ l) : qPart (trPt p) = 0 := by
  ext i; simp [qPart, trPt]

/- English proof (translation)
Simplify using `[rhoFun, phase, pPart_modPt, qPart_modPt]`.
-/
theorem rhoFun_modPt (q : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (modPt q) f x = cexp (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * I) * f x := by
  simp [rhoFun, phase, pPart_modPt, qPart_modPt]

/- English proof (translation)
Simplify using `[rhoFun, phase, pPart_trPt, qPart_trPt]`.
-/
theorem rhoFun_trPt (p : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (trPt p) f x = f (x + p) := by
  simp [rhoFun, phase, pPart_trPt, qPart_trPt]

def modS (q : EuclideanSpace ℝ l) (g : Sch l) : Sch l :=
  SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫) g

/- English proof (translation)
Establish `ht : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫` using `GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (innerSL ℝ q).hasTemperateGrowth`. Use function extensionality and compare the values at `x`. Rewrite using `[modS, SchwartzMap.smulLeftCLM_apply_apply ht, GlobalTheory.Published.Metaplectic.eChar_apply, rhoFun_modPt, smul_eq_mul]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coe_modS (q : EuclideanSpace ℝ l) (g : Sch l) : ⇑(modS q g) = rhoFun (modPt q) ⇑g := by
  have ht : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫ :=
    GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (innerSL ℝ q).hasTemperateGrowth
  funext x
  rw [modS, SchwartzMap.smulLeftCLM_apply_apply ht, GlobalTheory.Published.Metaplectic.eChar_apply, rhoFun_modPt, smul_eq_mul]
  congr 2
  push_cast
  ring

def trS (p : EuclideanSpace ℝ l) (g : Sch l) : Sch l := SchwartzMap.compSubConstCLM ℂ (-p) g

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[trS, SchwartzMap.compSubConstCLM_apply, rhoFun_trPt, sub_neg_eq_add]`.
-/
theorem coe_trS (p : EuclideanSpace ℝ l) (g : Sch l) : ⇑(trS p g) = rhoFun (trPt p) ⇑g := by
  funext x
  rw [trS, SchwartzMap.compSubConstCLM_apply, rhoFun_trPt, sub_neg_eq_add]

/- English proof (translation)
Use `b.integrable.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 a) (Complex.continuous_conj.comp a.continuous).aestronglyMeasurable (.of_forall fun x => ?_)` and prove the remaining obligations. Rewrite using `[Complex.norm_conj]`. Conclude with `SchwartzMap.norm_le_seminorm ℝ a x`.
-/
theorem integrable_conj_mul (a b : Sch l) : Integrable (fun x => conj (a x) * b x) := by
  refine b.integrable.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 a)
    (Complex.continuous_conj.comp a.continuous).aestronglyMeasurable (.of_forall fun x => ?_)
  rw [Complex.norm_conj]
  exact SchwartzMap.norm_le_seminorm ℝ a x

/- English proof (translation)
Establish `hn : ∀ h : Sch l, ‖(U h).toLp 2‖ = ‖h.toLp 2‖` using `fun h => by`. Rewrite using `[SchwartzMap.norm_toLp, SchwartzMap.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]`. Simplify using `only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hU]`. Establish `hlin : ∀ (b : ℂ) (u v : Sch l), u.toLp 2 volume + b • v.toLp 2 volume = (u + b • v).toLp 2 volume` using `fun b u v => by`. Use `(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_add u (b • v)` as an intermediate fact.

Rewrite `this` using `[(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_smul]`. Conclude with `this.symm`. Establish `key : ∀ b : ℂ, ‖(U f).toLp 2 + b • (U g).toLp 2‖ = ‖f.toLp 2 + b • g.toLp 2‖` using `fun b => by`. Rewrite using `[hlin, hlin, ← map_smul, ← map_add, hn]`. Establish `k1` using `key 1`.

Establish `k2` using `key (-1)`. Establish `k3` using `key (-(RCLike.I : ℂ))`. Establish `k4` using `key (RCLike.I : ℂ)`. Simplify using `only [one_smul, neg_one_smul, neg_smul, ← sub_eq_add_neg] at k1 k2 k3 k4`. Establish `e1` using `SchwartzMap.inner_toL2_toL2_eq (U f) (U g) volume`.

Establish `e2` using `SchwartzMap.inner_toL2_toL2_eq f g volume`. Simplify using `only [RCLike.inner_apply] at e1 e2`. Simplify using `only [mul_comm (starRingEnd ℂ _)]`. Rewrite using `[← e1, ← e2, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, k1, k2, k3, k4]`.
-/
theorem integral_conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) :
    ∫ x, conj (U f x) * U g x = ∫ x, conj (f x) * g x := by
  have hn : ∀ h : Sch l, ‖(U h).toLp 2‖ = ‖h.toLp 2‖ := fun h => by
    rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp,
      eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hU]
  have hlin : ∀ (b : ℂ) (u v : Sch l), u.toLp 2 volume + b • v.toLp 2 volume = (u + b • v).toLp 2 volume := fun b u v => by
    have := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_add u (b • v)
    rw [(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_smul] at this
    exact this.symm
  have key : ∀ b : ℂ, ‖(U f).toLp 2 + b • (U g).toLp 2‖ = ‖f.toLp 2 + b • g.toLp 2‖ := fun b => by
    rw [hlin, hlin, ← map_smul, ← map_add, hn]
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key (-(RCLike.I : ℂ))
  have k4 := key (RCLike.I : ℂ)
  simp only [one_smul, neg_one_smul, neg_smul, ← sub_eq_add_neg] at k1 k2 k3 k4
  have e1 := SchwartzMap.inner_toL2_toL2_eq (U f) (U g) volume
  have e2 := SchwartzMap.inner_toL2_toL2_eq f g volume
  simp only [RCLike.inner_apply] at e1 e2
  simp only [mul_comm (starRingEnd ℂ _)]
  rw [← e1, ← e2, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, k1, k2, k3, k4]

end GlobalTheory.RealWeil.SchurSchwartz

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

/- English proof (translation)
Use `set D : EuclideanSpace ℝ l → ℂ := fun y => conj (U f y) * U g y - conj (f y) * g y with hD`. Establish `hDi : Integrable D` using `(integrable_conj_mul (U f) (U g)).sub (integrable_conj_mul f g)`. Establish `hDc : Continuous D` using `((Complex.continuous_conj.comp (U f).continuous).mul (U g).continuous).sub ((Complex.continuous_conj.comp f.continuous).mul g.continuous)`. Establish `hF : 𝓕 D = 0`. Use function extensionality and compare the values at `w`.

Rewrite using `[Real.fourier_eq', Pi.zero_apply]`. Establish `h1` using `hc (modPt (-w)) g (modS (-w) g) (coe_modS _ _)`. Establish `h2` using `integral_conj_mul_eq U hU f (modS (-w) g)`. Rewrite `h2` using `[← sub_eq_zero, ← integral_sub (integrable_conj_mul _ _) (integrable_conj_mul _ _)]`. Rewrite using `[← h2]`.

Use `integral_congr_ae (.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [h1, coe_modS, rhoFun_modPt, hD, smul_eq_mul]`. Rewrite using `[inner_neg_left, real_inner_comm]`. Use `push_cast`. Put the polynomial expressions in normal form.

Establish `hinv` using `hDc.fourierInv_fourier_eq hDi (by rw [hF]; exact integrable_zero _ _ _)`. Establish `hz : 𝓕⁻ (0 : EuclideanSpace ℝ l → ℂ) = 0` using `by first`. Consider the case `exact FourierTransform.fourierInv_zero`. Consider the case `(funext w; simp [Real.fourierInv_eq])`. Rewrite `hinv` using `[hF, hz]`.

Establish `hx` using `congrFun hinv x`. Simplify using `only [hD, Pi.zero_apply] at hx`. Conclude with `sub_eq_zero.1 hx.symm`.
-/
theorem conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hc : ∀ (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h → ⇑(U h₁) = rhoFun w ⇑(U h))
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) (x : EuclideanSpace ℝ l) :
    conj (U f x) * U g x = conj (f x) * g x := by
  set D : EuclideanSpace ℝ l → ℂ := fun y => conj (U f y) * U g y - conj (f y) * g y with hD
  have hDi : Integrable D := (integrable_conj_mul (U f) (U g)).sub (integrable_conj_mul f g)
  have hDc : Continuous D :=
    ((Complex.continuous_conj.comp (U f).continuous).mul (U g).continuous).sub
      ((Complex.continuous_conj.comp f.continuous).mul g.continuous)
  have hF : 𝓕 D = 0 := by
    funext w
    rw [Real.fourier_eq', Pi.zero_apply]
    have h1 := hc (modPt (-w)) g (modS (-w) g) (coe_modS _ _)
    have h2 := integral_conj_mul_eq U hU f (modS (-w) g)
    rw [← sub_eq_zero, ← integral_sub (integrable_conj_mul _ _) (integrable_conj_mul _ _)] at h2
    rw [← h2]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [h1, coe_modS, rhoFun_modPt, hD, smul_eq_mul]
    rw [inner_neg_left, real_inner_comm]
    push_cast
    ring_nf
  have hinv := hDc.fourierInv_fourier_eq hDi (by rw [hF]; exact integrable_zero _ _ _)
  have hz : 𝓕⁻ (0 : EuclideanSpace ℝ l → ℂ) = 0 := by
    first
      | exact FourierTransform.fourierInv_zero
      | (funext w; simp [Real.fourierInv_eq])
  rw [hF, hz] at hinv
  have hx := congrFun hinv x
  simp only [hD, Pi.zero_apply] at hx
  exact sub_eq_zero.1 hx.symm

/- English proof (translation)
Introduce `_ l _ U hc hU`. Distinguish the cases in `h0 : ∃ (g : Sch l) (y : EuclideanSpace ℝ l), g y ≠ 0`. Take `⟨g, y0, hg⟩` from `h0`. Establish `hb` using `conj_mul_eq U hc hU g g y0`. Rewrite `hb` using `[Complex.conj_mul', Complex.conj_mul']`.

Establish `h2 : ‖U g y0‖ ^ 2 = ‖g y0‖ ^ 2` using `by exact_mod_cast hb`. Establish `hnb : ‖U g y0‖ = ‖g y0‖` using `by first`. Consider the case `exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2`. Consider the case `exact pow_left_injective₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero h2`. Consider the case `nlinarith [norm_nonneg (U g y0), norm_nonneg (g y0)]`.

Establish `hb0 : U g y0 ≠ 0`. Introduce `h`. Apply `hg` to reduce the goal to its premises. Rewrite using `[← norm_eq_zero, ← hnb, h, norm_zero]`. Establish `hcb : conj (U g y0) ≠ 0` using `(map_ne_zero _).2 hb0`.

Use `⟨conj (g y0 / U g y0), ?_, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.norm_conj, norm_div, hnb, div_self (norm_ne_zero_iff.2 hg)]`. Use extensionality with `x`. Establish `e1` using `conj_mul_eq U hc hU f (trS (y0 - x) g) x`. Establish `hxy : x + (y0 - x) = y0` using `by abel`.

Rewrite `e1` using `[hc (trPt (y0 - x)) g (trS (y0 - x) g) (coe_trS _ _), coe_trS, rhoFun_trPt, rhoFun_trPt, hxy]`. Establish `e2` using `congrArg conj e1`. Simplify using `only [map_mul, Complex.conj_conj] at e2`. Rewrite using `[SchwartzMap.smul_apply, smul_eq_mul, map_div₀, div_mul_eq_mul_div, eq_div_iff hcb, e2, mul_comm]`. Use `push_neg at h0`.

Use `⟨1, by simp, fun h => ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[h0 (U h) x, one_smul, h0 h x]`.
-/
theorem schur_schwartz : GlobalTheory.FunPr.Hypotheses₂ → ∀ (l : Type) [Fintype l] (U : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
    (∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(U h₁) = GlobalTheory.RealWeil.rhoFun w ⇑(U h)) →
    (∀ h : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, U h = a • h := by
  intro _ l _ U hc hU
  by_cases h0 : ∃ (g : Sch l) (y : EuclideanSpace ℝ l), g y ≠ 0
  · obtain ⟨g, y0, hg⟩ := h0
    have hb := conj_mul_eq U hc hU g g y0
    rw [Complex.conj_mul', Complex.conj_mul'] at hb
    have h2 : ‖U g y0‖ ^ 2 = ‖g y0‖ ^ 2 := by exact_mod_cast hb
    have hnb : ‖U g y0‖ = ‖g y0‖ := by
      first
        | exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
        | exact pow_left_injective₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero h2
        | nlinarith [norm_nonneg (U g y0), norm_nonneg (g y0)]
    have hb0 : U g y0 ≠ 0 := by
      intro h
      apply hg
      rw [← norm_eq_zero, ← hnb, h, norm_zero]
    have hcb : conj (U g y0) ≠ 0 := (map_ne_zero _).2 hb0
    refine ⟨conj (g y0 / U g y0), ?_, fun f => ?_⟩
    · rw [Complex.norm_conj, norm_div, hnb, div_self (norm_ne_zero_iff.2 hg)]
    · ext x
      have e1 := conj_mul_eq U hc hU f (trS (y0 - x) g) x
      have hxy : x + (y0 - x) = y0 := by abel
      rw [hc (trPt (y0 - x)) g (trS (y0 - x) g) (coe_trS _ _), coe_trS, rhoFun_trPt, rhoFun_trPt, hxy] at e1
      have e2 := congrArg conj e1
      simp only [map_mul, Complex.conj_conj] at e2
      rw [SchwartzMap.smul_apply, smul_eq_mul, map_div₀, div_mul_eq_mul_div, eq_div_iff hcb, e2, mul_comm]
  · push_neg at h0
    refine ⟨1, by simp, fun h => ?_⟩
    ext x
    rw [h0 (U h) x, one_smul, h0 h x]

end GlobalTheory.RealWeil.SchurSchwartz

end
