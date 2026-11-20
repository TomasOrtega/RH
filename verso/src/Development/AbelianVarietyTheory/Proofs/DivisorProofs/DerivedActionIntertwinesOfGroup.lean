import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Complex SchwartzMap
open scoped Real RealInnerProductSpace Topology

namespace GlobalTheory.RealWeil.DRhoTransfer

variable {l : Type} [Fintype l]

/- English proof (translation)
Use `⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h, by positivity, fun y => ?_⟩` and prove the remaining obligations. Use `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (le_refl N) (le_refl 0) h y` as an intermediate fact. Simplify `this` using `[norm_iteratedFDeriv_zero]`.
-/
theorem exists_decay (h : Sch l) (N : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, (1 + ‖y‖) ^ N * ‖h y‖ ≤ M := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h, by positivity, fun y => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (le_refl N) (le_refl 0) h y
  simpa [norm_iteratedFDeriv_zero] using this

/- English proof (translation)
Take `⟨M, hM, hb⟩` from `exists_decay h N`. Use `⟨M * (1 + ‖p‖) ^ N, by positivity, fun s hs x => ?_⟩` and prove the remaining obligations. Establish `h1 : 1 + ‖x‖ ≤ (1 + ‖x + s • p‖) * (1 + ‖p‖)`. Establish `h0 : ‖x‖ ≤ ‖x + s • p‖ + ‖s • p‖`. Use `norm_sub_le (x + s • p) (s • p)` as an intermediate fact.

Simplify using `using this`. Establish `h2 : ‖s • p‖ ≤ ‖p‖`. Rewrite using `[norm_smul, Real.norm_eq_abs]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) hs`. Use polynomial arithmetic with `[norm_nonneg (x + s • p), norm_nonneg p]`.

Establish `h3 : (1 + ‖x‖) ^ N ≤ (1 + ‖x + s • p‖) ^ N * (1 + ‖p‖) ^ N`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) h1 N`. Establish `hpos : 0 < (1 + ‖x‖) ^ N` using `by positivity`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ hpos]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem translate_bound (h : Sch l) (N : ℕ) (p : EuclideanSpace ℝ l) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, |s| ≤ 1 → ∀ x, ‖h (x + s • p)‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ := by
  obtain ⟨M, hM, hb⟩ := exists_decay h N
  refine ⟨M * (1 + ‖p‖) ^ N, by positivity, fun s hs x => ?_⟩
  have h1 : 1 + ‖x‖ ≤ (1 + ‖x + s • p‖) * (1 + ‖p‖) := by
    have h0 : ‖x‖ ≤ ‖x + s • p‖ + ‖s • p‖ := by
      have := norm_sub_le (x + s • p) (s • p)
      simpa using this
    have h2 : ‖s • p‖ ≤ ‖p‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hs
    nlinarith [norm_nonneg (x + s • p), norm_nonneg p]
  have h3 : (1 + ‖x‖) ^ N ≤ (1 + ‖x + s • p‖) ^ N * (1 + ‖p‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 N
  have hpos : 0 < (1 + ‖x‖) ^ N := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖h (x + s • p)‖ * (1 + ‖x‖) ^ N ≤ ‖h (x + s • p)‖ * ((1 + ‖x + s • p‖) ^ N * (1 + ‖p‖) ^ N) := by
        gcongr
    _ = ((1 + ‖x + s • p‖) ^ N * ‖h (x + s • p)‖) * (1 + ‖p‖) ^ N := by ring
    _ ≤ M * (1 + ‖p‖) ^ N := by gcongr; exact hb _

/- English proof (translation)
Use `set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN`. Establish `hi` using `integrable_one_add_norm (E := EuclideanSpace ℝ l) (μ := volume) (r := 2 * N) (by rw [hN]; push_cast; have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EuclideanSpace ℝ l)); linarith)`. Establish `hi2` using `hi.const_mul (K ^ 2)`. Establish `e : ∀ x : EuclideanSpace ℝ l, ‖K * ((1 + ‖x‖) ^ N)⁻¹‖ₑ ^ 2 = ‖K ^ 2 * (1 + ‖x‖) ^ (-(2 * N : ℝ))‖ₑ`. Introduce `x`.

Rewrite using `[← enorm_pow, mul_pow, inv_pow, ← pow_mul, Real.rpow_neg (by positivity), show (2 * (N : ℝ)) = ((N * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]`. Repeatedly rewrite using `[e]`. Conclude with `hi2.hasFiniteIntegral`.
-/
theorem lintegral_inv_pow_lt_top (K : ℝ) :
    ∫⁻ x : EuclideanSpace ℝ l, ‖K * ((1 + ‖x‖) ^ (Module.finrank ℝ (EuclideanSpace ℝ l) + 1))⁻¹‖ₑ ^ 2 < ⊤ := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  have hi := integrable_one_add_norm (E := EuclideanSpace ℝ l) (μ := volume) (r := 2 * N)
    (by rw [hN]; push_cast; have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EuclideanSpace ℝ l)); linarith)
  have hi2 := hi.const_mul (K ^ 2)
  have e : ∀ x : EuclideanSpace ℝ l, ‖K * ((1 + ‖x‖) ^ N)⁻¹‖ₑ ^ 2 = ‖K ^ 2 * (1 + ‖x‖) ^ (-(2 * N : ℝ))‖ₑ := by
    intro x
    rw [← enorm_pow, mul_pow, inv_pow, ← pow_mul, Real.rpow_neg (by positivity),
      show (2 * (N : ℝ)) = ((N * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  simp_rw [e]
  exact hi2.hasFiniteIntegral

/- English proof (translation)
Use `set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1`. Take `⟨M, hM, hb⟩` from `translate_bound (dRho w (dRho w f)) N (pPart w)`. Use `⟨fun x => M * ((1 + ‖x‖) ^ N)⁻¹, fun x => by positivity, lintegral_inv_pow_lt_top M, fun t ht x => ?_⟩` and prove the remaining obligations. Use `set h := dRho w f with hh`. Establish `hB : ∀ s : ℝ, |s| ≤ 1 → ‖rhoFun (s • w) (dRho w h) x‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹` using `fun s hs => by`.

Rewrite using `[rhoFun, norm_mul, norm_phase, one_mul, pPart_smul]`. Conclude with `hb s hs x`. Establish `habs : ∀ s σ : ℝ, σ ∈ Set.uIcc 0 s → |σ| ≤ |s|` using `fun s σ hσ => by`. Simplify using `using Set.abs_sub_left_of_mem_uIcc hσ`. Establish `step1 : ∀ s : ℝ, |s| ≤ 1 → ‖rhoFun (s • w) h x - h x‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ * |s|`.

Introduce `s hs`. Use `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun σ : ℝ => rhoFun (σ • w) h x) (f' := fun σ => rhoFun (σ • w) (dRho w h) x) (s := Set.uIcc 0 s) (C := M * ((1 + ‖x‖) ^ N)⁻¹) (fun σ _ => (hasDerivAt_rhoFun_at w h x σ).hasDerivWithinAt) (fun σ hσ => hB σ ((habs s σ hσ).tr …` as an intermediate fact. Simplify `this` using `[rhoFun_zero, Real.norm_eq_abs]`. Establish `hd : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => rhoFun (σ • w) f x - f x - σ * h x) (rhoFun (σ • w) h x - h x) σ` using `fun σ => by`. Establish `e1 : HasDerivAt (fun σ : ℝ => (σ : ℂ) * h x) (h x) σ`.

Simplify using `using (hasDerivAt_id σ).ofReal_comp.mul_const (h x)`. Conclude with `((hasDerivAt_rhoFun_at w f x σ).sub_const (f x)).sub e1`. Use `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun σ : ℝ => rhoFun (σ • w) f x - f x - σ * h x) (f' := fun σ => rhoFun (σ • w) h x - h x) (s := Set.uIcc 0 t) (C := M * ((1 + ‖x‖) ^ N)⁻¹ * |t|) (fun σ _ => (hd σ).hasDerivWithinAt) (fun σ hσ => (step1 σ ((habs t σ hσ).tra …` as an intermediate fact. Simplify using `only [zero_smul, rhoFun_zero, sub_self, ofReal_zero, zero_mul, sub_zero, Real.norm_eq_abs] at this`. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[← sq_abs t]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem taylor_bound (w : l ⊕ l → ℝ) (f : Sch l) :
    ∃ B : EuclideanSpace ℝ l → ℝ, (∀ x, 0 ≤ B x) ∧ (∫⁻ x, ‖B x‖ₑ ^ 2 < ⊤) ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x, ‖rhoFun (t • w) f x - f x - t * dRho w f x‖ ≤ t ^ 2 * B x := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1
  obtain ⟨M, hM, hb⟩ := translate_bound (dRho w (dRho w f)) N (pPart w)
  refine ⟨fun x => M * ((1 + ‖x‖) ^ N)⁻¹, fun x => by positivity, lintegral_inv_pow_lt_top M, fun t ht x => ?_⟩
  set h := dRho w f with hh
  have hB : ∀ s : ℝ, |s| ≤ 1 → ‖rhoFun (s • w) (dRho w h) x‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ := fun s hs => by
    rw [rhoFun, norm_mul, norm_phase, one_mul, pPart_smul]
    exact hb s hs x
  have habs : ∀ s σ : ℝ, σ ∈ Set.uIcc 0 s → |σ| ≤ |s| := fun s σ hσ => by
    simpa using Set.abs_sub_left_of_mem_uIcc hσ
  have step1 : ∀ s : ℝ, |s| ≤ 1 → ‖rhoFun (s • w) h x - h x‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ * |s| := by
    intro s hs
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun σ : ℝ => rhoFun (σ • w) h x)
      (f' := fun σ => rhoFun (σ • w) (dRho w h) x) (s := Set.uIcc 0 s) (C := M * ((1 + ‖x‖) ^ N)⁻¹)
      (fun σ _ => (hasDerivAt_rhoFun_at w h x σ).hasDerivWithinAt)
      (fun σ hσ => hB σ ((habs s σ hσ).trans hs)) (convex_uIcc 0 s) Set.left_mem_uIcc Set.right_mem_uIcc
    simpa [rhoFun_zero, Real.norm_eq_abs] using this
  have hd : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => rhoFun (σ • w) f x - f x - σ * h x)
      (rhoFun (σ • w) h x - h x) σ := fun σ => by
    have e1 : HasDerivAt (fun σ : ℝ => (σ : ℂ) * h x) (h x) σ := by
      simpa using (hasDerivAt_id σ).ofReal_comp.mul_const (h x)
    exact ((hasDerivAt_rhoFun_at w f x σ).sub_const (f x)).sub e1
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun σ : ℝ => rhoFun (σ • w) f x - f x - σ * h x)
    (f' := fun σ => rhoFun (σ • w) h x - h x) (s := Set.uIcc 0 t) (C := M * ((1 + ‖x‖) ^ N)⁻¹ * |t|)
    (fun σ _ => (hd σ).hasDerivWithinAt)
    (fun σ hσ => (step1 σ ((habs t σ hσ).trans ht)).trans (mul_le_mul_of_nonneg_left (habs t σ hσ) (by positivity)))
    (convex_uIcc 0 t) Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [zero_smul, rhoFun_zero, sub_self, ofReal_zero, zero_mul, sub_zero, Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [← sq_abs t]
  ring

/- English proof (translation)
Simplify using `only [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]`. Rewrite using `[show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Use polynomial arithmetic with `[norm_sub_le a b, norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]`.
-/
theorem enorm_sub_sq_le (a b : ℂ) : ‖a - b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  simp only [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_sub_le a b, norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]

/- English proof (translation)
Rewrite using `[← lintegral_const_mul' _ _ (by simp)]`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lintegral_le_of_bound (φ : EuclideanSpace ℝ l → ℂ) (B : EuclideanSpace ℝ l → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ x, 0 ≤ B x) (h : ∀ x, ‖φ x‖ ≤ c * B x) :
    ∫⁻ x, ‖φ x‖ₑ ^ 2 ≤ ENNReal.ofReal c ^ 2 * ∫⁻ x, ‖B x‖ₑ ^ 2 := by
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x => ?_
  rw [← mul_pow]
  gcongr
  calc ‖φ x‖ₑ = ENNReal.ofReal ‖φ x‖ := (ofReal_norm_eq_enorm _).symm
    _ ≤ ENNReal.ofReal (c * B x) := ENNReal.ofReal_le_ofReal (h x)
    _ = ENNReal.ofReal c * ‖B x‖ₑ := by rw [ENNReal.ofReal_mul hc, Real.enorm_eq_ofReal (hB x)]

/- English proof (translation)
Introduce `l _ L' A' C hC hA hI w f`. Take `⟨B₁, hB₁0, hB₁i, hB₁⟩` from `taylor_bound w f`. Take `⟨B₂, hB₂0, hB₂i, hB₂⟩` from `taylor_bound (L' w) (A' f)`. Use `set u := A' (dRho w f) - dRho (L' w) (A' f) with hu`. Establish `t1 : ∫⁻ x, ‖B₁ x‖ₑ ^ 2 ≠ ⊤` using `hB₁i.ne`.

Establish `t2 : (2 : ℝ≥0∞) * C ≠ ⊤` using `ENNReal.mul_ne_top (by norm_num) hC`. Establish `t4 : (2 : ℝ≥0∞) ≠ ⊤` using `by norm_num`. Take `⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = 2 * C * (∫⁻ x, ‖B₁ x‖ₑ ^ 2) + 2 * ∫⁻ x, ‖B₂ x‖ₑ ^ 2` from `⟨_, rfl⟩`. Establish `hKt : K ≠ ⊤`. Rewrite using `[hK]`.

Conclude with `ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top t2 t1, ENNReal.mul_ne_top t4 hB₂i.ne⟩`. Establish `hmeas : ∀ g : Sch l, AEMeasurable (fun x => ‖g x‖ₑ ^ 2) volume` using `fun g => ((ENNReal.continuous_pow 2).comp g.continuous.enorm).aemeasurable`. Establish `key : ∀ t : ℝ, 0 < t → t ≤ 1 → ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ ENNReal.ofReal (t ^ 2) * K`. Introduce `t ht0 ht1`. Establish `hta : |t| ≤ 1` using `by rw [abs_of_pos ht0]; exact ht1`.

Take `⟨g, hg⟩` from `exists_schwartz_rhoFun l (t • w) f`. Establish `hAg : ⇑(A' g) = rhoFun (t • L' w) ⇑(A' f)` using `by rw [hI (t • w) f g hg, map_smul]`. Use `set k := g - f - (t : ℂ) • dRho w f with hk`. Use `set m := A' g - A' f - (t : ℂ) • dRho (L' w) (A' f) with hm`. Establish `hkb : ∀ x, ‖k x‖ ≤ t ^ 2 * B₁ x` using `fun x => by`.

Establish `e : k x = rhoFun (t • w) f x - f x - t * dRho w f x`. Simplify using `only [hk, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hg]`. Rewrite using `[e]`. Conclude with `hB₁ t hta x`. Establish `hmb : ∀ x, ‖m x‖ ≤ t ^ 2 * B₂ x` using `fun x => by`.

Establish `e : m x = rhoFun (t • L' w) (A' f) x - A' f x - t * dRho (L' w) (A' f) x`. Simplify using `only [hm, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hAg]`. Rewrite using `[e]`. Conclude with `hB₂ t hta x`. Establish `hum : (t : ℂ) • u = m - A' k`.

Simplify using `only [hu, hk, hm, map_sub, map_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Take `⟨a, ha⟩ : ∃ a : ℝ≥0∞, a = ENNReal.ofReal (t ^ 2)` from `⟨_, rfl⟩`. Establish `ha0 : a ≠ 0` using `ha ▸ (ENNReal.ofReal_pos.2 (by positivity)).ne'`. Establish `hat : a ≠ ⊤` using `ha ▸ ENNReal.ofReal_ne_top`.

Establish `hIk` using `lintegral_le_of_bound k B₁ (by positivity) hB₁0 hkb`. Establish `hIm` using `lintegral_le_of_bound m B₂ (by positivity) hB₂0 hmb`. Establish `hsc : ∀ x, ‖((t : ℂ) • u) x‖ₑ ^ 2 = a * ‖u x‖ₑ ^ 2` using `fun x => by`. Rewrite using `[SchwartzMap.smul_apply, enorm_smul, mul_pow, ha, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Establish `main : a * ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ a * (a * K)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← lintegral_const_mul' _ _ hat]`. Simplify using `only [hsc]`. Use `_ = ∫⁻ x, ‖m x - A' k x‖ₑ ^ 2 := by rw [hum]; simp only [SchwartzMap.sub_apply]`. Use `_ ≤ ∫⁻ x, (2 * ‖m x‖ₑ ^ 2 + 2 * ‖A' k x‖ₑ ^ 2) := lintegral_mono fun x => enorm_sub_sq_le _ _`.

Use `_ = 2 * (∫⁻ x, ‖m x‖ₑ ^ 2) + 2 * ∫⁻ x, ‖A' k x‖ₑ ^ 2 := by`. Rewrite using `[lintegral_add_left' ((hmeas m).const_mul 2), lintegral_const_mul' _ _ t4, lintegral_const_mul' _ _ t4]`. Use `_ ≤ 2 * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₂ x‖ₑ ^ 2) + 2 * (C * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₁ x‖ₑ ^ 2)) := by`. Establish `hAk : ∫⁻ x, ‖A' k x‖ₑ ^ 2 ≤ C * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₁ x‖ₑ ^ 2)` using `(hA k).trans (by gcongr)`. Use `gcongr`.

Use `_ = a * (a * K) := by rw [hK, ha]; ring`. Rewrite using `[← ha]`. Conclude with `(ENNReal.mul_le_mul_iff_right ha0 hat).mp main`. Establish `hz : ∫⁻ x, ‖u x‖ₑ ^ 2 = 0`. Use `le_antisymm ?_ bot_le` and prove the remaining obligations.

Establish `ht : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ 2) * K) (𝓝[>] 0) (𝓝 0)`. Use `ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal ((continuous_pow 2).tendsto (0 : ℝ))) (Or.inr hKt)` as an intermediate fact. Simplify using `using this.mono_left nhdsWithin_le_nhds`. Use `ge_of_tendsto ht ?_` and prove the remaining obligations. Use `filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht`.

Conclude with `key t ht.1 ht.2.le`. Establish `hae` using `(lintegral_eq_zero_iff' (hmeas u)).1 hz`. Establish `hu0 : ⇑u = fun _ => (0 : ℂ)`. Use `(Continuous.ae_eq_iff_eq volume u.continuous (continuous_const (y := (0 : ℂ)))).1 ?_` and prove the remaining obligations. Use `filter_upwards [hae] with x hx`.

Establish `hx' : ‖u x‖ₑ ^ 2 = 0` using `hx`. Simplify using `using hx'`. Establish `: u = 0` using `by ext x; simpa using congrFun hu0 x`. Conclude with `sub_eq_zero.1 this`.
-/
theorem dRho_intertwine : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w (f f' : GlobalTheory.RealWeil.Sch l), ⇑f' = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(A' f') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' f)) →
    ∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f) := by
  intro l _ L' A' C hC hA hI w f
  obtain ⟨B₁, hB₁0, hB₁i, hB₁⟩ := taylor_bound w f
  obtain ⟨B₂, hB₂0, hB₂i, hB₂⟩ := taylor_bound (L' w) (A' f)
  set u := A' (dRho w f) - dRho (L' w) (A' f) with hu
  have t1 : ∫⁻ x, ‖B₁ x‖ₑ ^ 2 ≠ ⊤ := hB₁i.ne
  have t2 : (2 : ℝ≥0∞) * C ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hC
  have t4 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = 2 * C * (∫⁻ x, ‖B₁ x‖ₑ ^ 2) + 2 * ∫⁻ x, ‖B₂ x‖ₑ ^ 2 := ⟨_, rfl⟩
  have hKt : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top t2 t1, ENNReal.mul_ne_top t4 hB₂i.ne⟩
  have hmeas : ∀ g : Sch l, AEMeasurable (fun x => ‖g x‖ₑ ^ 2) volume := fun g =>
    ((ENNReal.continuous_pow 2).comp g.continuous.enorm).aemeasurable
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ ENNReal.ofReal (t ^ 2) * K := by
    intro t ht0 ht1
    have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
    obtain ⟨g, hg⟩ := exists_schwartz_rhoFun l (t • w) f
    have hAg : ⇑(A' g) = rhoFun (t • L' w) ⇑(A' f) := by rw [hI (t • w) f g hg, map_smul]
    set k := g - f - (t : ℂ) • dRho w f with hk
    set m := A' g - A' f - (t : ℂ) • dRho (L' w) (A' f) with hm
    have hkb : ∀ x, ‖k x‖ ≤ t ^ 2 * B₁ x := fun x => by
      have e : k x = rhoFun (t • w) f x - f x - t * dRho w f x := by
        simp only [hk, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hg]
      rw [e]; exact hB₁ t hta x
    have hmb : ∀ x, ‖m x‖ ≤ t ^ 2 * B₂ x := fun x => by
      have e : m x = rhoFun (t • L' w) (A' f) x - A' f x - t * dRho (L' w) (A' f) x := by
        simp only [hm, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hAg]
      rw [e]; exact hB₂ t hta x
    have hum : (t : ℂ) • u = m - A' k := by
      simp only [hu, hk, hm, map_sub, map_smul, smul_sub]
      abel
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0∞, a = ENNReal.ofReal (t ^ 2) := ⟨_, rfl⟩
    have ha0 : a ≠ 0 := ha ▸ (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hat : a ≠ ⊤ := ha ▸ ENNReal.ofReal_ne_top
    have hIk := lintegral_le_of_bound k B₁ (by positivity) hB₁0 hkb
    have hIm := lintegral_le_of_bound m B₂ (by positivity) hB₂0 hmb
    have hsc : ∀ x, ‖((t : ℂ) • u) x‖ₑ ^ 2 = a * ‖u x‖ₑ ^ 2 := fun x => by
      rw [SchwartzMap.smul_apply, enorm_smul, mul_pow, ha, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have main : a * ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ a * (a * K) := by
      calc a * ∫⁻ x, ‖u x‖ₑ ^ 2 = ∫⁻ x, ‖((t : ℂ) • u) x‖ₑ ^ 2 := by
            rw [← lintegral_const_mul' _ _ hat]; simp only [hsc]
        _ = ∫⁻ x, ‖m x - A' k x‖ₑ ^ 2 := by rw [hum]; simp only [SchwartzMap.sub_apply]
        _ ≤ ∫⁻ x, (2 * ‖m x‖ₑ ^ 2 + 2 * ‖A' k x‖ₑ ^ 2) := lintegral_mono fun x => enorm_sub_sq_le _ _
        _ = 2 * (∫⁻ x, ‖m x‖ₑ ^ 2) + 2 * ∫⁻ x, ‖A' k x‖ₑ ^ 2 := by
            rw [lintegral_add_left' ((hmeas m).const_mul 2), lintegral_const_mul' _ _ t4, lintegral_const_mul' _ _ t4]
        _ ≤ 2 * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₂ x‖ₑ ^ 2) +
              2 * (C * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₁ x‖ₑ ^ 2)) := by
            have hAk : ∫⁻ x, ‖A' k x‖ₑ ^ 2 ≤ C * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₁ x‖ₑ ^ 2) :=
              (hA k).trans (by gcongr)
            gcongr
        _ = a * (a * K) := by rw [hK, ha]; ring
    rw [← ha]
    exact (ENNReal.mul_le_mul_iff_right ha0 hat).mp main
  have hz : ∫⁻ x, ‖u x‖ₑ ^ 2 = 0 := by
    refine le_antisymm ?_ bot_le
    have ht : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ 2) * K) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal ((continuous_pow 2).tendsto (0 : ℝ)))
        (Or.inr hKt)
      simpa using this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact key t ht.1 ht.2.le
  have hae := (lintegral_eq_zero_iff' (hmeas u)).1 hz
  have hu0 : ⇑u = fun _ => (0 : ℂ) := by
    refine (Continuous.ae_eq_iff_eq volume u.continuous (continuous_const (y := (0 : ℂ)))).1 ?_
    filter_upwards [hae] with x hx
    have hx' : ‖u x‖ₑ ^ 2 = 0 := hx
    simpa using hx'
  have : u = 0 := by ext x; simpa using congrFun hu0 x
  exact sub_eq_zero.1 this

end GlobalTheory.RealWeil.DRhoTransfer
