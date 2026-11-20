import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSB

section VE

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E]

/- English proof (translation)
Set `` to `nontriviallyNormedField F`. Use `completeSpace_nontriviallyNormedField F` as an intermediate fact. Use `t2Space_of_isNonarchimedeanLocalField E` as an intermediate fact. Establish `: ContinuousSMul F E` using `continuousSMul_of_algebraMap F E h`. Conclude with `LinearMap.isClosedEmbedding_of_injective (f := Algebra.linearMap F E) (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)`.
-/
theorem isClosedEmbedding_algebraMap (h : Continuous (algebraMap F E)) :
    Topology.IsClosedEmbedding (algebraMap F E) := by
  let := nontriviallyNormedField F
  have := completeSpace_nontriviallyNormedField F
  have := t2Space_of_isNonarchimedeanLocalField E
  have : ContinuousSMul F E := continuousSMul_of_algebraMap F E h
  exact LinearMap.isClosedEmbedding_of_injective (f := Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a b => vle_map_iff_of_valuation_lt_one_iff (algebraMap F E) (fun z => by rw [← GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff, ← GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff, (isClosedEmbedding_algebraMap h).isInducing.tendsto_nhds_iff, ← map_zero (algebr …`.
-/
theorem valuativeExtension_of_continuous (h : Continuous (algebraMap F E)) : ValuativeExtension F E :=
  ⟨fun a b => vle_map_iff_of_valuation_lt_one_iff (algebraMap F E) (fun z => by
    rw [← GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff, ← GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff,
      (isClosedEmbedding_algebraMap h).isInducing.tendsto_nhds_iff, ← map_zero (algebraMap F E)]
    simp only [Function.comp_def, map_pow]) a b⟩

end VE

/- English proof (translation)
The claim follows from `isLocallyConstant_of_add_valBall (N := addCharConductor χ) fun x h hh => by rw [AddChar.map_add_eq_mul, isTrivialOn_addCharConductor hχ hχ1 h hh, mul_one]`.
-/
theorem isLocallyConstant_char {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) :
    IsLocallyConstant (fun x => (χ x : ℂ)) :=
  isLocallyConstant_of_add_valBall (N := addCharConductor χ) fun x h hh => by
    rw [AddChar.map_add_eq_mul, isTrivialOn_addCharConductor hχ hχ1 h hh, mul_one]

section SB

variable {E : Type} [TopologicalSpace E]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hH.1.comp_continuous φ.continuous, hH.2.comp_homeomorph φ⟩`.
-/
theorem sb_comp (φ : E ≃ₜ E) {H : E → ℂ} (hH : H ∈ SBE E) : (fun z => H (φ z)) ∈ SBE E :=
  ⟨hH.1.comp_continuous φ.continuous, hH.2.comp_homeomorph φ⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.mul hH.1, hH.2.mul_left⟩`.
-/
theorem sb_mul {f H : E → ℂ} (hf : IsLocallyConstant f) (hH : H ∈ SBE E) :
    (fun z => f z * H z) ∈ SBE E :=
  ⟨hf.mul hH.1, hH.2.mul_left⟩

end SB

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]
  [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

/- English proof (translation)
Rewrite using `[(isClosedEmbedding_algebraMap h).isInducing.continuous_iff]`. Establish `e : (algebraMap F E) ∘ (Algebra.norm F : E → F) = fun x => x * conj F E x`. Use function extensionality and compare the values at `algebraMap_norm_eq_mul_conj`. Rewrite using `[e]`. Conclude with `continuous_id.mul continuous_conj`.
-/
theorem continuous_norm_of (h : Continuous (algebraMap F E)) :
    Continuous (Algebra.norm F : E → F) := by
  rw [(isClosedEmbedding_algebraMap h).isInducing.continuous_iff]
  have e : (algebraMap F E) ∘ (Algebra.norm F : E → F) = fun x => x * conj F E x :=
    funext algebraMap_norm_eq_mul_conj
  rw [e]
  exact continuous_id.mul continuous_conj

/- English proof (translation)
Rewrite using `[map_mul, hu, mul_one]`.
-/
theorem norm_mul_of_norm_one {u : E} (hu : Algebra.norm F u = 1) (x : E) :
    Algebra.norm F (x * u) = Algebra.norm F x := by
  rw [map_mul, hu, mul_one]

/- English proof (translation)
Establish `h` using `algebraMap_norm_eq_mul_conj (K := F) u`. Rewrite `h` using `[hu, map_one]`. Rewrite using `[mul_comm]`. Conclude with `h.symm`.
-/
theorem conj_mul_self_of_norm_one {u : E} (hu : Algebra.norm F u = 1) : conj F E u * u = 1 := by
  have h := algebraMap_norm_eq_mul_conj (K := F) u
  rw [hu, map_one] at h
  rw [mul_comm]
  exact h.symm

/- English proof (translation)
Rewrite using `[← modulus_norm (K := F), hu, GroundTheory.LocalField.modulus_one]`.
-/
theorem modulus_of_norm_one {u : E} (hu : Algebra.norm F u = 1) : GroundTheory.LocalField.modulus u = 1 := by
  rw [← modulus_norm (K := F), hu, GroundTheory.LocalField.modulus_one]

/- English proof (translation)
Rewrite using `[rW, if_neg hc]`. Use `congr 1`. Rewrite using `[localFourier, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `e : (a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / c = a * Algebra.norm F z / c + (d * Algebra.norm F u / c + Algebra.trace F E (u * (algebraMap F E (-c⁻¹) * conj F E z)))`.

Establish `h : u * (algebraMap F E (-c⁻¹) * conj F E z) = algebraMap F E (-c⁻¹) * (conj F E z * u)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, trace_algebraMap_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `show (χ _ : ℂ) * Φ u = (χ _ : ℂ) * ((χ _ : ℂ) * Φ u * (χ (Algebra.trace F E (u * (algebraMap F E (-c⁻¹) * conj F E z))) : ℂ))`. Rewrite using `[e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rW_of_ne_zero (χ : AddChar F Circle) (μ : Measure E) (lam : ℂ) {a b c d : F} (hc : c ≠ 0)
    (Φ : E → ℂ) (z : E) :
    rW χ (conj F E) μ lam a b c d Φ z =
      (lam * nsg E (-c) * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ)) * ((χ (a * Algebra.norm F z / c) : ℂ) *
        localFourier μ (chE E χ) (fun u => (χ (d * Algebra.norm F u / c) : ℂ) * Φ u)
          (algebraMap F E (-c⁻¹) * conj F E z)) := by
  rw [rW, if_neg hc]
  congr 1
  rw [localFourier, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have e : (a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / c =
      a * Algebra.norm F z / c + (d * Algebra.norm F u / c +
        Algebra.trace F E (u * (algebraMap F E (-c⁻¹) * conj F E z))) := by
    have h : u * (algebraMap F E (-c⁻¹) * conj F E z) = algebraMap F E (-c⁻¹) * (conj F E z * u) := by
      ring
    rw [h, trace_algebraMap_mul]
    field_simp
    ring
  show (χ _ : ℂ) * Φ u = (χ _ : ℂ) * ((χ _ : ℂ) * Φ u *
    (χ (Algebra.trace F E (u * (algebraMap F E (-c⁻¹) * conj F E z))) : ℂ))
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  push_cast
  ring

/- English proof (translation)
Establish `hN` using `continuous_norm_of (F := F) (E := E) hcont`. Establish `hlc` using `isLocallyConstant_char hχ hχ1`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Establish `ha : a ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hdet`. Establish `hA : algebraMap F E a ≠ 0` using `(map_ne_zero _).2 ha`. Establish `e : rW χ (conj F E) μ lam a b 0 d Φ = fun z => ((χ (a * b * Algebra.norm F z) : ℂ) * nsg E a * ((modulus a : ℝ) : ℂ)) * Φ (Homeomorph.mulLeft₀ (algebraMap F E a) hA z)`. Use function extensionality and compare the values at `z`.

Rewrite using `[rW, if_pos rfl]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `sb_mul ?_ (sb_comp (Homeomorph.mulLeft₀ (algebraMap F E a) hA) hΦ)` and prove the remaining obligations. Conclude with `((hlc.comp_continuous (continuous_const.mul hN)).mul (IsLocallyConstant.const _)).mul (IsLocallyConstant.const _)`.

Establish `hχE : Continuous (chE E χ)` using `continuous_traceChar hχ hχ1`. Establish `hχE1 : chE E χ ≠ 1` using `traceChar_ne_one hχ hχ1`. Establish `hΨ : (fun u => (χ (d * Algebra.norm F u / c) : ℂ) * Φ u) ∈ SBE E` using `sb_mul (hlc.comp_continuous ((continuous_const.mul hN).div_const c)) hΦ`. Establish `hH` using `localFourier_mem_schwartzBruhat μ hχE hχE1 hΨ`. Establish `hB : algebraMap F E (-c⁻¹) ≠ 0` using `(map_ne_zero _).2 (neg_ne_zero.2 (inv_ne_zero hc))`.

Set `φ : E ≃ₜ E` to `(conjContinuousAddEquiv F E).toHomeomorph.trans (Homeomorph.mulLeft₀ (algebraMap F E (-c⁻¹)) hB)`. Establish `e : rW χ (conj F E) μ lam a b c d Φ = fun z => (lam * nsg E (-c) * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ)) * ((χ (a * Algebra.norm F z / c) : ℂ) * localFourier μ (chE E χ) (fun u => (χ (d * Algebra.norm F u / c) : ℂ) * Φ u) (φ z))`. Use function extensionality and compare the values at `fun z => rW_of_ne_zero χ μ lam hc Φ z`. Rewrite using `[e]`. Conclude with `sb_mul (IsLocallyConstant.const _) (sb_mul (hlc.comp_continuous ((continuous_const.mul hN).div_const c)) (sb_comp φ hH))`.
-/
theorem rW_mem_SBE {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ)
    {a b c d : F} (hdet : a * d - b * c = 1) {Φ : E → ℂ} (hΦ : Φ ∈ SBE E) :
    rW χ (conj F E) μ lam a b c d Φ ∈ SBE E := by
  have hN := continuous_norm_of (F := F) (E := E) hcont
  have hlc := isLocallyConstant_char hχ hχ1
  by_cases hc : c = 0
  · subst hc
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hdet
    have hA : algebraMap F E a ≠ 0 := (map_ne_zero _).2 ha
    have e : rW χ (conj F E) μ lam a b 0 d Φ = fun z =>
        ((χ (a * b * Algebra.norm F z) : ℂ) * nsg E a * ((modulus a : ℝ) : ℂ)) *
          Φ (Homeomorph.mulLeft₀ (algebraMap F E a) hA z) := by
      funext z
      rw [rW, if_pos rfl]
      rfl
    rw [e]
    refine sb_mul ?_ (sb_comp (Homeomorph.mulLeft₀ (algebraMap F E a) hA) hΦ)
    exact ((hlc.comp_continuous (continuous_const.mul hN)).mul (IsLocallyConstant.const _)).mul
      (IsLocallyConstant.const _)
  · have hχE : Continuous (chE E χ) := continuous_traceChar hχ hχ1
    have hχE1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
    have hΨ : (fun u => (χ (d * Algebra.norm F u / c) : ℂ) * Φ u) ∈ SBE E :=
      sb_mul (hlc.comp_continuous ((continuous_const.mul hN).div_const c)) hΦ
    have hH := localFourier_mem_schwartzBruhat μ hχE hχE1 hΨ
    have hB : algebraMap F E (-c⁻¹) ≠ 0 := (map_ne_zero _).2 (neg_ne_zero.2 (inv_ne_zero hc))
    let φ : E ≃ₜ E := (conjContinuousAddEquiv F E).toHomeomorph.trans
      (Homeomorph.mulLeft₀ (algebraMap F E (-c⁻¹)) hB)
    have e : rW χ (conj F E) μ lam a b c d Φ = fun z =>
        (lam * nsg E (-c) * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ)) * ((χ (a * Algebra.norm F z / c) : ℂ) *
          localFourier μ (chE E χ) (fun u => (χ (d * Algebra.norm F u / c) : ℂ) * Φ u) (φ z)) :=
      funext fun z => rW_of_ne_zero χ μ lam hc Φ z
    rw [e]
    exact sb_mul (IsLocallyConstant.const _)
      (sb_mul (hlc.comp_continuous ((continuous_const.mul hN).div_const c)) (sb_comp φ hH))

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Rewrite using `[rW, rW, if_pos rfl, if_pos rfl, norm_mul_of_norm_one hu, ← mul_assoc (algebraMap F E a), hΦ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[rW, rW, if_neg hc, if_neg hc]`.

Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hu`. Establish `key : ∫ v, (χ ((a * Algebra.norm F (x * u) + d * Algebra.norm F v - Algebra.trace F E (conj F E (x * u) * v)) / c) : ℂ) * Φ v ∂μ = k * ∫ v, (χ ((a * Algebra.norm F x + d * Algebra.norm F v - Algebra.trace F E (conj F E x * v)) / c) : ℂ) * Φ v ∂μ`. Establish `hs` using `integral_comp_mul_left μ hu0 (fun v => (χ ((a * Algebra.norm F (x * u) + d * Algebra.norm F v - Algebra.trace F E (conj F E (x * u) * v)) / c) : ℂ) * Φ v)`.

Rewrite `hs` using `[modulus_of_norm_one hu]`. Simplify using `only [NNReal.coe_one, inv_one, one_smul] at hs`. Rewrite using `[← hs, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Establish `t : conj F E (x * u) * (u * v) = conj F E x * v`.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Φ (u * v) = k * Φ v`. Rewrite using `[mul_comm]`. Conclude with `hΦ v`.

Use `show (χ _ : ℂ) * Φ (u * v) = _`. Rewrite using `[t, norm_mul_of_norm_one hu, map_mul (Algebra.norm F) u v, hu, one_mul, h2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rW_isotypic (χ : AddChar F Circle) (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ)
    (a b c d : F) {Φ : E → ℂ} {u : E} (hu : Algebra.norm F u = 1) {k : ℂ}
    (hΦ : ∀ x, Φ (x * u) = k * Φ x) (x : E) :
    rW χ (conj F E) μ lam a b c d Φ (x * u) = k * rW χ (conj F E) μ lam a b c d Φ x := by
  by_cases hc : c = 0
  · subst hc
    rw [rW, rW, if_pos rfl, if_pos rfl, norm_mul_of_norm_one hu, ← mul_assoc (algebraMap F E a), hΦ]
    ring
  · rw [rW, rW, if_neg hc, if_neg hc]
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    have key : ∫ v, (χ ((a * Algebra.norm F (x * u) + d * Algebra.norm F v -
          Algebra.trace F E (conj F E (x * u) * v)) / c) : ℂ) * Φ v ∂μ =
        k * ∫ v, (χ ((a * Algebra.norm F x + d * Algebra.norm F v -
          Algebra.trace F E (conj F E x * v)) / c) : ℂ) * Φ v ∂μ := by
      have hs := integral_comp_mul_left μ hu0 (fun v => (χ ((a * Algebra.norm F (x * u) +
        d * Algebra.norm F v - Algebra.trace F E (conj F E (x * u) * v)) / c) : ℂ) * Φ v)
      rw [modulus_of_norm_one hu] at hs
      simp only [NNReal.coe_one, inv_one, one_smul] at hs
      rw [← hs, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      have t : conj F E (x * u) * (u * v) = conj F E x * v := by
        rw [map_mul]
        calc conj F E x * conj F E u * (u * v) = conj F E x * (conj F E u * u) * v := by ring
          _ = conj F E x * v := by rw [conj_mul_self_of_norm_one hu, mul_one]
      have h2 : Φ (u * v) = k * Φ v := by
        rw [mul_comm]
        exact hΦ v
      show (χ _ : ℂ) * Φ (u * v) = _
      rw [t, norm_mul_of_norm_one hu, map_mul (Algebra.norm F) u v, hu, one_mul, h2]
      ring
    rw [key]
    ring

end Main

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη g hg Φ hΦ`. Use `haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Use `haveI : ValuativeExtension F E := valuativeExtension_of_continuous hcont`. Use `haveI : Algebra.IsSeparable F E := inferInstance`.

Establish `hσc : σ = conj F E` using `(eq_one_or_eq_conj σ).resolve_left hσ`. Substitute `hσc` using the available equality. Establish `hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1`. Rewrite using `[← Matrix.det_fin_two]`. Conclude with `hg`.

Establish `hm` using `rW_mem_SBE (E := E) hχ hχ1 hcont (muE E χ) (lamE E χ η) hdet hΦ`. Use `⟨hm, fun c hc => ⟨hm.1, hm.2, fun u hu x => ?_⟩⟩` and prove the remaining obligations. Conclude with `rW_isotypic χ (muE E χ) (lamE E χ η) _ _ _ _ hu (hc.2.2 u hu) x`.
-/
theorem wsb : Ad3.K.GL2LocalData.WSB := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη g hg Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hσc : σ = conj F E := (eq_one_or_eq_conj σ).resolve_left hσ
  subst hσc
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact hg
  have hm := rW_mem_SBE (E := E) hχ hχ1 hcont (muE E χ) (lamE E χ η) hdet hΦ
  refine ⟨hm, fun c hc => ⟨hm.1, hm.2, fun u hu x => ?_⟩⟩
  exact rW_isotypic χ (muE E χ) (lamE E χ η) _ _ _ _ hu (hc.2.2 u hu) x

end GlobalTheory.CompanionTheory.WeilSB
