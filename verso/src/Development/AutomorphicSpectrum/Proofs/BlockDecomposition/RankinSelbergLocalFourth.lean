import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

open MeasureTheory Matrix GroundTheory.LocalField Ad3 Ad3.R
open scoped ValuativeRel ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinKernel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

open scoped Classical in

def ePow (a : ℝ) (t : F) : ℝ≥0∞ := if t = 0 then 0 else ENNReal.ofReal ((modulus t : ℝ) ^ a)

/- English proof (translation)
Simplify using `[ePow]`.
-/
theorem ePow_zero (a : ℝ) : ePow a (0 : F) = 0 := by simp [ePow]

/- English proof (translation)
Simplify using `[ePow, ht]`.
-/
theorem ePow_of_ne (a : ℝ) {t : F} (ht : t ≠ 0) :
    ePow a t = ENNReal.ofReal ((modulus t : ℝ) ^ a) := by simp [ePow, ht]

/- English proof (translation)
Conclude with `modulus_pos ht` after adjusting the coercions.
-/
theorem modulus_pos_real {t : F} (ht : t ≠ 0) : (0 : ℝ) < modulus t := by
  exact_mod_cast modulus_pos ht

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx, ePow_zero]`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy, ePow_zero]`. Rewrite using `[ePow_of_ne a hx, ePow_of_ne a hy, ePow_of_ne a (mul_ne_zero hx hy), modulus_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), ENNReal.ofReal_mul (by positivity)]`.
-/
theorem ePow_mul (a : ℝ) (x y : F) : ePow a (x * y) = ePow a x * ePow a y := by
  by_cases hx : x = 0
  · simp [hx, ePow_zero]
  by_cases hy : y = 0
  · simp [hy, ePow_zero]
  rw [ePow_of_ne a hx, ePow_of_ne a hy, ePow_of_ne a (mul_ne_zero hx hy), modulus_mul,
    NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
    ENNReal.ofReal_mul (by positivity)]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Rewrite using `[ePow_of_ne a hx, ePow_of_ne a (neg_ne_zero.mpr hx), modulus_neg_eq]`.
-/
theorem ePow_neg (a : ℝ) (x : F) : ePow a (-x) = ePow a x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [ePow_of_ne a hx, ePow_of_ne a (neg_ne_zero.mpr hx), modulus_neg_eq]

/- English proof (translation)
Distinguish the cases in `ht : t = 0`. Simplify using `[ht, ePow_zero]`. Rewrite using `[ePow_of_ne a ht, ePow_of_ne b ht, ePow_of_ne _ ht, ← ENNReal.ofReal_mul (by positivity), Real.rpow_add (modulus_pos_real ht)]`.
-/
theorem ePow_mul_ePow (a b : ℝ) (t : F) : ePow a t * ePow b t = ePow (a + b) t := by
  by_cases ht : t = 0
  · simp [ht, ePow_zero]
  rw [ePow_of_ne a ht, ePow_of_ne b ht, ePow_of_ne _ ht, ← ENNReal.ofReal_mul (by positivity),
    Real.rpow_add (modulus_pos_real ht)]

/- English proof (translation)
Rewrite using `[ePow_of_ne a hx, ePow_of_ne a hy]`. Conclude with `ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (modulus_pos_real hy) (by exact_mod_cast h) ha)`.
-/
theorem ePow_anti {a : ℝ} (ha : a ≤ 0) {x y : F} (hy : y ≠ 0) (hx : x ≠ 0)
    (h : modulus y ≤ modulus x) : ePow a x ≤ ePow a y := by
  rw [ePow_of_ne a hx, ePow_of_ne a hy]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_nonpos (modulus_pos_real hy) (by exact_mod_cast h) ha)

/- English proof (translation)
Use `(Units.continuous_val.comp hc).mul ?_` and prove the remaining obligations. Use `(Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_` and prove the remaining obligations. Conclude with `Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)`.
-/
theorem continuous_char_units {c : Fˣ →* ℂˣ} (hc : Continuous c) (s : ℂ) :
    Continuous fun u : Fˣ => ((c u : ℂˣ) : ℂ) * mp u s := by
  refine (Units.continuous_val.comp hc).mul ?_
  refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)

/- English proof (translation)
Simplify using `[chF, u.ne_zero]`.
-/
theorem chF_coe (c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) : chF c s (u : F) = ((c u : ℂˣ) : ℂ) * mp u s := by
  simp [chF, u.ne_zero]

/- English proof (translation)
Distinguish the cases in `ht : t = 0`. Simplify using `[chF, ht, ePow_zero]`. Take `⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = t` from `⟨Units.mk0 t ht, rfl⟩`. Rewrite using `[chF_coe, ePow_of_ne _ ht, ← ofReal_norm, norm_mul, hc, one_mul, mp, Complex.norm_cpow_eq_rpow_re_of_pos (modulus_pos_real ht)]`.
-/
theorem enorm_chF {c : Fˣ →* ℂˣ} (hc : ∀ x, ‖((c x : ℂˣ) : ℂ)‖ = 1) (s : ℂ) (t : F) :
    ‖chF c s t‖ₑ = ePow s.re t := by
  by_cases ht : t = 0
  · simp [chF, ht, ePow_zero]
  obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = t := ⟨Units.mk0 t ht, rfl⟩
  rw [chF_coe, ePow_of_ne _ ht, ← ofReal_norm, norm_mul, hc, one_mul, mp,
    Complex.norm_cpow_eq_rpow_re_of_pos (modulus_pos_real ht)]

/- English proof (translation)
Establish `hmono : Monotone fun m : ℕ => Set.pi Set.univ fun _ : Fin 2 => (valBall F (-(m : ℤ)) : Set F)`. Introduce `m m' h r hr i hi`. Conclude with `valBall_antitone (by omega) (hr i hi)`. Take `⟨m, hm⟩` from `hB.elim_directed_cover (fun m : ℕ => Set.pi Set.univ fun _ : Fin 2 => (valBall F (-(m : ℤ)) : Set F)) (fun m => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall _) (fun r _ => by`. Take `⟨m₀, h₀⟩` from `exists_mem_valBall_neg_nat (r 0)`.

Take `⟨m₁, h₁⟩` from `exists_mem_valBall_neg_nat (r 1)`. Use `Set.mem_iUnion.mpr ⟨max m₀ m₁, fun i _ => ?_⟩` and prove the remaining obligations. Use `fin_cases i`. Conclude with `valBall_antitone (by omega) h₀`. Conclude with `valBall_antitone (by omega) h₁)`.

Use the proof step `hmono.directed_le`. Conclude with `⟨_, hm⟩`.
-/
theorem exists_box {B : Set (Fin 2 → F)} (hB : IsCompact B) :
    ∃ n : ℤ, B ⊆ Set.pi Set.univ fun _ => (valBall F n : Set F) := by
  have hmono : Monotone fun m : ℕ =>
      Set.pi Set.univ fun _ : Fin 2 => (valBall F (-(m : ℤ)) : Set F) := by
    intro m m' h r hr i hi
    exact valBall_antitone (by omega) (hr i hi)
  obtain ⟨m, hm⟩ := hB.elim_directed_cover
    (fun m : ℕ => Set.pi Set.univ fun _ : Fin 2 => (valBall F (-(m : ℤ)) : Set F))
    (fun m => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall _)
    (fun r _ => by
      obtain ⟨m₀, h₀⟩ := exists_mem_valBall_neg_nat (r 0)
      obtain ⟨m₁, h₁⟩ := exists_mem_valBall_neg_nat (r 1)
      refine Set.mem_iUnion.mpr ⟨max m₀ m₁, fun i _ => ?_⟩
      fin_cases i
      · exact valBall_antitone (by omega) h₀
      · exact valBall_antitone (by omega) h₁)
    hmono.directed_le
  exact ⟨_, hm⟩

section Meas

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `: (ePow a : F → ℝ≥0∞) = fun t => if t = 0 then 0 else ENNReal.ofReal ((modulus t : ℝ) ^ a)`. Use function extensionality and compare the values at `t`. Distinguish the cases in `ht : t = 0`. Simplify using `[ht, ePow_zero]`. Simplify using `[ht, ePow_of_ne]`.

Rewrite using `[this]`. Conclude with `Measurable.ite (measurableSet_eq) measurable_const (ENNReal.measurable_ofReal.comp ((measurable_modulus.coe_nnreal_real).pow_const a))`.
-/
theorem measurable_ePow (a : ℝ) : Measurable (ePow a : F → ℝ≥0∞) := by
  classical
  have : (ePow a : F → ℝ≥0∞) = fun t => if t = 0 then 0 else ENNReal.ofReal ((modulus t : ℝ) ^ a) := by
    funext t
    by_cases ht : t = 0
    · simp [ht, ePow_zero]
    · simp [ht, ePow_of_ne]
  rw [this]
  exact Measurable.ite (measurableSet_eq) measurable_const
    (ENNReal.measurable_ofReal.comp ((measurable_modulus.coe_nnreal_real).pow_const a))

/- English proof (translation)
Use `measurable_of_continuousOn_compl_singleton (0 : F) ?_` and prove the remaining obligations. Introduce `t ht`. Establish `ht0 : t ≠ 0` using `ht`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Take `⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = t` from `⟨Units.mk0 t ht0, rfl⟩`.

Rewrite using `[← (isOpenEmbedding_units_val (K := F)).continuousAt_iff]`. Establish `: chF c s ∘ (Units.val : Fˣ → F) = fun u => ((c u : ℂˣ) : ℂ) * mp u s`. Use function extensionality and compare the values at `(chF_coe c s)`. Rewrite using `[this]`. Conclude with `(continuous_char_units hc s).continuousAt`.
-/
theorem measurable_chF {c : Fˣ →* ℂˣ} (hc : Continuous c) (s : ℂ) : Measurable (chF c s) := by
  refine measurable_of_continuousOn_compl_singleton (0 : F) ?_
  intro t ht
  have ht0 : t ≠ 0 := ht
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = t := ⟨Units.mk0 t ht0, rfl⟩
  rw [← (isOpenEmbedding_units_val (K := F)).continuousAt_iff]
  have : chF c s ∘ (Units.val : Fˣ → F) = fun u => ((c u : ℂˣ) : ℂ) * mp u s :=
    funext (chF_coe c s)
  rw [this]
  exact (continuous_char_units hc s).continuousAt

/- English proof (translation)
Establish `hPm : MeasurableSet (valBall F n : Set F)` using `measurableSet_valBall n`. Establish `hχ : quasiCharExponent (1 : Fˣ →* ℂˣ) = 0` using `by simp [quasiCharExponent]`. Establish `hi` using `integrable_localZeta (indicator_valBall_mem_schwartzBruhat (K := F) n) (χ := 1) continuous_one (s := ((a + 1 : ℝ) : ℂ)) (by rw [hχ]; simp; linarith)`. Establish `hgm : Measurable ((valBall F n : Set F).indicator (ePow (a + 1)))` using `(measurable_ePow _).indicator hPm`. Establish `h1 : ∫⁻ u : Fˣ, (valBall F n : Set F).indicator (ePow (a + 1)) (u : F) ∂multHaar F < ∞`.

Use `lt_of_eq_of_lt (lintegral_congr fun u => ?_) hi.2` and prove the remaining obligations. Use `beta_reduce`. Distinguish the cases in `hu : (u : F) ∈ (valBall F n : Set F)`. Rewrite using `[Set.indicator_of_mem hu, Set.indicator_of_mem hu, ePow_of_ne _ u.ne_zero, ← ofReal_norm]`. Simplify using `only [MonoidHom.one_apply, Units.val_one, mul_one, one_mul]`.

Rewrite using `[Complex.norm_cpow_eq_rpow_re_of_pos (modulus_pos_real u.ne_zero)]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[lintegral_multHaar hgm]`.

Establish `h2 : ∫⁻ x in ({0}ᶜ : Set F), ((modulus x : ℝ≥0∞))⁻¹ * (valBall F n : Set F).indicator (ePow (a + 1)) x ∂haarIntegers F < ∞`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_lt, top_le_iff]`. Rewrite `h1` using `[h, ENNReal.mul_top multHaarConst_ne_zero]`. Conclude with `lt_irrefl _ h1`.

Use `lt_of_le_of_lt ?_ h2` and prove the remaining obligations. Rewrite using `[← lintegral_indicator hPm, ← lintegral_indicator (measurableSet_singleton (0 : F)).compl]`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality.

Simplify using `[ePow_zero]`. Rewrite using `[Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set F) from hx)]`. Distinguish the cases in `hxP : x ∈ (valBall F n : Set F)`. Rewrite using `[Set.indicator_of_mem hxP, Set.indicator_of_mem hxP, ePow_of_ne _ hx, ePow_of_ne _ hx]`. Establish `hm` using `modulus_pos_real hx`.

Rewrite using `[← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_inv_of_pos hm, ← ENNReal.ofReal_mul (by positivity), Real.rpow_add hm, Real.rpow_one]`. Use `le_of_eq ?_` and prove the remaining obligations. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Set.indicator_of_notMem hxP, Set.indicator_of_notMem hxP]`.

Simplify using the standard rewrite rules.
-/
theorem setLIntegral_ePow_haar_lt_top {a : ℝ} (ha : -1 < a) (n : ℤ) :
    ∫⁻ t in (valBall F n : Set F), ePow a t ∂haarIntegers F < ∞ := by
  have hPm : MeasurableSet (valBall F n : Set F) := measurableSet_valBall n
  have hχ : quasiCharExponent (1 : Fˣ →* ℂˣ) = 0 := by simp [quasiCharExponent]
  have hi := integrable_localZeta (indicator_valBall_mem_schwartzBruhat (K := F) n) (χ := 1)
    continuous_one (s := ((a + 1 : ℝ) : ℂ)) (by rw [hχ]; simp; linarith)
  have hgm : Measurable ((valBall F n : Set F).indicator (ePow (a + 1))) :=
    (measurable_ePow _).indicator hPm
  have h1 : ∫⁻ u : Fˣ, (valBall F n : Set F).indicator (ePow (a + 1)) (u : F) ∂multHaar F < ∞ := by
    refine lt_of_eq_of_lt (lintegral_congr fun u => ?_) hi.2
    beta_reduce
    by_cases hu : (u : F) ∈ (valBall F n : Set F)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ePow_of_ne _ u.ne_zero, ← ofReal_norm]
      simp only [MonoidHom.one_apply, Units.val_one, mul_one, one_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (modulus_pos_real u.ne_zero)]
      simp
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
      simp
  rw [lintegral_multHaar hgm] at h1
  have h2 : ∫⁻ x in ({0}ᶜ : Set F), ((modulus x : ℝ≥0∞))⁻¹ *
      (valBall F n : Set F).indicator (ePow (a + 1)) x ∂haarIntegers F < ∞ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.mul_top multHaarConst_ne_zero] at h1
    exact lt_irrefl _ h1
  refine lt_of_le_of_lt ?_ h2
  rw [← lintegral_indicator hPm, ← lintegral_indicator (measurableSet_singleton (0 : F)).compl]
  refine lintegral_mono fun x => ?_
  by_cases hx : x = 0
  · subst hx
    simp [ePow_zero]
  rw [Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set F) from hx)]
  by_cases hxP : x ∈ (valBall F n : Set F)
  · rw [Set.indicator_of_mem hxP, Set.indicator_of_mem hxP, ePow_of_ne _ hx, ePow_of_ne _ hx]
    have hm := modulus_pos_real hx
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_inv_of_pos hm,
      ← ENNReal.ofReal_mul (by positivity), Real.rpow_add hm, Real.rpow_one]
    refine le_of_eq ?_
    congr 1
    field_simp
  · rw [Set.indicator_of_notMem hxP, Set.indicator_of_notMem hxP]
    simp

/- English proof (translation)
Rewrite using `[selfDualMeasure, Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]`. Conclude with `ENNReal.mul_lt_top ENNReal.coe_lt_top (setLIntegral_ePow_haar_lt_top ha n)`.
-/
theorem setLIntegral_ePow_lt_top (ψ : AddChar F Circle) {a : ℝ} (ha : -1 < a) (n : ℤ) :
    ∫⁻ t in (valBall F n : Set F), ePow a t ∂selfDualMeasure ψ < ∞ := by
  rw [selfDualMeasure, Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (setLIntegral_ePow_haar_lt_top ha n)

/- English proof (translation)
Use `set b : F := u⁻¹ * w * y₁ with hb`. Establish `hbm : b ∈ valBall F n`. Establish `h1 : u⁻¹ * w ∈ valBall F 0`. Rewrite using `[mem_valBall_zero_iff, ← modulus_le_one_iff, modulus_mul, modulus_inv]`. Conclude with `inv_mul_le_one_of_le₀ hle (by simp)`.

Simplify using `using mul_mem_valBall h1 hy`. Establish `hmp` using `measurePreserving_sub_right μ b`. Establish `hpre : (fun y => y - b) ⁻¹' (valBall F n : Set F) = valBall F n`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe]`.

Conclude with `⟨fun h => by simpa using add_mem h hbm, fun h => sub_mem h hbm⟩`. Establish `e : ∀ y, ePow a (u * y - w * y₁) = ePow a u * ePow a (y - b)`. Introduce `y`. Rewrite using `[← ePow_mul]`. Use `congr 1`.

Simplify using `only [hb]`. Clear the denominators using the available nonvanishing facts. Repeatedly rewrite using `[e]`. Establish `hmb : Measurable fun y => ePow a (y - b)` using `(measurable_ePow a).comp (measurable_sub_const b)`. Rewrite using `[lintegral_const_mul _ hmb]`.

Use `congr 1`. Use `hmp.setLIntegral_comp_preimage (measurableSet_valBall n) (measurable_ePow a)` as an intermediate fact. Rewrite `this` using `[hpre]`. Then use the resulting hypothesis.
-/
theorem setLIntegral_ePow_shift (μ : Measure F) [μ.IsAddHaarMeasure] (a : ℝ) (n : ℤ) {u w y₁ : F}
    (hu : u ≠ 0) (hle : modulus w ≤ modulus u) (hy : y₁ ∈ valBall F n) :
    ∫⁻ y in (valBall F n : Set F), ePow a (u * y - w * y₁) ∂μ =
      ePow a u * ∫⁻ y in (valBall F n : Set F), ePow a y ∂μ := by
  set b : F := u⁻¹ * w * y₁ with hb
  have hbm : b ∈ valBall F n := by
    have h1 : u⁻¹ * w ∈ valBall F 0 := by
      rw [mem_valBall_zero_iff, ← modulus_le_one_iff, modulus_mul, modulus_inv]
      exact inv_mul_le_one_of_le₀ hle (by simp)
    simpa using mul_mem_valBall h1 hy
  have hmp := measurePreserving_sub_right μ b
  have hpre : (fun y => y - b) ⁻¹' (valBall F n : Set F) = valBall F n := by
    ext y
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun h => by simpa using add_mem h hbm, fun h => sub_mem h hbm⟩
  have e : ∀ y, ePow a (u * y - w * y₁) = ePow a u * ePow a (y - b) := by
    intro y
    rw [← ePow_mul]
    congr 1
    simp only [hb]
    field_simp
  simp_rw [e]
  have hmb : Measurable fun y => ePow a (y - b) := (measurable_ePow a).comp (measurable_sub_const b)
  rw [lintegral_const_mul _ hmb]
  congr 1
  have := hmp.setLIntegral_comp_preimage (measurableSet_valBall n) (measurable_ePow a)
  rwa [hpre] at this

def Jint (μ : Measure F) (a : ℝ) (n : ℤ) (u₁ u₃ : F) : ℝ≥0∞ :=
  ∫⁻ y₁ in (valBall F n : Set F), ∫⁻ y₃ in (valBall F n : Set F), ePow a (u₁ * y₃ - u₃ * y₁) ∂μ ∂μ

/- English proof (translation)
Unfold `Jint`. Rewrite using `[setLIntegral_congr_fun (measurableSet_valBall n) (fun y hy => setLIntegral_ePow_shift μ a n h₁ hle hy), setLIntegral_const]`.
-/
theorem Jint_of_le (μ : Measure F) [μ.IsAddHaarMeasure] (a : ℝ) (n : ℤ) {u₁ u₃ : F} (h₁ : u₁ ≠ 0)
    (hle : modulus u₃ ≤ modulus u₁) :
    Jint μ a n u₁ u₃ = ePow a u₁ * (∫⁻ y in (valBall F n : Set F), ePow a y ∂μ) * μ (valBall F n) := by
  unfold Jint
  rw [setLIntegral_congr_fun (measurableSet_valBall n)
    (fun y hy => setLIntegral_ePow_shift μ a n h₁ hle hy), setLIntegral_const]

/- English proof (translation)
Unfold `Jint`. Rewrite using `[lintegral_lintegral_swap]`. Use `lintegral_congr fun y₃ => lintegral_congr fun y₁ => ?_` and prove the remaining obligations. Rewrite using `[← ePow_neg]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `Measurable.aemeasurable ?_` and prove the remaining obligations. Conclude with `(measurable_ePow a).comp (by fun_prop)`.
-/
theorem Jint_symm (μ : Measure F) [μ.IsAddHaarMeasure] (a : ℝ) (n : ℤ) (u₁ u₃ : F) :
    Jint μ a n u₁ u₃ = Jint μ a n u₃ u₁ := by
  unfold Jint
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun y₃ => lintegral_congr fun y₁ => ?_
    rw [← ePow_neg]
    congr 1
    ring
  · refine Measurable.aemeasurable ?_
    exact (measurable_ePow a).comp (by fun_prop)

/- English proof (translation)
Establish `key : ∀ {x z : F}, x ≠ 0 → z ≠ 0 → modulus z ≤ modulus x → ePow (-σ) x ≤ ePow (-(σ / 2)) x * ePow (-(σ / 2)) z`. Introduce `x z hx hz h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ePow_mul_ePow]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ePow (-(σ / 2)) x * ePow (-(σ / 2)) z := by gcongr`. Conclude with `ePow_anti (by linarith) hz hx h`. Break down `le_total (modulus u₃) (modulus u₁) with h | h` into its components or cases. Rewrite using `[Jint_of_le μ _ n h₁ h]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc]`. Use `_ ≤ _ := by`. Rewrite using `[mul_comm]`. Use `gcongr`.

Conclude with `key h₁ h₃ h`. Rewrite using `[Jint_symm, Jint_of_le μ _ n h₃ h]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc]`. Use `_ ≤ _ := by`.

Rewrite using `[mul_comm, mul_comm (ePow (-(σ / 2)) u₁)]`. Use `gcongr`. Conclude with `key h₃ h₁ h`.
-/
theorem Jint_le (μ : Measure F) [μ.IsAddHaarMeasure] {σ : ℝ} (hσ : 0 ≤ σ) (n : ℤ) {u₁ u₃ : F}
    (h₁ : u₁ ≠ 0) (h₃ : u₃ ≠ 0) :
    Jint μ (-σ) n u₁ u₃ ≤ ((∫⁻ y in (valBall F n : Set F), ePow (-σ) y ∂μ) * μ (valBall F n)) *
      (ePow (-(σ / 2)) u₁ * ePow (-(σ / 2)) u₃) := by
  have key : ∀ {x z : F}, x ≠ 0 → z ≠ 0 → modulus z ≤ modulus x →
      ePow (-σ) x ≤ ePow (-(σ / 2)) x * ePow (-(σ / 2)) z := by
    intro x z hx hz h
    calc ePow (-σ) x = ePow (-(σ / 2)) x * ePow (-(σ / 2)) x := by
          rw [ePow_mul_ePow]; congr 1; ring
      _ ≤ ePow (-(σ / 2)) x * ePow (-(σ / 2)) z := by
          gcongr
          exact ePow_anti (by linarith) hz hx h
  rcases le_total (modulus u₃) (modulus u₁) with h | h
  · rw [Jint_of_le μ _ n h₁ h]
    calc _ = ePow (-σ) u₁ * ((∫⁻ y in (valBall F n : Set F), ePow (-σ) y ∂μ) * μ (valBall F n)) := by
          rw [mul_assoc]
      _ ≤ _ := by
          rw [mul_comm]
          gcongr
          exact key h₁ h₃ h
  · rw [Jint_symm, Jint_of_le μ _ n h₃ h]
    calc _ = ePow (-σ) u₃ * ((∫⁻ y in (valBall F n : Set F), ePow (-σ) y ∂μ) * μ (valBall F n)) := by
          rw [mul_assoc]
      _ ≤ _ := by
          rw [mul_comm, mul_comm (ePow (-(σ / 2)) u₁)]
          gcongr
          exact key h₃ h₁ h

def Kc (σ : ℝ) (q : (F × F) × (F × F)) : ℝ≥0∞ :=
  ePow (σ - 1) q.1.1 * ePow (σ - 1) q.2.1 * ePow (-σ) (q.1.1 * q.2.2 - q.2.1 * q.1.2)

/- English proof (translation)
Unfold `Kc`. Conclude with `(((measurable_ePow _).comp (by fun_prop)).mul ((measurable_ePow _).comp (by fun_prop))).mul ((measurable_ePow _).comp (by fun_prop))`.
-/
theorem measurable_Kc (σ : ℝ) : Measurable (Kc σ : (F × F) × (F × F) → ℝ≥0∞) := by
  unfold Kc
  exact (((measurable_ePow _).comp (by fun_prop)).mul ((measurable_ePow _).comp (by fun_prop))).mul
    ((measurable_ePow _).comp (by fun_prop))

/- English proof (translation)
Use `set μ := selfDualMeasure ψ with hμ`. Use `set ν := μ.restrict (valBall F n : Set F) with hν`. Establish `hK` using `measurable_Kc (F := F) σ`. Use `set C : ℝ≥0∞ := (∫⁻ y in (valBall F n : Set F), ePow (-σ) y ∂μ) * μ (valBall F n) with hC`. Establish `hCfin : C < ∞` using `ENNReal.mul_lt_top (setLIntegral_ePow_lt_top ψ (by linarith) n) (isCompact_valBall n).measure_lt_top`.

Use `set h : F → ℝ≥0∞ := ePow (σ - 1 + -(σ / 2)) with hh`. Establish `hhm : Measurable h` using `measurable_ePow _`. Establish `hI : ∫⁻ t, h t ∂ν < ∞` using `setLIntegral_ePow_lt_top ψ (by linarith) n`. Establish `step1 : ∫⁻ q, Kc σ q ∂(ν.prod ν).prod (ν.prod ν) = ∫⁻ u₁, ∫⁻ y₁, ∫⁻ u₃, ∫⁻ y₃, Kc σ ((u₁, y₁), (u₃, y₃)) ∂ν ∂ν ∂ν ∂ν`. Rewrite using `[lintegral_prod _ hK.aemeasurable, lintegral_prod _ (hK.lintegral_prod_right').aemeasurable]`.

Use `lintegral_congr fun u₁ => lintegral_congr fun y₁ => ?_` and prove the remaining obligations. Conclude with `lintegral_prod _ (hK.comp measurable_prodMk_left).aemeasurable`. Establish `step2 : ∀ u₁, ∫⁻ y₁, ∫⁻ u₃, ∫⁻ y₃, Kc σ ((u₁, y₁), (u₃, y₃)) ∂ν ∂ν ∂ν = ∫⁻ u₃, ePow (σ - 1) u₁ * ePow (σ - 1) u₃ * Jint μ (-σ) n u₁ u₃ ∂ν`. Introduce `u₁`. Rewrite using `[lintegral_lintegral_swap]`.

Use `lintegral_congr fun u₃ => ?_` and prove the remaining obligations. Simplify using `only [Kc]`. Unfold `Jint`. Establish `hm : ∀ y₁ : F, Measurable fun y₃ : F => ePow (-σ) (u₁ * y₃ - u₃ * y₁)` using `fun y₁ => (measurable_ePow _).comp (by fun_prop)`. Repeatedly rewrite using `[lintegral_const_mul _ (hm _)]`.

Rewrite using `[lintegral_const_mul]`. Establish `: Measurable fun z : F × F => ePow (-σ) (u₁ * z.2 - u₃ * z.1)` using `(measurable_ePow _).comp (by fun_prop)`. Conclude with `this.lintegral_prod_right'`. Use `Measurable.aemeasurable ?_` and prove the remaining obligations. Establish `: Measurable fun w : (F × F) × F => Kc σ ((u₁, w.1.1), (w.1.2, w.2))` using `hK.comp (by fun_prop)`.

Conclude with `this.lintegral_prod_right'`. Establish `step3 : ∀ u₁ u₃ : F, ePow (σ - 1) u₁ * ePow (σ - 1) u₃ * Jint μ (-σ) n u₁ u₃ ≤ C * h u₁ * h u₃`. Introduce `u₁ u₃`. Distinguish the cases in `h₁ : u₁ = 0`. Simplify using `[h₁, ePow_zero]`.

Distinguish the cases in `h₃ : u₃ = 0`. Simplify using `[h₃, ePow_zero]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Jint_le μ h0.le n h₁ h₃`. Use `_ = C * (ePow (σ - 1) u₁ * ePow (-(σ / 2)) u₁) * (ePow (σ - 1) u₃ * ePow (-(σ / 2)) u₃) := by`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = C * h u₁ * h u₃ := by`. Rewrite using `[ePow_mul_ePow, ePow_mul_ePow]`. Rewrite using `[step1]`. Repeatedly rewrite using `[step2]`.

Combine the equalities or inequalities in the displayed calculation. Establish `e1 : ∀ u₁, ∫⁻ u₃, C * h u₁ * h u₃ ∂ν = C * (∫⁻ t, h t ∂ν) * h u₁`. Introduce `u₁`. Rewrite using `[lintegral_const_mul _ hhm]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[e1]`. Rewrite using `[lintegral_const_mul _ hhm]`. Use `_ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hCfin hI) hI`.
-/
theorem lintegral_Kc_lt_top (ψ : AddChar F Circle) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (n : ℤ) :
    ∫⁻ q, Kc σ q ∂(((selfDualMeasure ψ).restrict (valBall F n : Set F)).prod
        ((selfDualMeasure ψ).restrict (valBall F n : Set F))).prod
      (((selfDualMeasure ψ).restrict (valBall F n : Set F)).prod
        ((selfDualMeasure ψ).restrict (valBall F n : Set F))) < ∞ := by
  set μ := selfDualMeasure ψ with hμ
  set ν := μ.restrict (valBall F n : Set F) with hν
  have hK := measurable_Kc (F := F) σ
  set C : ℝ≥0∞ := (∫⁻ y in (valBall F n : Set F), ePow (-σ) y ∂μ) * μ (valBall F n) with hC
  have hCfin : C < ∞ := ENNReal.mul_lt_top (setLIntegral_ePow_lt_top ψ (by linarith) n)
    (isCompact_valBall n).measure_lt_top
  set h : F → ℝ≥0∞ := ePow (σ - 1 + -(σ / 2)) with hh
  have hhm : Measurable h := measurable_ePow _
  have hI : ∫⁻ t, h t ∂ν < ∞ := setLIntegral_ePow_lt_top ψ (by linarith) n
  have step1 : ∫⁻ q, Kc σ q ∂(ν.prod ν).prod (ν.prod ν) =
      ∫⁻ u₁, ∫⁻ y₁, ∫⁻ u₃, ∫⁻ y₃, Kc σ ((u₁, y₁), (u₃, y₃)) ∂ν ∂ν ∂ν ∂ν := by
    rw [lintegral_prod _ hK.aemeasurable, lintegral_prod _ (hK.lintegral_prod_right').aemeasurable]
    refine lintegral_congr fun u₁ => lintegral_congr fun y₁ => ?_
    exact lintegral_prod _ (hK.comp measurable_prodMk_left).aemeasurable
  have step2 : ∀ u₁, ∫⁻ y₁, ∫⁻ u₃, ∫⁻ y₃, Kc σ ((u₁, y₁), (u₃, y₃)) ∂ν ∂ν ∂ν =
      ∫⁻ u₃, ePow (σ - 1) u₁ * ePow (σ - 1) u₃ * Jint μ (-σ) n u₁ u₃ ∂ν := by
    intro u₁
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun u₃ => ?_
      simp only [Kc]
      unfold Jint
      have hm : ∀ y₁ : F, Measurable fun y₃ : F => ePow (-σ) (u₁ * y₃ - u₃ * y₁) :=
        fun y₁ => (measurable_ePow _).comp (by fun_prop)
      simp_rw [lintegral_const_mul _ (hm _)]
      rw [lintegral_const_mul]
      have : Measurable fun z : F × F => ePow (-σ) (u₁ * z.2 - u₃ * z.1) :=
        (measurable_ePow _).comp (by fun_prop)
      exact this.lintegral_prod_right'
    · refine Measurable.aemeasurable ?_
      have : Measurable fun w : (F × F) × F => Kc σ ((u₁, w.1.1), (w.1.2, w.2)) :=
        hK.comp (by fun_prop)
      exact this.lintegral_prod_right'
  have step3 : ∀ u₁ u₃ : F, ePow (σ - 1) u₁ * ePow (σ - 1) u₃ * Jint μ (-σ) n u₁ u₃ ≤
      C * h u₁ * h u₃ := by
    intro u₁ u₃
    by_cases h₁ : u₁ = 0
    · simp [h₁, ePow_zero]
    by_cases h₃ : u₃ = 0
    · simp [h₃, ePow_zero]
    calc _ ≤ ePow (σ - 1) u₁ * ePow (σ - 1) u₃ *
          (C * (ePow (-(σ / 2)) u₁ * ePow (-(σ / 2)) u₃)) := by
          gcongr
          exact Jint_le μ h0.le n h₁ h₃
      _ = C * (ePow (σ - 1) u₁ * ePow (-(σ / 2)) u₁) * (ePow (σ - 1) u₃ * ePow (-(σ / 2)) u₃) := by
          ring
      _ = C * h u₁ * h u₃ := by
          rw [ePow_mul_ePow, ePow_mul_ePow]
  rw [step1]
  simp_rw [step2]
  calc _ ≤ ∫⁻ u₁, ∫⁻ u₃, C * h u₁ * h u₃ ∂ν ∂ν :=
        lintegral_mono fun u₁ => lintegral_mono fun u₃ => step3 u₁ u₃
    _ = C * (∫⁻ t, h t ∂ν) * (∫⁻ t, h t ∂ν) := by
        have e1 : ∀ u₁, ∫⁻ u₃, C * h u₁ * h u₃ ∂ν = C * (∫⁻ t, h t ∂ν) * h u₁ := by
          intro u₁
          rw [lintegral_const_mul _ hhm]
          ring
        simp_rw [e1]
        rw [lintegral_const_mul _ hhm]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hCfin hI) hI

end Meas

/- English proof (translation)
Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Establish `: ⇑(α * β) = fun x => α x * β x`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `hα.1.mul hβ.1`. Simplify using `[hα.2, hβ.2]`.
-/
theorem isUnit1_mul {α β : Fˣ →* ℂˣ} (hα : IsUnit1 α) (hβ : IsUnit1 β) : IsUnit1 (α * β) := by
  refine ⟨?_, fun x => ?_⟩
  · have : ⇑(α * β) = fun x => α x * β x := by
      funext x; simp
    rw [this]
    exact hα.1.mul hβ.1
  · simp [hα.2, hβ.2]

/- English proof (translation)
Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Establish `: ⇑(α⁻¹) = fun x => (α x)⁻¹`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `hα.1.inv`. Simplify using `[hα.2]`.
-/
theorem isUnit1_inv {α : Fˣ →* ℂˣ} (hα : IsUnit1 α) : IsUnit1 α⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · have : ⇑(α⁻¹) = fun x => (α x)⁻¹ := by
      funext x; simp
    rw [this]
    exact hα.1.inv
  · simp [hα.2]

/- English proof (translation)
Simplify using `[dt]`.
-/
theorem dt_zero_one (r : Fin 2 → F) : dt r ![0, 1] = r 0 := by simp [dt]

section Meas2

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Unfold `dt`. Use `fun_prop`.
-/
theorem measurable_dt : Measurable (fun q : (Fin 2 → F) × (Fin 2 → F) => dt q.1 q.2) := by
  unfold dt
  fun_prop

/- English proof (translation)
Establish `a1 : Measurable fun p : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => dt p.2.1 p.1` using `measurable_dt.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)`. Establish `a2 : Measurable fun p : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => dt p.2.2 p.1` using `measurable_dt.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)`. Establish `a3 : Measurable fun p : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => dt p.2.1 p.2.2` using `measurable_dt.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))`. Establish `f1` using `(measurable_chF (isUnit1_mul hν hc).1 (s - 1)).comp a1`. Establish `f2` using `(measurable_chF (isUnit1_mul (isUnit1_inv hν) hc).1 (s - 1)).comp a2`.

Establish `f3` using `(measurable_chF (isUnit1_inv hc).1 (-s)).comp a3`. Conclude with `(f1.mul f2).mul f3`.
-/
theorem measurable_Kr {ν c : Fˣ →* ℂˣ} (hν : IsUnit1 ν) (hc : IsUnit1 c) (s : ℂ) :
    Measurable (fun p : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => Kr ν c s p.2.1 p.1 p.2.2) := by
  have a1 : Measurable fun p : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => dt p.2.1 p.1 :=
    measurable_dt.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  have a2 : Measurable fun p : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => dt p.2.2 p.1 :=
    measurable_dt.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
  have a3 : Measurable fun p : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => dt p.2.1 p.2.2 :=
    measurable_dt.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
  have f1 := (measurable_chF (isUnit1_mul hν hc).1 (s - 1)).comp a1
  have f2 := (measurable_chF (isUnit1_mul (isUnit1_inv hν) hc).1 (s - 1)).comp a2
  have f3 := (measurable_chF (isUnit1_inv hc).1 (-s)).comp a3
  exact (f1.mul f2).mul f3

/- English proof (translation)
Establish `e : dt r₁ r₃ = r₁ 0 * r₃ 1 - r₃ 0 * r₁ 1`. Simplify using `only [dt]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Kr, enorm_mul, enorm_mul, enorm_chF (isUnit1_mul hν hc).2, enorm_chF (isUnit1_mul (isUnit1_inv hν) hc).2, enorm_chF (isUnit1_inv hc).2, dt_zero_one, dt_zero_one, e, Kc]`. Simplify using `only [Complex.sub_re, Complex.one_re, Complex.neg_re]`.
-/
theorem enorm_Kr {ν c : Fˣ →* ℂˣ} (hν : IsUnit1 ν) (hc : IsUnit1 c) (s : ℂ) (r₁ r₃ : Fin 2 → F) :
    ‖Kr ν c s r₁ ![0, 1] r₃‖ₑ = Kc s.re ((r₁ 0, r₁ 1), (r₃ 0, r₃ 1)) := by
  have e : dt r₁ r₃ = r₁ 0 * r₃ 1 - r₃ 0 * r₁ 1 := by
    simp only [dt]
    ring
  rw [Kr, enorm_mul, enorm_mul, enorm_chF (isUnit1_mul hν hc).2,
    enorm_chF (isUnit1_mul (isUnit1_inv hν) hc).2, enorm_chF (isUnit1_inv hc).2, dt_zero_one,
    dt_zero_one, e, Kc]
  simp only [Complex.sub_re, Complex.one_re, Complex.neg_re]

/- English proof (translation)
Establish `e` using `measurePreserving_finTwoArrow ρ`. Conclude with `(e.prod e).lintegral_comp (measurable_Kc σ)`.
-/
theorem lintegral_pi_Kc (ρ : Measure F) [SigmaFinite ρ] (σ : ℝ) :
    ∫⁻ p : (Fin 2 → F) × (Fin 2 → F), Kc σ ((p.1 0, p.1 1), (p.2 0, p.2 1))
        ∂(Measure.pi fun _ : Fin 2 => ρ).prod (Measure.pi fun _ : Fin 2 => ρ) =
      ∫⁻ q, Kc σ q ∂(ρ.prod ρ).prod (ρ.prod ρ) := by
  have e := measurePreserving_finTwoArrow ρ
  exact (e.prod e).lintegral_comp (measurable_Kc σ)

/- English proof (translation)
Establish `a1 : Measurable fun p : (Fin 2 → F) × (Fin 2 → F) => dt p.1 (![0, 1] : Fin 2 → F)`. Simplify using `only [dt_zero_one]`. Conclude with `(measurable_pi_apply 0).comp measurable_fst`. Establish `a2 : Measurable fun p : (Fin 2 → F) × (Fin 2 → F) => dt p.2 (![0, 1] : Fin 2 → F)`. Simplify using `only [dt_zero_one]`.

Conclude with `(measurable_pi_apply 0).comp measurable_snd`. Establish `f1` using `(measurable_chF (isUnit1_mul hν hc).1 (s - 1)).comp a1`. Establish `f2` using `(measurable_chF (isUnit1_mul (isUnit1_inv hν) hc).1 (s - 1)).comp a2`. Establish `f3` using `(measurable_chF (isUnit1_inv hc).1 (-s)).comp (measurable_dt (F := F))`. Establish `hm : Measurable (fun p : (Fin 2 → F) × (Fin 2 → F) => Kr ν c s p.1 ![0, 1] p.2)` using `(f1.mul f2).mul f3`.

Use `⟨hm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `h` using `lintegral_Kc_lt_top ψ hs.1 hs.2 n`. Rewrite `h` using `[← lintegral_pi_Kc]`. Conclude with `lt_of_eq_of_lt (lintegral_congr fun p => enorm_Kr hν hc s p.1 p.2) h`.
-/
theorem integrable_Kr (ψ : AddChar F Circle) {ν c : Fˣ →* ℂˣ} (hν : IsUnit1 ν) (hc : IsUnit1 c)
    {s : ℂ} (hs : Strip s) (n : ℤ) :
    Integrable (fun p : (Fin 2 → F) × (Fin 2 → F) => Kr ν c s p.1 ![0, 1] p.2)
      ((Measure.pi fun _ : Fin 2 => (selfDualMeasure ψ).restrict (valBall F n : Set F)).prod
        (Measure.pi fun _ : Fin 2 => (selfDualMeasure ψ).restrict (valBall F n : Set F))) := by
  have a1 : Measurable fun p : (Fin 2 → F) × (Fin 2 → F) => dt p.1 (![0, 1] : Fin 2 → F) := by
    simp only [dt_zero_one]
    exact (measurable_pi_apply 0).comp measurable_fst
  have a2 : Measurable fun p : (Fin 2 → F) × (Fin 2 → F) => dt p.2 (![0, 1] : Fin 2 → F) := by
    simp only [dt_zero_one]
    exact (measurable_pi_apply 0).comp measurable_snd
  have f1 := (measurable_chF (isUnit1_mul hν hc).1 (s - 1)).comp a1
  have f2 := (measurable_chF (isUnit1_mul (isUnit1_inv hν) hc).1 (s - 1)).comp a2
  have f3 := (measurable_chF (isUnit1_inv hc).1 (-s)).comp (measurable_dt (F := F))
  have hm : Measurable (fun p : (Fin 2 → F) × (Fin 2 → F) => Kr ν c s p.1 ![0, 1] p.2) :=
    (f1.mul f2).mul f3
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have h := lintegral_Kc_lt_top ψ hs.1 hs.2 n
  rw [← lintegral_pi_Kc] at h
  exact lt_of_eq_of_lt (lintegral_congr fun p => enorm_Kr hν hc s p.1 p.2) h

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_box hB`. Use `IntegrableOn.mono_set ?_ (Set.prod_mono hn hn)` and prove the remaining obligations. Establish `h` using `integrable_Kr ψ hν hc hs n`. Rewrite `h` using `[← Measure.restrict_pi_pi, Measure.prod_restrict]`. Conclude with `h`.
-/
theorem integrableOn_Kr (ψ : AddChar F Circle) {ν c : Fˣ →* ℂˣ} (hν : IsUnit1 ν) (hc : IsUnit1 c)
    {s : ℂ} (hs : Strip s) {B : Set (Fin 2 → F)} (hB : IsCompact B) :
    IntegrableOn (fun p : (Fin 2 → F) × (Fin 2 → F) => Kr ν c s p.1 ![0, 1] p.2)
      (B ×ˢ B) ((m2 ψ).prod (m2 ψ)) := by
  obtain ⟨n, hn⟩ := exists_box hB
  refine IntegrableOn.mono_set ?_ (Set.prod_mono hn hn)
  have h := integrable_Kr ψ hν hc hs n
  rw [← Measure.restrict_pi_pi, Measure.prod_restrict] at h
  exact h

end Meas2

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ ν c hν hc s hs`. Conclude with `⟨measurable_Kr hν hc s, fun B hB => integrableOn_Kr ψ hν hc hs hB⟩`.
-/
theorem kernel_integrable : A4 := by
  intro F _ _ _ _ _ _ ψ hψ ν c hν hc s hs
  exact ⟨measurable_Kr hν hc s, fun B hB => integrableOn_Kr ψ hν hc hs hB⟩

end GlobalTheory.CompanionTheory.RankinKernel
