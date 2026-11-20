import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

noncomputable section
namespace GlobalTheory.IntShell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `[nabs, map_pow]`.
-/
theorem nabs_pow' (u : kˣ) (m : ℕ) : nabs k (u ^ m) = nabs k u ^ m := by
  simp [nabs, map_pow]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[k]`. Establish `h0 : (ϖ : k) ≠ 0` using `by simpa using hϖ.ne_zero`. Use `⟨Units.mk0 _ h0, ?_⟩` and prove the remaining obligations. Rewrite using `[nabs_uniformiser hϖ rfl]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_resCard k)`.
-/
theorem exists_unit_nabs_lt_one : ∃ u : kˣ, nabs k u < 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  refine ⟨Units.mk0 _ h0, ?_⟩
  rw [nabs_uniformiser hϖ rfl]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_resCard k)

/- English proof (translation)
Use extensionality with `y`. Simplify using `[cball, Valuation.mem_integer_iff]`.
-/
theorem cball_one : cball (1 : kˣ) = (𝒪[k] : Set k) := by
  ext y; simp [cball, Valuation.mem_integer_iff]

/- English proof (translation)
Rewrite using `[nabs_le_iff]`. Conclude with `h`.
-/
theorem nabs_le_of_mem_cball {u : kˣ} {y : k} (hy : y ≠ 0) (h : y ∈ cball u) :
    nabs k (Units.mk0 y hy) ≤ nabs k u := by
  rw [nabs_le_iff]; exact h

/- English proof (translation)
Rewrite using `[nabs_le_iff]`. Conclude with `(not_le.mp h).le`.
-/
theorem nabs_ge_of_not_mem_cball {u : kˣ} {y : k} (hy : y ≠ 0) (h : y ∉ cball u) :
    nabs k u ≤ nabs k (Units.mk0 y hy) := by
  rw [nabs_le_iff]; exact (not_le.mp h).le

/- English proof (translation)
Establish `hP : ∃ n : ℕ, y ∉ cball (u ^ n)`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (nabs_pos k (Units.mk0 y hy)) hu`. Use `⟨n, fun h => ?_⟩` and prove the remaining obligations. Use `nabs_le_of_mem_cball hy h` as an intermediate fact. Rewrite `this` using `[nabs_pow']`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0 : Nat.find hP ≠ 0`. Introduce `h`. Use `Nat.find_spec hP` as an intermediate fact. Rewrite `this` using `[h, pow_zero, cball_one]`.

Conclude with `this hO`. Take `⟨m, hm⟩` from `Nat.exists_eq_succ_of_ne_zero h0`. Use `⟨m, ?_, ?_⟩` and prove the remaining obligations. Use `Nat.find_min hP (show m < Nat.find hP by omega)` as an intermediate fact. Simplify using `using this`.

Use `Nat.find_spec hP` as an intermediate fact. Rewrite `this` using `[hm]`. Then use the resulting hypothesis.
-/
theorem exists_shell {u : kˣ} (hu : nabs k u < 1) {y : k} (hy : y ≠ 0) (hO : y ∈ 𝒪[k]) :
    ∃ m : ℕ, y ∈ cball (u ^ m) ∧ y ∉ cball (u ^ (m + 1)) := by
  have hP : ∃ n : ℕ, y ∉ cball (u ^ n) := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (nabs_pos k (Units.mk0 y hy)) hu
    refine ⟨n, fun h => ?_⟩
    have := nabs_le_of_mem_cball hy h
    rw [nabs_pow'] at this
    linarith
  have h0 : Nat.find hP ≠ 0 := by
    intro h
    have := Nat.find_spec hP
    rw [h, pow_zero, cball_one] at this
    exact this hO
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
  refine ⟨m, ?_, ?_⟩
  · have := Nat.find_min hP (show m < Nat.find hP by omega)
    simpa using this
  · have := Nat.find_spec hP
    rwa [hm] at this

section Meas
variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_unit_nabs_lt_one (k := k)`. Establish `hle : ∀ m : ℕ, μ {0} ≤ ENNReal.ofReal (nabs k u) ^ m * μ (𝒪[k] : Set k)`. Introduce `m`. Establish `h1 : ({0} : Set k) ⊆ cball (u ^ m)`. Introduce `y hy`.

Rewrite using `[Set.mem_singleton_iff.mp hy]`. Simplify using `[cball]`. Use `(measure_mono h1).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[measure_cball, map_pow]`. Use `congr 1`.

Simplify using `[nabs, ENNReal.ofReal_coe_nnreal]`. Establish `ht : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal (nabs k u) ^ m * μ (𝒪[k] : Set k)) Filter.atTop (nhds (0 * μ (𝒪[k] : Set k)))` using `ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by rw [ENNReal.ofReal_lt_one]; exact hu)) (Or.inr (isCompact_int k).measure_lt_top.ne)`. Rewrite `ht` using `[zero_mul]`. Conclude with `le_antisymm (ge_of_tendsto' ht hle) bot_le`.
-/
theorem measure_zero_singleton (μ : Measure k) [μ.IsAddHaarMeasure] : μ {0} = 0 := by
  obtain ⟨u, hu⟩ := exists_unit_nabs_lt_one (k := k)
  have hle : ∀ m : ℕ, μ {0} ≤ ENNReal.ofReal (nabs k u) ^ m * μ (𝒪[k] : Set k) := by
    intro m
    have h1 : ({0} : Set k) ⊆ cball (u ^ m) := by
      intro y hy; rw [Set.mem_singleton_iff.mp hy]; simp [cball]
    refine (measure_mono h1).trans (le_of_eq ?_)
    rw [measure_cball, map_pow]
    congr 1
    simp [nabs, ENNReal.ofReal_coe_nnreal]
  have ht : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal (nabs k u) ^ m * μ (𝒪[k] : Set k)) Filter.atTop
      (nhds (0 * μ (𝒪[k] : Set k))) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by rw [ENNReal.ofReal_lt_one]; exact hu)) (Or.inr (isCompact_int k).measure_lt_top.ne)
  rw [zero_mul] at ht
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le

end Meas

section Main
variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Establish `hO : μ (𝒪[k] : Set k) < ⊤` using `(isCompact_int k).measure_lt_top`. Break down `le_or_gt 0 s with hs0 | hs0` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ (𝒪[k] : Set k)`.

Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hx]`. Use `ENNReal.rpow_le_one ?_ hs0` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_le_one]`. Use `split_ifs with h`. Conclude with `zero_le_one`.

Conclude with `Model.nabs_le_one _ hx`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]`. Use `_ = μ (𝒪[k] : Set k) := by rw [lintegral_indicator_const (isOpen_int k).measurableSet, one_mul]`. Use `_ < ⊤ := hO`. Take `⟨u, hu⟩` from `exists_unit_nabs_lt_one (k := k)`.

Use `set R := ENNReal.ofReal (nabs k u) with hRdef`. Establish `hR0 : R ≠ 0` using `by rw [hRdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact nabs_pos k u`. Establish `hRt : R ≠ ⊤` using `ENNReal.ofReal_ne_top`. Establish `hR1 : R ^ s * R < 1`. Establish `e : R ^ s * R = R ^ (s + 1)` using `by rw [ENNReal.rpow_add _ _ hR0 hRt, ENNReal.rpow_one]`.

Rewrite using `[e]`. Conclude with `ENNReal.rpow_lt_one (by rw [hRdef, ENNReal.ofReal_lt_one]; exact hu) (by linarith)`. Establish `hRs : R ^ s < ⊤`. Rewrite using `[lt_top_iff_ne_top, ne_eq, ENNReal.rpow_eq_top_iff]`. Introduce and unpack `(⟨h, _⟩ | ⟨h, _⟩)`.

Conclude with `hR0 h`. Conclude with `hRt h`. Establish `hanti : ∀ a b : ℝ≥0∞, a ≤ b → b ^ s ≤ a ^ s`. Introduce `a b h`. Establish `hb : b ^ s = (b ^ (-s))⁻¹` using `by rw [← ENNReal.rpow_neg, neg_neg]`.

Establish `ha : a ^ s = (a ^ (-s))⁻¹` using `by rw [← ENNReal.rpow_neg, neg_neg]`. Rewrite using `[ha, hb]`. Conclude with `ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow h (show (0:ℝ) ≤ -s by linarith))`. Establish `hae : ∀ᵐ y ∂μ, y ∉ ({0} : Set k)` using `measure_eq_zero_iff_ae_notMem.mp (measure_zero_singleton μ)`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_mono_ae (hae.mono fun y hy => ?_)` and prove the remaining obligations. Establish `hy0 : y ≠ 0` using `hy`. Distinguish the cases in `hx : y ∈ (𝒪[k] : Set k)`. Rewrite using `[Set.indicator_of_mem hx, dif_neg hy0]`. Take `⟨m, hm1, hm2⟩` from `exists_shell hu hy0 hx`.

Use `le_trans ?_ (ENNReal.le_tsum m)` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem hm1]`. Use `hanti _ _ (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations. Use `nabs_ge_of_not_mem_cball hy0 hm2` as an intermediate fact. Rewrite `this` using `[nabs_pow']`. Then use the resulting hypothesis.

Rewrite using `[Set.indicator_of_notMem hx]`. Conclude with `bot_le`. Use `_ = ∑' m : ℕ, ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s * μ (cball (u ^ m)) := by`. Rewrite using `[lintegral_tsum fun m => (measurable_const.indicator (isOpen_cball _).measurableSet).aemeasurable]`. Use `congr 1`.

Use function extensionality and compare the values at `m`. Rewrite using `[lintegral_indicator_const (isOpen_cball _).measurableSet]`. Use `_ = ∑' m : ℕ, R ^ s * μ (𝒪[k] : Set k) * (R ^ s * R) ^ m := by`. Use `congr 1`. Use function extensionality and compare the values at `m`.

Establish `hc : ((distribHaarChar k (u ^ m) : NNReal) : ℝ≥0∞) = R ^ m`. Rewrite using `[map_pow, ENNReal.coe_pow, hRdef]`. Use `congr 1`. Simplify using `[nabs, ENNReal.ofReal_coe_nnreal]`. Establish `h2 : ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s = (R ^ s) ^ m * R ^ s`.

Rewrite using `[ENNReal.ofReal_pow (nabs_pos k u).le, ← hRdef, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_comm (((m + 1 : ℕ)) : ℝ) s, ENNReal.rpow_mul, ENNReal.rpow_natCast, pow_succ]`. Rewrite using `[h2, measure_cball, hc, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = R ^ s * μ (𝒪[k] : Set k) * (1 - R ^ s * R)⁻¹ := by`. Rewrite using `[ENNReal.tsum_mul_left, ENNReal.tsum_geometric]`.

Use `_ < ⊤ := by`. Use `ENNReal.mul_lt_top (ENNReal.mul_lt_top hRs hO) ?_` and prove the remaining obligations. Rewrite using `[ENNReal.inv_lt_top]`. Conclude with `tsub_pos_of_lt hR1`.
-/
theorem lintegral_int_nabs_rpow_lt_top (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ) (hs : -1 < s) :
    ∫⁻ x, (𝒪[k] : Set k).indicator
      (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ < ⊤ := by
  have hO : μ (𝒪[k] : Set k) < ⊤ := (isCompact_int k).measure_lt_top
  rcases le_or_gt 0 s with hs0 | hs0
  · calc _ ≤ ∫⁻ x, (𝒪[k] : Set k).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ (𝒪[k] : Set k)
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
            refine ENNReal.rpow_le_one ?_ hs0
            rw [ENNReal.ofReal_le_one]
            split_ifs with h
            · exact zero_le_one
            · exact Model.nabs_le_one _ hx
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      _ = μ (𝒪[k] : Set k) := by rw [lintegral_indicator_const (isOpen_int k).measurableSet, one_mul]
      _ < ⊤ := hO
  ·
    obtain ⟨u, hu⟩ := exists_unit_nabs_lt_one (k := k)
    set R := ENNReal.ofReal (nabs k u) with hRdef
    have hR0 : R ≠ 0 := by rw [hRdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact nabs_pos k u
    have hRt : R ≠ ⊤ := ENNReal.ofReal_ne_top
    have hR1 : R ^ s * R < 1 := by
      have e : R ^ s * R = R ^ (s + 1) := by rw [ENNReal.rpow_add _ _ hR0 hRt, ENNReal.rpow_one]
      rw [e]
      exact ENNReal.rpow_lt_one (by rw [hRdef, ENNReal.ofReal_lt_one]; exact hu) (by linarith)
    have hRs : R ^ s < ⊤ := by
      rw [lt_top_iff_ne_top, ne_eq, ENNReal.rpow_eq_top_iff]
      rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact hR0 h
      · exact hRt h
    have hanti : ∀ a b : ℝ≥0∞, a ≤ b → b ^ s ≤ a ^ s := by
      intro a b h
      have hb : b ^ s = (b ^ (-s))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
      have ha : a ^ s = (a ^ (-s))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
      rw [ha, hb]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow h (show (0:ℝ) ≤ -s by linarith))
    have hae : ∀ᵐ y ∂μ, y ∉ ({0} : Set k) := measure_eq_zero_iff_ae_notMem.mp (measure_zero_singleton μ)
    calc _ ≤ ∫⁻ y, ∑' m : ℕ, (cball (u ^ m)).indicator
            (fun _ => ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s) y ∂μ := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          have hy0 : y ≠ 0 := hy
          by_cases hx : y ∈ (𝒪[k] : Set k)
          · rw [Set.indicator_of_mem hx, dif_neg hy0]
            obtain ⟨m, hm1, hm2⟩ := exists_shell hu hy0 hx
            refine le_trans ?_ (ENNReal.le_tsum m)
            rw [Set.indicator_of_mem hm1]
            refine hanti _ _ (ENNReal.ofReal_le_ofReal ?_)
            have := nabs_ge_of_not_mem_cball hy0 hm2
            rwa [nabs_pow'] at this
          · rw [Set.indicator_of_notMem hx]; exact bot_le
      _ = ∑' m : ℕ, ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s * μ (cball (u ^ m)) := by
          rw [lintegral_tsum fun m => (measurable_const.indicator (isOpen_cball _).measurableSet).aemeasurable]
          congr 1; funext m
          rw [lintegral_indicator_const (isOpen_cball _).measurableSet]
      _ = ∑' m : ℕ, R ^ s * μ (𝒪[k] : Set k) * (R ^ s * R) ^ m := by
          congr 1; funext m
          have hc : ((distribHaarChar k (u ^ m) : NNReal) : ℝ≥0∞) = R ^ m := by
            rw [map_pow, ENNReal.coe_pow, hRdef]
            congr 1
            simp [nabs, ENNReal.ofReal_coe_nnreal]
          have h2 : ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s = (R ^ s) ^ m * R ^ s := by
            rw [ENNReal.ofReal_pow (nabs_pos k u).le, ← hRdef, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
              mul_comm (((m + 1 : ℕ)) : ℝ) s, ENNReal.rpow_mul, ENNReal.rpow_natCast, pow_succ]
          rw [h2, measure_cball, hc, mul_pow]
          ring
      _ = R ^ s * μ (𝒪[k] : Set k) * (1 - R ^ s * R)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ⊤ := by
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hRs hO) ?_
          rw [ENNReal.inv_lt_top]
          exact tsub_pos_of_lt hR1

end Main

end GlobalTheory.IntShell
