import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

def dyShell (n : ℕ) : Set ℝ := {x | x * 2 ^ n ∈ Set.Ico (1 : ℝ) 2}

/- English proof (translation)
The claim follows from `(measurable_id.mul_const ((2 : ℝ) ^ n)) measurableSet_Ico`.
-/
theorem measurableSet_dyShell (n : ℕ) : MeasurableSet (dyShell n) :=
  (measurable_id.mul_const ((2 : ℝ) ^ n)) measurableSet_Ico

/- English proof (translation)
Establish `hex : ∃ m : ℕ, 1 ≤ x * 2 ^ m`. Take `⟨m, hm⟩` from `pow_unbounded_of_one_lt x⁻¹ (one_lt_two : (1 : ℝ) < 2)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use `mul_lt_mul_of_pos_left hm h0` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ h0.ne']`.

Conclude with `this.le`. Establish `hspec` using `Nat.find_spec hex`. Establish `hne : Nat.find hex ≠ 0`. Introduce `h`. Rewrite `hspec` using `[h]`.

Simplify using `at hspec`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero hne`. Establish `hmin : ¬ 1 ≤ x * 2 ^ k` using `Nat.find_min hex (by omega)`. Rewrite `hspec` using `[hk]`.

Use `⟨k, hspec, ?_⟩` and prove the remaining obligations. Establish `: x * 2 ^ (k + 1) = 2 * (x * 2 ^ k)` using `by ring`. Use `show x * 2 ^ (k + 1) < 2`. Rewrite using `[this]`. Combine the linear relations using `[not_le.1 hmin]`.
-/
theorem exists_mem_dyShell {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : ∃ n : ℕ, x ∈ dyShell (n + 1) := by
  have hex : ∃ m : ℕ, 1 ≤ x * 2 ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt x⁻¹ (one_lt_two : (1 : ℝ) < 2)
    refine ⟨m, ?_⟩
    have := mul_lt_mul_of_pos_left hm h0
    rw [mul_inv_cancel₀ h0.ne'] at this
    exact this.le
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    simp at hspec
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin : ¬ 1 ≤ x * 2 ^ k := Nat.find_min hex (by omega)
  rw [hk] at hspec
  refine ⟨k, hspec, ?_⟩
  have : x * 2 ^ (k + 1) = 2 * (x * 2 ^ k) := by ring
  show x * 2 ^ (k + 1) < 2
  rw [this]
  linarith [not_le.1 hmin]

def lowW (H : G2 → ℂ) (σ : ℝ) (g : G2) : ℝ≥0∞ := ‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ)

/- English proof (translation)
The claim follows from `hH.cont.measurable.enorm.mul (ENNReal.measurable_ofReal.comp (measurable_Dt.pow_const σ))`.
-/
theorem measurable_lowW {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) : Measurable (lowW H σ) :=
  hH.cont.measurable.enorm.mul (ENNReal.measurable_ofReal.comp (measurable_Dt.pow_const σ))

/- English proof (translation)
Introduce `γ g` and use `by simp only [lowW, hH.left γ g, Dt_dia]`.
-/
theorem linv_lowW {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) : LInv (lowW H σ) := fun γ g => by
  simp only [lowW, hH.left γ g, Dt_dia]

/- English proof (translation)
Simplify using `only [lowW, hH.cen z g, Dt_dg, hz]`. Rewrite using `[Real.mul_rpow (by norm_num) (Dt_pos g).le, ENNReal.ofReal_mul (by positivity)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lowW_dg {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) {z : Jd} (hz : md z ^ 2 = 1 / 2) (g : G2) :
    lowW H σ (dg2 z z * g) = ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) * lowW H σ g := by
  simp only [lowW, hH.cen z g, Dt_dg, hz]
  rw [Real.mul_rpow (by norm_num) (Dt_pos g).le, ENNReal.ofReal_mul (by positivity)]
  ring

def lowS (H : G2 → ℂ) (σ : ℝ) (n : ℕ) : G2 → ℝ≥0∞ := Set.indicator {g | Dt g ∈ dyShell n} (lowW H σ)

/- English proof (translation)
The claim follows from `(measurable_lowW hH σ).indicator (measurable_Dt (measurableSet_dyShell n))`.
-/
theorem measurable_lowS {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) (n : ℕ) : Measurable (lowS H σ n) :=
  (measurable_lowW hH σ).indicator (measurable_Dt (measurableSet_dyShell n))

/- English proof (translation)
Establish `hm : Dt (dg2 z z * g) ∈ dyShell (n + 1) ↔ Dt g ∈ dyShell n`. Establish `e : 1 / 2 * Dt g * 2 ^ (n + 1) = Dt g * 2 ^ n` using `by ring`. Simplify using `only [dyShell, Set.mem_setOf_eq, Dt_dg, hz, e]`. Distinguish the cases in `h : Dt g ∈ dyShell n`. Rewrite using `[lowS, lowS, Set.indicator_of_mem (show dg2 z z * g ∈ {g | Dt g ∈ dyShell (n + 1)} from hm.2 h), Set.indicator_of_mem (show g ∈ {g | Dt g ∈ dyShell n} from h), lowW_dg hH σ hz]`.

Rewrite using `[lowS, lowS, Set.indicator_of_notMem (show dg2 z z * g ∉ {g | Dt g ∈ dyShell (n + 1)} from fun h' => h (hm.1 h')), Set.indicator_of_notMem (show g ∉ {g | Dt g ∈ dyShell n} from h), mul_zero]`.
-/
theorem lowS_dg {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) {z : Jd} (hz : md z ^ 2 = 1 / 2) (n : ℕ) (g : G2) :
    lowS H σ (n + 1) (dg2 z z * g) = ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) * lowS H σ n g := by
  have hm : Dt (dg2 z z * g) ∈ dyShell (n + 1) ↔ Dt g ∈ dyShell n := by
    have e : 1 / 2 * Dt g * 2 ^ (n + 1) = Dt g * 2 ^ n := by ring
    simp only [dyShell, Set.mem_setOf_eq, Dt_dg, hz, e]
  by_cases h : Dt g ∈ dyShell n
  · rw [lowS, lowS, Set.indicator_of_mem (show dg2 z z * g ∈ {g | Dt g ∈ dyShell (n + 1)} from hm.2 h),
      Set.indicator_of_mem (show g ∈ {g | Dt g ∈ dyShell n} from h), lowW_dg hH σ hz]
  · rw [lowS, lowS, Set.indicator_of_notMem (show dg2 z z * g ∉ {g | Dt g ∈ dyShell (n + 1)} from fun h' => h (hm.1 h')),
      Set.indicator_of_notMem (show g ∉ {g | Dt g ∈ dyShell n} from h), mul_zero]

/- English proof (translation)
Take `⟨C, hC⟩` from `hH.bdd`. Establish `hb : MeasurableSet band`. Establish `: band = {g | Dt g ∈ Set.Ico (1 : ℝ) 2}` using `rfl`. Rewrite using `[this]`. Conclude with `measurable_Dt measurableSet_Ico`.

Establish `hle : ∀ g, lowS H σ 0 g ≤ Set.indicator band (fun _ => ENNReal.ofReal (C * 2 ^ σ)) g`. Introduce `g`. Establish `hiff : g ∈ {g | Dt g ∈ dyShell 0} ↔ g ∈ band` using `by show Dt g * 2 ^ 0 ∈ Set.Ico (1 : ℝ) 2 ↔ (1 ≤ Dt g ∧ Dt g < 2)`. Simplify using the standard rewrite rules. Distinguish the cases in `h : g ∈ band`.

Establish `hs` using `hiff.2 h`. Rewrite using `[lowS, Set.indicator_of_mem hs, Set.indicator_of_mem h, lowW]`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC g)`. Rewrite using `[← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]`. Conclude with `ENNReal.ofReal_le_ofReal (mul_le_mul (hC g) (Real.rpow_le_rpow (Dt_pos g).le h.2.le hσ.le) (by have := Dt_pos g; positivity) hC0)`.

Establish `hs : g ∉ {g | Dt g ∈ dyShell 0}` using `fun h' => h (hiff.1 h')`. Rewrite using `[lowS, Set.indicator_of_notMem hs, Set.indicator_of_notMem h]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_indicator hb, setLIntegral_const, Measure.restrict_apply hb, Set.inter_comm band 𝓕]`. Use `_ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h0.vol`.
-/
theorem lintegral_lowS_zero {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} {H : G2 → ℂ}
    (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ < ∞ := by
  obtain ⟨C, hC⟩ := hH.bdd
  have hb : MeasurableSet band := by
    have : band = {g | Dt g ∈ Set.Ico (1 : ℝ) 2} := rfl
    rw [this]
    exact measurable_Dt measurableSet_Ico
  have hle : ∀ g, lowS H σ 0 g ≤ Set.indicator band (fun _ => ENNReal.ofReal (C * 2 ^ σ)) g := by
    intro g
    have hiff : g ∈ {g | Dt g ∈ dyShell 0} ↔ g ∈ band := by
      show Dt g * 2 ^ 0 ∈ Set.Ico (1 : ℝ) 2 ↔ (1 ≤ Dt g ∧ Dt g < 2)
      simp
    by_cases h : g ∈ band
    · have hs := hiff.2 h
      rw [lowS, Set.indicator_of_mem hs, Set.indicator_of_mem h, lowW]
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC g)
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul (hC g)
        (Real.rpow_le_rpow (Dt_pos g).le h.2.le hσ.le) (by have := Dt_pos g; positivity) hC0)
    · have hs : g ∉ {g | Dt g ∈ dyShell 0} := fun h' => h (hiff.1 h')
      rw [lowS, Set.indicator_of_notMem hs, Set.indicator_of_notMem h]
  calc ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ
      ≤ ∫⁻ g in 𝓕, Set.indicator band (fun _ => ENNReal.ofReal (C * 2 ^ σ)) g ∂μ :=
        lintegral_mono hle
    _ = ENNReal.ofReal (C * 2 ^ σ) * μ (𝓕 ∩ band) := by
        rw [lintegral_indicator hb, setLIntegral_const, Measure.restrict_apply hb, Set.inter_comm band 𝓕]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h0.vol

/- English proof (translation)
Establish `hT` using `((hG μ 𝓕 mK 𝓓 h0).2.2 (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).1 (lowS H σ (n + 1)) (measurable_lowS hH σ (n + 1)) (linv_ind (linv_lowW hH σ) (dyShell (n + 1)))`. Rewrite using `[← hT, ← lintegral_const_mul _ (measurable_lowS hH σ n)]`. Conclude with `lintegral_congr fun g => lowS_dg hH σ hz n g`.
-/
theorem lintegral_lowS_succ {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} {H : G2 → ℂ}
    (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) (σ : ℝ) {z : Jd} (hz : md z ^ 2 = 1 / 2) (n : ℕ) :
    ∫⁻ g in 𝓕, lowS H σ (n + 1) g ∂μ = ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) * ∫⁻ g in 𝓕, lowS H σ n g ∂μ := by
  have hT := ((hG μ 𝓕 mK 𝓓 h0).2.2 (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).1 (lowS H σ (n + 1))
    (measurable_lowS hH σ (n + 1)) (linv_ind (linv_lowW hH σ) (dyShell (n + 1)))
  rw [← hT, ← lintegral_const_mul _ (measurable_lowS hH σ n)]
  exact lintegral_congr fun g => lowS_dg hH σ hz n g

/- English proof (translation)
Take `⟨z, hz, -⟩` from `(hG μ 𝓕 mK 𝓓 h0).2.1 (1 / 2) (by norm_num)`. Use `set q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) with hq`. Establish `hq1 : q < 1`. Rewrite using `[hq, ENNReal.ofReal_lt_one]`. Conclude with `Real.rpow_lt_one (by norm_num) (by norm_num) hσ`.

Establish `hpow : ∀ n, ∫⁻ g in 𝓕, lowS H σ n g ∂μ = q ^ n * ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [lintegral_lowS_succ hG h0 hH σ hz n, ih, pow_succ']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hS : MeasurableSet {g : G2 | Dt g < 1}` using `measurable_Dt measurableSet_Iio`. Establish `hle : ∀ g, Set.indicator {g : G2 | Dt g < 1} (lowW H σ) g ≤ ∑' n, lowS H σ n g`. Introduce `g`. Distinguish the cases in `h : g ∈ {g : G2 | Dt g < 1}`.

Take `⟨n, hn⟩` from `exists_mem_dyShell (Dt_pos g) h`. Rewrite using `[Set.indicator_of_mem h]`. Use `le_trans (le_of_eq ?_) (ENNReal.le_tsum (n + 1))` and prove the remaining obligations. Rewrite using `[lowS, Set.indicator_of_mem (show g ∈ {g | Dt g ∈ dyShell (n + 1)} from hn)]`. Rewrite using `[Set.indicator_of_notMem h]`.

Conclude with `zero_le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_indicator hS, Measure.restrict_restrict hS, Set.inter_comm 𝓕]`. Use `_ ≤ ∫⁻ g in 𝓕, ∑' n, lowS H σ n g ∂μ := lintegral_mono hle`. Use `_ = ∑' n, ∫⁻ g in 𝓕, lowS H σ n g ∂μ := lintegral_tsum fun n => (measurable_lowS hH σ n).aemeasurable`.

Use `_ = (∑' n, q ^ n) * ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ := by`. Rewrite using `[tsum_congr hpow, ENNReal.tsum_mul_right]`. Use `_ < ∞ := by`. Use `ENNReal.mul_lt_top ?_ (lintegral_lowS_zero h0 hH hσ)` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_geometric]`.

Conclude with `ENNReal.inv_lt_top.2 (tsub_pos_of_lt hq1)`.
-/
theorem lintegral_lowW_lt_top {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} {H : G2 → ℂ}
    (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ g in 𝓕 ∩ {g | Dt g < 1}, lowW H σ g ∂μ < ∞ := by
  obtain ⟨z, hz, -⟩ := (hG μ 𝓕 mK 𝓓 h0).2.1 (1 / 2) (by norm_num)
  set q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) with hq
  have hq1 : q < 1 := by
    rw [hq, ENNReal.ofReal_lt_one]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hσ
  have hpow : ∀ n, ∫⁻ g in 𝓕, lowS H σ n g ∂μ = q ^ n * ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [lintegral_lowS_succ hG h0 hH σ hz n, ih, pow_succ']; ring
  have hS : MeasurableSet {g : G2 | Dt g < 1} := measurable_Dt measurableSet_Iio
  have hle : ∀ g, Set.indicator {g : G2 | Dt g < 1} (lowW H σ) g ≤ ∑' n, lowS H σ n g := by
    intro g
    by_cases h : g ∈ {g : G2 | Dt g < 1}
    · obtain ⟨n, hn⟩ := exists_mem_dyShell (Dt_pos g) h
      rw [Set.indicator_of_mem h]
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (n + 1))
      rw [lowS, Set.indicator_of_mem (show g ∈ {g | Dt g ∈ dyShell (n + 1)} from hn)]
    · rw [Set.indicator_of_notMem h]
      exact zero_le
  calc ∫⁻ g in 𝓕 ∩ {g | Dt g < 1}, lowW H σ g ∂μ
      = ∫⁻ g in 𝓕, Set.indicator {g : G2 | Dt g < 1} (lowW H σ) g ∂μ := by
        rw [lintegral_indicator hS, Measure.restrict_restrict hS, Set.inter_comm 𝓕]
    _ ≤ ∫⁻ g in 𝓕, ∑' n, lowS H σ n g ∂μ := lintegral_mono hle
    _ = ∑' n, ∫⁻ g in 𝓕, lowS H σ n g ∂μ :=
        lintegral_tsum fun n => (measurable_lowS hH σ n).aemeasurable
    _ = (∑' n, q ^ n) * ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ := by
        rw [tsum_congr hpow, ENNReal.tsum_mul_right]
    _ < ∞ := by
        refine ENNReal.mul_lt_top ?_ (lintegral_lowS_zero h0 hH hσ)
        rw [ENNReal.tsum_geometric]
        exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hq1)

/- English proof (translation)
Use `⟨(measurable_w hH c s).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `hn : ∀ g, ‖H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s‖ₑ = lowW H s.re g`. Introduce `g`. Rewrite using `[enorm_mul, enorm_mul, lowW, ← ofReal_norm_eq_enorm (cdet c g), norm_cdet, ← ofReal_norm_eq_enorm (((Dt g : ℝ) : ℂ) ^ s), Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]`. Simplify using the standard rewrite rules.

Rewrite using `[HasFiniteIntegral]`. Repeatedly rewrite using `[hn]`. Conclude with `lintegral_lowW_lt_top hG h0 hH hs`.
-/
theorem integrableOn_low (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ)
    (c : HeckeCharacter ℚ) (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) (_hc : IsOfFinOrder c)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ := by
  refine ⟨(measurable_w hH c s).aestronglyMeasurable, ?_⟩
  have hn : ∀ g, ‖H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s‖ₑ = lowW H s.re g := by
    intro g
    rw [enorm_mul, enorm_mul, lowW, ← ofReal_norm_eq_enorm (cdet c g), norm_cdet,
      ← ofReal_norm_eq_enorm (((Dt g : ℝ) : ℂ) ^ s), Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
    simp
  rw [HasFiniteIntegral]
  simp_rw [hn]
  exact lintegral_lowW_lt_top hG h0 hH hs

end GlobalTheory.CompanionTheory.RSZeta
