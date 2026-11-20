import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumSu21RankOneSeriesDifferencesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureWeylCellOddUnitaryStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.WeylCell.WeylUnipotentShell.Atone

/- English proof (translation)
Establish `hset : ∀ i : ℕ, f ⁻¹' {i + 1} = {x | f x ≤ i + 1} \ {x | f x ≤ i}`. Introduce `i`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]`. Use linear arithmetic over natural numbers and integers.

Establish `hset0 : f ⁻¹' {0} = {x | f x ≤ 0}`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]`. Use linear arithmetic over natural numbers and integers. Use `⟨measurable_to_countable' fun j => ?_, fun j => ?_⟩` and prove the remaining obligations.

Break down `j with _ | i` into its components or cases. Rewrite using `[hset0]`. Conclude with `hmeas 0`. Rewrite using `[hset]`. Conclude with `(hmeas _).diff (hmeas _)`.

Break down `j with _ | i` into its components or cases. Rewrite using `[hset0, hV]`. Simplify using the standard rewrite rules. Establish `hsub : {x | f x ≤ i} ⊆ {x | f x ≤ i + 1}` using `fun x hx => by`. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hset, measure_diff hsub (hmeas i).nullMeasurableSet (by rw [hV]; exact ENNReal.ofReal_ne_top), hV, hV, if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, ENNReal.ofReal_sub _ (hV0 i)]`.
-/
theorem level_sets {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℕ) (V : ℕ → ℝ)
    (hmeas : ∀ j : ℕ, MeasurableSet {x | f x ≤ j})
    (hV : ∀ j, μ {x | f x ≤ j} = ENNReal.ofReal (V j))
    (hV0 : ∀ j, 0 ≤ V j) :
    Measurable f ∧ ∀ j, μ (f ⁻¹' {j}) = ENNReal.ofReal (V j - if j = 0 then 0 else V (j - 1)) := by
  have hset : ∀ i : ℕ, f ⁻¹' {i + 1} = {x | f x ≤ i + 1} \ {x | f x ≤ i} := by
    intro i; ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]; omega
  have hset0 : f ⁻¹' {0} = {x | f x ≤ 0} := by
    ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]; omega
  refine ⟨measurable_to_countable' fun j => ?_, fun j => ?_⟩
  · rcases j with _ | i
    · rw [hset0]; exact hmeas 0
    · rw [hset]; exact (hmeas _).diff (hmeas _)
  · rcases j with _ | i
    · rw [hset0, hV]; simp
    · have hsub : {x | f x ≤ i} ⊆ {x | f x ≤ i + 1} := fun x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢; omega
      rw [hset, measure_diff hsub (hmeas i).nullMeasurableSet (by rw [hV]; exact ENNReal.ofReal_ne_top),
        hV, hV, if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, ENNReal.ofReal_sub _ (hV0 i)]

/- English proof (translation)
Establish `hmap : ∀ j, (μ.map f) {j} = ENNReal.ofReal (w j)` using `fun j => by`. Rewrite using `[Measure.map_apply hf (measurableSet_singleton j)]`. Conclude with `hw j`. Establish `hL : ∫⁻ x, ‖c (f x)‖ₑ ∂μ = ENNReal.ofReal r`. Rewrite using `[← lintegral_map (f := fun j => ‖c j‖ₑ) measurable_from_nat hf, lintegral_countable']`.

Repeatedly rewrite using `[hmap]`. Rewrite using `[← hr.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (norm_nonneg _) (hw0 j)) hr.summable]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]`.

Establish `hI : Integrable (fun x => c (f x)) μ`. Use `⟨(measurable_from_nat.comp hf).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[HasFiniteIntegral, hL]`. Conclude with `ENNReal.ofReal_lt_top`. Use `⟨hL, hI, ?_⟩` and prove the remaining obligations.

Establish `hIm : Integrable c (μ.map f)` using `(integrable_map_measure measurable_from_nat.aestronglyMeasurable hf.aemeasurable).2 hI`. Rewrite using `[← integral_map hf.aemeasurable measurable_from_nat.aestronglyMeasurable, integral_countable' hIm, ← hs.tsum_eq]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[measureReal_def, hmap, ENNReal.toReal_ofReal (hw0 j), Complex.real_smul, mul_comm]`.
-/
theorem sums_over_levels {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℕ) (hf : Measurable f)
    (w : ℕ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw : ∀ j, μ (f ⁻¹' {j}) = ENNReal.ofReal (w j))
    (c : ℕ → ℂ) (s : ℂ) (hs : HasSum (fun j => c j * (w j : ℂ)) s) (r : ℝ)
    (hr : HasSum (fun j => ‖c j‖ * w j) r) :
    ∫⁻ x, ‖c (f x)‖ₑ ∂μ = ENNReal.ofReal r ∧ Integrable (fun x => c (f x)) μ ∧ ∫ x, c (f x) ∂μ = s := by
  have hmap : ∀ j, (μ.map f) {j} = ENNReal.ofReal (w j) := fun j => by
    rw [Measure.map_apply hf (measurableSet_singleton j)]; exact hw j
  have hL : ∫⁻ x, ‖c (f x)‖ₑ ∂μ = ENNReal.ofReal r := by
    rw [← lintegral_map (f := fun j => ‖c j‖ₑ) measurable_from_nat hf, lintegral_countable']
    simp_rw [hmap]
    rw [← hr.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (norm_nonneg _) (hw0 j)) hr.summable]
    congr 1; funext j
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
  have hI : Integrable (fun x => c (f x)) μ := by
    refine ⟨(measurable_from_nat.comp hf).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hL]; exact ENNReal.ofReal_lt_top
  refine ⟨hL, hI, ?_⟩
  have hIm : Integrable c (μ.map f) :=
    (integrable_map_measure measurable_from_nat.aestronglyMeasurable hf.aemeasurable).2 hI
  rw [← integral_map hf.aemeasurable measurable_from_nat.aestronglyMeasurable, integral_countable' hIm,
    ← hs.tsum_eq]
  congr 1; funext j
  rw [measureReal_def, hmap, ENNReal.toReal_ofReal (hw0 j), Complex.real_smul, mul_comm]

end GlobalTheory.WeylCell.WeylUnipotentShell.Atone

open GlobalTheory.WeylCell.WeylUnipotentShell.Atone in

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q hq n k hk hn y hy hwy _ _ μ _ hμ z hz`. Establish `q2 : 2 ≤ q` using `hq.2.2.2.2.2.1`. Establish `hsh` using `GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup L ϖ σ q hq n k hk hn y hy hwy`. Establish `hvol` using `GlobalTheory.T.haar_measure_weyl_cell_odd_unitary L ϖ σ q hq n k hk hn y hy hwy μ hμ`. Set `f : cellU y → ℕ` to `fun u => depthU k (u : GU σ n)`.

Set `V : ℕ → ℝ` to `fun j => (q : ℝ) ^ (j + 2 * (j / 2))`. Establish `hV0 : ∀ j, 0 ≤ V j` using `fun j => by positivity`. Establish `hlev : ∀ j : ℕ, {u : cellU y | f u ≤ j} = shellU k y j`. Introduce `j`. Use extensionality with `u`.

Conclude with `(mem_shellU_iff_depth k y j u).symm`. Establish `hmeas : ∀ j : ℕ, MeasurableSet {u : cellU y | f u ≤ j}` using `fun j => by`. Rewrite using `[hlev]`. Conclude with `(hsh.1 j).1.measurableSet`. Establish `hV : ∀ j : ℕ, μ {u : cellU y | f u ≤ j} = ENNReal.ofReal (V j)` using `fun j => by`.

Rewrite using `[hlev, hvol j, ENNReal.ofReal_pow (Nat.cast_nonneg q), ENNReal.ofReal_natCast]`. Take `⟨hf, hlv⟩` from `level_sets μ f V hmeas hV hV0`. Set `w : ℕ → ℝ` to `fun j => V j - if j = 0 then 0 else V (j - 1)`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast (by omega : 1 ≤ q)`. Establish `hw0 : ∀ j, 0 ≤ w j` using `fun j => by`.

Simplify using `only [w, V]`. Use `split_ifs with h`. Simplify using `only [sub_zero]`. Check the signs of the components of the expression. Rewrite using `[sub_nonneg]; exact pow_le_pow_right₀ hq1 (by omega)`.

Establish `hwc : ∀ j : ℕ, ((w j : ℝ) : ℂ) = (q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2)))` using `fun j => by`. Apply the tactic sequence `simp only [w, V]; split_ifs <;> push_cast <;> rfl`. Set `c : ℕ → ℂ` to `fun j => (z / (q : ℂ) ^ 2) ^ j`. Establish `hs : HasSum (fun j => c j * (w j : ℂ)) (cSU q z)`. Simplify using `only [c, hwc]`.

Conclude with `GlobalTheory.T.hasSum_cSU_power_differences q q2 z hz`. Establish `hz' : ‖((‖z‖ : ℝ) : ℂ)‖ < 1` using `by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hz`. Establish `hs'` using `GlobalTheory.T.hasSum_cSU_power_differences q q2 _ hz'`. Establish `hterm : ∀ j : ℕ, (((‖z‖ : ℝ) : ℂ) / (q : ℂ) ^ 2) ^ j * ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2)))) = ((‖c j‖ * w j : ℝ) : ℂ)` using `fun j => by`. Rewrite using `[← hwc]`.

Simplify using `only [c, norm_pow, norm_div, Complex.norm_natCast]`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [hterm] at hs'`. Establish `hsum : Summable (fun j => ‖c j‖ * w j)` using `Complex.summable_ofReal.1 hs'.summable`.

Establish `hr` using `hsum.hasSum`. Establish `heq : cSU q ((‖z‖ : ℝ) : ℂ) = ((∑' j, ‖c j‖ * w j : ℝ) : ℂ)` using `hs'.unique (Complex.hasSum_ofReal.2 hr)`. Take `⟨h1, h2, h3⟩` from `sums_over_levels μ f hf w hw0 hlv c _ hs _ hr`. Use `⟨h2, h3, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, heq, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (hw0 j))]`.
-/
theorem _root_.GlobalTheory.WeylCell.WeylUnipotentShell.integral_depth_cell : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ z : ℂ, ‖z‖ < 1 →
      Integrable (fun u : cellU y => (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)) μ ∧
      ∫ u : cellU y, (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) ∂μ = cSU q z ∧
      ∫⁻ u : cellU y, ‖(z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)‖ₑ ∂μ = ‖cSU q ((‖z‖ : ℝ) : ℂ)‖ₑ := by
  intro L _ _ _ ϖ σ q hq n k hk hn y hy hwy _ _ μ _ hμ z hz
  have q2 : 2 ≤ q := hq.2.2.2.2.2.1
  have hsh := GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup L ϖ σ q hq n k hk hn y hy hwy
  have hvol := GlobalTheory.T.haar_measure_weyl_cell_odd_unitary L ϖ σ q hq n k hk hn y hy hwy μ hμ
  let f : cellU y → ℕ := fun u => depthU k (u : GU σ n)
  let V : ℕ → ℝ := fun j => (q : ℝ) ^ (j + 2 * (j / 2))
  have hV0 : ∀ j, 0 ≤ V j := fun j => by positivity
  have hlev : ∀ j : ℕ, {u : cellU y | f u ≤ j} = shellU k y j := by
    intro j; ext u; exact (mem_shellU_iff_depth k y j u).symm
  have hmeas : ∀ j : ℕ, MeasurableSet {u : cellU y | f u ≤ j} := fun j => by
    rw [hlev]; exact (hsh.1 j).1.measurableSet
  have hV : ∀ j : ℕ, μ {u : cellU y | f u ≤ j} = ENNReal.ofReal (V j) := fun j => by
    rw [hlev, hvol j, ENNReal.ofReal_pow (Nat.cast_nonneg q), ENNReal.ofReal_natCast]
  obtain ⟨hf, hlv⟩ := level_sets μ f V hmeas hV hV0
  let w : ℕ → ℝ := fun j => V j - if j = 0 then 0 else V (j - 1)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hw0 : ∀ j, 0 ≤ w j := fun j => by
    simp only [w, V]
    split_ifs with h
    · simp only [sub_zero]; positivity
    · rw [sub_nonneg]; exact pow_le_pow_right₀ hq1 (by omega)
  have hwc : ∀ j : ℕ, ((w j : ℝ) : ℂ) = (q : ℂ) ^ (j + 2 * (j / 2)) -
      (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))) := fun j => by
    simp only [w, V]; split_ifs <;> push_cast <;> rfl
  let c : ℕ → ℂ := fun j => (z / (q : ℂ) ^ 2) ^ j
  have hs : HasSum (fun j => c j * (w j : ℂ)) (cSU q z) := by
    simp only [c, hwc]; exact GlobalTheory.T.hasSum_cSU_power_differences q q2 z hz
  have hz' : ‖((‖z‖ : ℝ) : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hz
  have hs' := GlobalTheory.T.hasSum_cSU_power_differences q q2 _ hz'
  have hterm : ∀ j : ℕ, (((‖z‖ : ℝ) : ℂ) / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2)))) =
      ((‖c j‖ * w j : ℝ) : ℂ) := fun j => by
    rw [← hwc]; simp only [c, norm_pow, norm_div, Complex.norm_natCast]; push_cast; rfl
  simp only [hterm] at hs'
  have hsum : Summable (fun j => ‖c j‖ * w j) := Complex.summable_ofReal.1 hs'.summable
  have hr := hsum.hasSum
  have heq : cSU q ((‖z‖ : ℝ) : ℂ) = ((∑' j, ‖c j‖ * w j : ℝ) : ℂ) :=
    hs'.unique (Complex.hasSum_ofReal.2 hr)
  obtain ⟨h1, h2, h3⟩ := sums_over_levels μ f hf w hw0 hlv c _ hs _ hr
  refine ⟨h2, h3, ?_⟩
  rw [h1, heq, ← ofReal_norm_eq_enorm, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (hw0 j))]
