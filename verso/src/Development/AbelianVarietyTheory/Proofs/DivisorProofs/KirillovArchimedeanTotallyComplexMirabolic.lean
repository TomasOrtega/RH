import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothCompactPartitionOnCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOperatorGLnSmoothAffineTranslationSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelOperatorRowFrequencyColumnTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnipotentTimesGLrSetClosedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTruncatedRowUnipotentInvariantNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionMatrixInvertibleLevelReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanMatrixSmoothingNeZeroAtOneStatement

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Use `open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))`.
-/
theorem isOpenEmbedding_valGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

/- English proof (translation)
Use `(isOpenEmbedding_valGLInf (E := E) (n := n)).isOpen_range` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Conclude with `⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩`.
-/
theorem isOpen_isUnit_ofInf : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
  have := (isOpenEmbedding_valGLInf (E := E) (n := n)).isOpen_range
  convert this using 1
  ext x
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩

/- English proof (translation)
Rewrite using `[isOpenEmbedding_valGLInf.isInducing.continuousOn_iff]`. Conclude with `continuousOn_id.congr fun x hx => val_toGLInf hx`.
-/
theorem continuousOn_toGLInf :
    ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)} := by
  rw [isOpenEmbedding_valGLInf.isInducing.continuousOn_iff]
  exact continuousOn_id.congr fun x hx => val_toGLInf hx

/- English proof (translation)
Introduce `u hu g`. Simplify using `only [smoothMatInf]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Rewrite using `[Units.val_mul, mul_assoc (u : Matrix (Fin n) (Fin n) (Cinf E))]`. Distinguish the cases in `h : IsUnit ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a)`. Take `⟨x, hx⟩` from `h`. Rewrite using `[← hx, ← Units.val_mul, onMatInf_val, onMatInf_val, hW u hu]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h' : ¬ IsUnit ((u : Matrix (Fin n) (Fin n) (Cinf E)) * ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a))` using `fun h' => h ((Units.isUnit_units_mul u _).1 h')`. Simplify using `[onMatInf, h, h']`.
-/
theorem isWhitInf_smoothMatInf {W : GL (Fin n) (Cinf E) → ℂ} (hW : IsWhitInf W) (α : (Fin n → Fin n → Cinf E) → ℂ) :
    IsWhitInf (smoothMatInf α W) := by
  intro u hu g
  simp only [smoothMatInf]
  rw [← integral_const_mul]
  congr 1
  funext a
  rw [Units.val_mul, mul_assoc (u : Matrix (Fin n) (Fin n) (Cinf E))]
  by_cases h : IsUnit ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a)
  · obtain ⟨x, hx⟩ := h
    rw [← hx, ← Units.val_mul, onMatInf_val, onMatInf_val, hW u hu]; ring
  · have h' : ¬ IsUnit ((u : Matrix (Fin n) (Fin n) (Cinf E)) * ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a)) :=
      fun h' => h ((Units.isUnit_units_mul u _).1 h')
    simp [onMatInf, h, h']

/- English proof (translation)
The claim follows from `(GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j h => (mem_levSetInf.1 hg i (Nat.zero_le _)).1 j h, fun i => (mem_levSetInf.1 hg i (Nat.zero_le _)).2⟩`.
-/
theorem mem_unipB_of_levSetInf_zero {g : GL (Fin n) (Cinf E)} (hg : g ∈ levSetInf E n 0) :
    g ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j h => (mem_levSetInf.1 hg i (Nat.zero_le _)).1 j h,
    fun i => (mem_levSetInf.1 hg i (Nat.zero_le _)).2⟩

/- English proof (translation)
The claim follows from `mem_levSetInf.2 fun i hi => mem_levSetInf.1 hg i (by omega)`.
-/
theorem levSetInf_mono {r : ℕ} {g : GL (Fin n) (Cinf E)} (hg : g ∈ levSetInf E n r) : g ∈ levSetInf E n (r + 1) :=
  mem_levSetInf.2 fun i hi => mem_levSetInf.1 hg i (by omega)

/- English proof (translation)
Introduce `Y _ _ _ B hB hBe ⟨D, C, hD, _, hDC⟩`. Establish `h1 : (1 : GL (Fin n) (Cinf E)) ∈ levSetInf E n 0` using `(GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup E n 0).2.2.1 1 (one_mem _)`. Establish `hΦ : ContDiff ℝ ∞ fun y => B (y, matInf (1 : GL (Fin n) (Cinf E)))` using `hB.comp_contDiff (contDiff_id.prodMk contDiff_const) fun y => (1 : GL (Fin n) (Cinf E)).isUnit`. Establish `hΦc : HasCompactSupport fun y => B (y, matInf (1 : GL (Fin n) (Cinf E)))` using `HasCompactSupport.intro hD fun y hy => by_contra fun h => hy (hDC y 1 h1 h).1`. Take `⟨X, _, ν, _, κ, τ, h1, h2, h3, h4⟩` from `GlobalTheory.JSW.exists_rapid_superposition_characters _ _ hΦ hΦc`.

Use `⟨fun W y g => ∫ x, κ x * (𝐞 (τ x y) : ℂ) * W (g * 1) ∂ν, ⟨X, inferInstance, ν, inferInstance, κ, fun _ => 1, τ, ⟨h1, fun _ _ => measurable_const, h2, fun N => ?_⟩, fun _ _ _ _ => rfl⟩, fun W _ hW y g hg => ?_⟩` and prove the remaining obligations. Use `((h3 N).const_mul (htInf (1 : GL (Fin n) (Cinf E)) ^ N)).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hg'` using `mem_unipB_of_levSetInf_zero hg`.

Establish `e` using `hBe y g hg' 1`. Simplify using `only [mul_one] at e`. Simplify using `only`. Rewrite using `[integral_mul_const, ← h4, hW g hg', e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levRepInf_zero (n : ℕ) : LevRepInf E n 0 fun W => W 1 := by
  intro Y _ _ _ B hB hBe ⟨D, C, hD, _, hDC⟩
  have h1 : (1 : GL (Fin n) (Cinf E)) ∈ levSetInf E n 0 := (GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup E n 0).2.2.1 1 (one_mem _)
  have hΦ : ContDiff ℝ ∞ fun y => B (y, matInf (1 : GL (Fin n) (Cinf E))) :=
    hB.comp_contDiff (contDiff_id.prodMk contDiff_const) fun y => (1 : GL (Fin n) (Cinf E)).isUnit
  have hΦc : HasCompactSupport fun y => B (y, matInf (1 : GL (Fin n) (Cinf E))) :=
    HasCompactSupport.intro hD fun y hy => by_contra fun h => hy (hDC y 1 h1 h).1
  obtain ⟨X, _, ν, _, κ, τ, h1, h2, h3, h4⟩ := GlobalTheory.JSW.exists_rapid_superposition_characters _ _ hΦ hΦc
  refine ⟨fun W y g => ∫ x, κ x * (𝐞 (τ x y) : ℂ) * W (g * 1) ∂ν,
    ⟨X, inferInstance, ν, inferInstance, κ, fun _ => 1, τ, ⟨h1, fun _ _ => measurable_const, h2, fun N => ?_⟩,
      fun _ _ _ _ => rfl⟩, fun W _ hW y g hg => ?_⟩
  · refine ((h3 N).const_mul (htInf (1 : GL (Fin n) (Cinf E)) ^ N)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_pow]; ring
  · have hg' := mem_unipB_of_levSetInf_zero hg
    have e := hBe y g hg' 1
    simp only [mul_one] at e
    simp only
    rw [integral_mul_const, ← h4, hW g hg', e]; ring

/- English proof (translation)
Take `⟨hs1, hs2, L, hL⟩` from `GlobalTheory.T.archimedeanSectionMatrix_invertible_level_reduction E n ρ j hj`. Establish `hU : IsOpen {z : Y × (Fin n → Cinf E) | ∀ w, z.2 (j w) w ≠ 0}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const`. Take `⟨χ, hχ, hχ1⟩` from `GlobalTheory.exists_smooth_compact_partition_on_compact _ _ hφc.isCompact Unit (fun _ => {z : Y × (Fin n → Cinf E) | ∀ w, z.2 (j w) w ≠ 0}) (fun _ => hU) (by simpa [Set.iUnion_const] using hφs)`.

Take `⟨hχa, hχb, hχc⟩` from `hχ ()`. Establish `hsd : ContDiff ℝ ∞ (secMatInf ρ j)`. Rewrite using `[show secMatInf ρ j = fun v => secMatInf ρ j 0 + L v from funext hL]`. Conclude with `contDiff_const.add L.contDiff`. Set `B' : (Y × (Fin n → Cinf E)) × (Fin n → Fin n → Cinf E) → ℂ` to `fun p => φ p.1 * B (p.1.1, fun a b => (Matrix.of p.2 * Matrix.of (secMatInf ρ j p.1.2)) a b)`.

Establish `hB'v : ∀ (z : Y × (Fin n → Cinf E)) (g : GL (Fin n) (Cinf E)), (∀ w, z.2 (j w) w ≠ 0) → B' (z, matInf g) = φ z * B (z.1, matInf (g * toGLInf (Matrix.of (secMatInf ρ j z.2))))`. Introduce `z g hz`. Establish `: matInf (g * toGLInf (Matrix.of (secMatInf ρ j z.2))) = fun a b => (Matrix.of (matInf g) * Matrix.of (secMatInf ρ j z.2)) a b`. Use function extensionality and compare the values at `a b`. Simplify using `only [matInf, Units.val_mul, val_toGLInf (hs1 _ hz).1]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Establish `hφ0 : ∀ z : Y × (Fin n → Cinf E), φ z ≠ 0 → ∀ w, z.2 (j w) w ≠ 0` using `fun z hz => hφs (subset_tsupport _ hz)`. Establish `hB' : ContDiffOn ℝ ∞ B' {p | IsUnit (Matrix.of p.2)}`. Introduce `p hp`.

Use `ContDiffAt.contDiffWithinAt ?_` and prove the remaining obligations. Distinguish the cases in `hz : p.1 ∈ tsupport φ`. Use `(hφ.comp contDiff_fst).contDiffAt.mul ?_` and prove the remaining obligations. Establish `hin : ContDiff ℝ ∞ fun p : (Y × (Fin n → Cinf E)) × (Fin n → Fin n → Cinf E) => (p.1.1, fun a b => (Matrix.of p.2 * Matrix.of (secMatInf ρ j p.1.2)) a b)`. Use `contDiff_fst.fst.prodMk (contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_)` and prove the remaining obligations.

Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Use `ContDiff.sum fun l _ => ContDiff.mul ?_ ?_` and prove the remaining obligations. Conclude with `contDiff_pi.1 (contDiff_pi.1 contDiff_snd a) l`. Conclude with `contDiff_pi.1 (contDiff_pi.1 (hsd.comp contDiff_fst.snd) l) b`. Use `ContDiffAt.comp p (hB.contDiffAt ((isOpen_isUnit_ofInf.preimage continuous_snd).mem_nhds ?_)) hin.contDiffAt` and prove the remaining obligations.

Conclude with `IsUnit.mul hp (hs1 _ (hφs hz)).1`. Use `(contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_ filter_upwards [continuous_fst.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hz)] with y hy` and prove the remaining obligations. Simplify using `only [B']`. Rewrite using `[hy, Pi.zero_apply, zero_mul]`. Establish `hB'e : ∀ z, IsWhitInf fun g => B' (z, matInf g)`.

Introduce `z u hu g`. Distinguish the cases in `hz : φ z = 0`. Simplify using `[B', hz]`. Simplify using `only [hB'v z _ (hφ0 z hz)]`. Establish `e` using `hBe z.1 u hu (g * toGLInf (Matrix.of (secMatInf ρ j z.2)))`.

Simplify using `only at e`. Rewrite using `[mul_assoc, e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcont : ContinuousOn (fun p : GL (Fin n) (Cinf E) × (Y × (Fin n → Cinf E)) => p.1 * (toGLInf (Matrix.of (secMatInf ρ j p.2.2)))⁻¹) (C ×ˢ tsupport φ)` using `continuousOn_fst.mul (ContinuousOn.inv (continuousOn_toGLInf.comp (hsd.continuous.comp continuous_snd.snd).continuousOn fun p hp => (hs1 _ (hφs hp.2)).1))`. Take `⟨T, hT, hT'⟩` from `ih (Y × (Fin n → Cinf E)) B' hB' hB'e ⟨tsupport φ, _, hφc.isCompact, (hC.prod hφc.isCompact).image_of_continuousOn hcont, fun z g hg h => by`.

Establish `hz : φ z ≠ 0` using `fun h0 => h (by simp [B', h0])`. Rewrite `h` using `[hB'v z g (hφ0 z hz)]`. Take `⟨u, hu, hu'⟩` from `hBC z.1 _ ((GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup E n (ρ + 1)).1 g (levSetInf_mono hg) _ (hs1 _ (hφ0 z hz)).2) (right_ne_zero_of_mul h)`. Conclude with `⟨subset_tsupport _ hz, u, hu, ⟨(_, z), ⟨hu', subset_tsupport _ hz⟩, by simp [mul_assoc]⟩⟩⟩`. Establish `hT2` using `GlobalTheory.T.kernelOperator_GLn_smoothAffineTranslation_section E n _ (secMatInf ρ j 0) (L.comp (ContinuousLinearMap.snd ℝ Y (Fin n → Cinf E))) (χ ()) α hχa hχb (fun z hz => by simpa [← hL] using (hs1 _ (hχc hz)).1) hα hαc hαs T hT`.

Take `⟨T', hT3, hT4⟩` from `GlobalTheory.T.exists_kernelOperator_rowFrequency_columnTranslate E n ρ hρ Y _ hT2`. Use `⟨T', hT3, fun W hW hWe y g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[hT4 W hW hWe y g hg]`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', ← hL]`. Distinguish the cases in `hv : ∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0`.

Rewrite using `[hT' _ (GlobalTheory.T.isArchimedeanModerateGrowth_matrixSmoothingIntegral E n α hα.continuous hαc hαs W hW) (isWhitInf_smoothMatInf hWe α) _ _ (hs2 g hg hv), hB'v _ _ hv, inv_mul_cancel_right]`. Distinguish the cases in `a1 : φ (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) = 0`. Simplify using `[a1]`. Use `hχ1 _ (subset_tsupport _ a1)` as an intermediate fact. Simplify using `only [Finset.univ_unique, Finset.sum_singleton] at this`.

Rewrite using `[this, one_mul]`. Establish `a1 : φ (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) = 0` using `by_contra fun h => hv (hφ0 _ h)`. Establish `a2 : χ () (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) = 0`. Assume the negation of the conclusion as `fun h => hv (hχc (subset_tsupport _ h))`. Simplify using `[a1, a2]`.
-/
theorem step_chart (ρ : Fin n) (hρ : (ρ : ℕ) + 1 < n) {lam : (GL (Fin n) (Cinf E) → ℂ) → ℂ}
    (ih : LevRepInf E n ρ lam) {α : (Fin n → Fin n → Cinf E) → ℂ}
    (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α) (hαs : tsupport α ⊆ {x | IsUnit (Matrix.of x)})
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] {B : Y × (Fin n → Fin n → Cinf E) → ℂ}
    (hB : ContDiffOn ℝ ∞ B {p | IsUnit (Matrix.of p.2)}) (hBe : ∀ y, IsWhitInf fun g => B (y, matInf g))
    {C : Set (GL (Fin n) (Cinf E))} (hC : IsCompact C)
    (hBC : ∀ y, ∀ g ∈ levSetInf E n (ρ + 1), B (y, matInf g) ≠ 0 →
      ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u⁻¹ * g ∈ C)
    {j : InfinitePlace E → Fin n} (hj : ∀ w, j w ≤ ρ) {φ : Y × (Fin n → Cinf E) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ {z | ∀ w, z.2 (j w) w ≠ 0}) :
    ∃ T : (GL (Fin n) (Cinf E) → ℂ) → Y → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T ∧
      ∀ W, IsModGrowthInf W → IsWhitInf W → ∀ y, ∀ g ∈ levSetInf E n (ρ + 1),
        T W y g = φ (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) * B (y, matInf g) *
          lam (smoothMatInf α W) := by
  obtain ⟨hs1, hs2, L, hL⟩ := GlobalTheory.T.archimedeanSectionMatrix_invertible_level_reduction E n ρ j hj
  have hU : IsOpen {z : Y × (Fin n → Cinf E) | ∀ w, z.2 (j w) w ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const
  obtain ⟨χ, hχ, hχ1⟩ := GlobalTheory.exists_smooth_compact_partition_on_compact _ _ hφc.isCompact Unit
    (fun _ => {z : Y × (Fin n → Cinf E) | ∀ w, z.2 (j w) w ≠ 0}) (fun _ => hU) (by simpa [Set.iUnion_const] using hφs)
  obtain ⟨hχa, hχb, hχc⟩ := hχ ()
  have hsd : ContDiff ℝ ∞ (secMatInf ρ j) := by
    rw [show secMatInf ρ j = fun v => secMatInf ρ j 0 + L v from funext hL]
    exact contDiff_const.add L.contDiff
  let B' : (Y × (Fin n → Cinf E)) × (Fin n → Fin n → Cinf E) → ℂ := fun p =>
    φ p.1 * B (p.1.1, fun a b => (Matrix.of p.2 * Matrix.of (secMatInf ρ j p.1.2)) a b)
  have hB'v : ∀ (z : Y × (Fin n → Cinf E)) (g : GL (Fin n) (Cinf E)), (∀ w, z.2 (j w) w ≠ 0) →
      B' (z, matInf g) = φ z * B (z.1, matInf (g * toGLInf (Matrix.of (secMatInf ρ j z.2)))) := by
    intro z g hz
    have : matInf (g * toGLInf (Matrix.of (secMatInf ρ j z.2))) =
        fun a b => (Matrix.of (matInf g) * Matrix.of (secMatInf ρ j z.2)) a b := by
      funext a b
      simp only [matInf, Units.val_mul, val_toGLInf (hs1 _ hz).1]
      rfl
    rw [this]
  have hφ0 : ∀ z : Y × (Fin n → Cinf E), φ z ≠ 0 → ∀ w, z.2 (j w) w ≠ 0 :=
    fun z hz => hφs (subset_tsupport _ hz)
  have hB' : ContDiffOn ℝ ∞ B' {p | IsUnit (Matrix.of p.2)} := by
    intro p hp
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hz : p.1 ∈ tsupport φ
    · refine (hφ.comp contDiff_fst).contDiffAt.mul ?_
      have hin : ContDiff ℝ ∞ fun p : (Y × (Fin n → Cinf E)) × (Fin n → Fin n → Cinf E) =>
          (p.1.1, fun a b => (Matrix.of p.2 * Matrix.of (secMatInf ρ j p.1.2)) a b) := by
        refine contDiff_fst.fst.prodMk (contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_)
        simp only [Matrix.mul_apply, Matrix.of_apply]
        refine ContDiff.sum fun l _ => ContDiff.mul ?_ ?_
        · exact contDiff_pi.1 (contDiff_pi.1 contDiff_snd a) l
        · exact contDiff_pi.1 (contDiff_pi.1 (hsd.comp contDiff_fst.snd) l) b
      refine ContDiffAt.comp p (hB.contDiffAt ((isOpen_isUnit_ofInf.preimage continuous_snd).mem_nhds ?_))
        hin.contDiffAt
      exact IsUnit.mul hp (hs1 _ (hφs hz)).1
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [continuous_fst.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hz)] with y hy
      simp only [B']
      rw [hy, Pi.zero_apply, zero_mul]
  have hB'e : ∀ z, IsWhitInf fun g => B' (z, matInf g) := by
    intro z u hu g
    by_cases hz : φ z = 0
    · simp [B', hz]
    · simp only [hB'v z _ (hφ0 z hz)]
      have e := hBe z.1 u hu (g * toGLInf (Matrix.of (secMatInf ρ j z.2)))
      simp only at e
      rw [mul_assoc, e]; ring
  have hcont : ContinuousOn (fun p : GL (Fin n) (Cinf E) × (Y × (Fin n → Cinf E)) =>
      p.1 * (toGLInf (Matrix.of (secMatInf ρ j p.2.2)))⁻¹) (C ×ˢ tsupport φ) :=
    continuousOn_fst.mul (ContinuousOn.inv (continuousOn_toGLInf.comp
      (hsd.continuous.comp continuous_snd.snd).continuousOn fun p hp => (hs1 _ (hφs hp.2)).1))
  obtain ⟨T, hT, hT'⟩ := ih (Y × (Fin n → Cinf E)) B' hB' hB'e
    ⟨tsupport φ, _, hφc.isCompact, (hC.prod hφc.isCompact).image_of_continuousOn hcont, fun z g hg h => by
      have hz : φ z ≠ 0 := fun h0 => h (by simp [B', h0])
      rw [hB'v z g (hφ0 z hz)] at h
      obtain ⟨u, hu, hu'⟩ := hBC z.1 _ ((GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup E n (ρ + 1)).1 g (levSetInf_mono hg) _
        (hs1 _ (hφ0 z hz)).2) (right_ne_zero_of_mul h)
      exact ⟨subset_tsupport _ hz, u, hu, ⟨(_, z), ⟨hu', subset_tsupport _ hz⟩, by simp [mul_assoc]⟩⟩⟩
  have hT2 := GlobalTheory.T.kernelOperator_GLn_smoothAffineTranslation_section E n _ (secMatInf ρ j 0) (L.comp (ContinuousLinearMap.snd ℝ Y (Fin n → Cinf E))) (χ ()) α
    hχa hχb (fun z hz => by simpa [← hL] using (hs1 _ (hχc hz)).1) hα hαc hαs T hT
  obtain ⟨T', hT3, hT4⟩ := GlobalTheory.T.exists_kernelOperator_rowFrequency_columnTranslate E n ρ hρ Y _ hT2
  refine ⟨T', hT3, fun W hW hWe y g hg => ?_⟩
  rw [hT4 W hW hWe y g hg]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', ← hL]
  by_cases hv : ∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0
  · rw [hT' _ (GlobalTheory.T.isArchimedeanModerateGrowth_matrixSmoothingIntegral E n α hα.continuous hαc hαs W hW) (isWhitInf_smoothMatInf hWe α) _ _ (hs2 g hg hv),
      hB'v _ _ hv, inv_mul_cancel_right]
    by_cases a1 : φ (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) = 0
    · simp [a1]
    · have := hχ1 _ (subset_tsupport _ a1)
      simp only [Finset.univ_unique, Finset.sum_singleton] at this
      rw [this, one_mul]
  · have a1 : φ (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) = 0 := by_contra fun h => hv (hφ0 _ h)
    have a2 : χ () (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) = 0 :=
      by_contra fun h => hv (hχc (subset_tsupport _ h))
    simp [a1, a2]

/- English proof (translation)
Introduce `Y _ _ _ B hB hBe ⟨D, C, hD, hC, hDC⟩`. Establish `hrc : Continuous fun g : GL (Fin n) (Cinf E) => rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))`. Use `continuous_pi fun l => ?_` and prove the remaining obligations. Distinguish the cases in `h : l ≤ ρ`. Simplify using `only [rowCutInf, h, if_true]`.

Conclude with `Units.continuous_val.matrix_elem ρ l`. Simplify using `only [rowCutInf, h, if_false]`. Conclude with `continuous_const`. Take `⟨hl1, hl2, hl3, hl4⟩` from `GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup E n (ρ + 1)`. Establish `hK : IsCompact (D ×ˢ ((fun g : GL (Fin n) (Cinf E) => rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) '' (C ∩ levSetInf E n (ρ + 1))))` using `hD.prod ((hC.inter_right hl4).image hrc)`.

Take `⟨φ, hφ, hφ1⟩` from `GlobalTheory.exists_smooth_compact_partition_on_compact _ _ hK (InfinitePlace E → {j : Fin n // j ≤ ρ}) (fun j => {z : Y × (Fin n → Cinf E) | ∀ w, z.2 (j w).1 w ≠ 0}) (fun _ => by`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const) (by`. Introduce and unpack `⟨y, v⟩ ⟨-, c, hc, rfl⟩`. Use `choose j hj hj' using (GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero E n ρ c hc.2).2`.

Conclude with `Set.mem_iUnion.2 ⟨fun w => ⟨j w, hj w⟩, hj'⟩)`. Use `choose T hT hT' using fun j : InfinitePlace E → {j : Fin n // j ≤ ρ} => step_chart ρ hρ ih hα hαc hαs hB hBe hC (fun y g hg h => (hDC y g hg h).2) (j := fun w => (j w).1) (fun w => (j w).2) (hφ j).1 (hφ j).2.1 (hφ j).2.2`. Use `⟨_, GlobalTheory.T.isArchimedeanRapidKernelOperator_finset_sum E n Y _ T hT, fun W hW hWe y g hg => ?_⟩` and prove the remaining obligations. Simplify using `only [hT' _ W hW hWe y g hg, ← Finset.sum_mul]`. Distinguish the cases in `h : B (y, matInf g) = 0`.

Simplify using `[h]`. Take `⟨hy, u, hu, hu'⟩` from `hDC y g hg h`. Establish `hc : u⁻¹ * g ∈ levSetInf E n (ρ + 1)` using `hl1 _ (hl3 _ (inv_mem hu)) _ hg`. Rewrite using `[hφ1 _ ⟨hy, u⁻¹ * g, ⟨hu', hc⟩, (GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero E n ρ g hg).1 _ (inv_mem hu)⟩, one_mul]`.
-/
theorem levRepInf_succ (ρ : Fin n) (hρ : (ρ : ℕ) + 1 < n) {lam : (GL (Fin n) (Cinf E) → ℂ) → ℂ}
    (ih : LevRepInf E n ρ lam) {α : (Fin n → Fin n → Cinf E) → ℂ} (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    (hαs : tsupport α ⊆ {x | IsUnit (Matrix.of x)}) :
    LevRepInf E n (ρ + 1) fun W => lam (smoothMatInf α W) := by
  classical
  intro Y _ _ _ B hB hBe ⟨D, C, hD, hC, hDC⟩
  have hrc : Continuous fun g : GL (Fin n) (Cinf E) => rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) := by
    refine continuous_pi fun l => ?_
    by_cases h : l ≤ ρ
    · simp only [rowCutInf, h, if_true]
      exact Units.continuous_val.matrix_elem ρ l
    · simp only [rowCutInf, h, if_false]
      exact continuous_const
  obtain ⟨hl1, hl2, hl3, hl4⟩ := GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup E n (ρ + 1)
  have hK : IsCompact (D ×ˢ ((fun g : GL (Fin n) (Cinf E) => rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ''
      (C ∩ levSetInf E n (ρ + 1)))) := hD.prod ((hC.inter_right hl4).image hrc)
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.exists_smooth_compact_partition_on_compact _ _ hK
    (InfinitePlace E → {j : Fin n // j ≤ ρ}) (fun j => {z : Y × (Fin n → Cinf E) | ∀ w, z.2 (j w).1 w ≠ 0})
    (fun _ => by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const) (by
      rintro ⟨y, v⟩ ⟨-, c, hc, rfl⟩
      choose j hj hj' using (GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero E n ρ c hc.2).2
      exact Set.mem_iUnion.2 ⟨fun w => ⟨j w, hj w⟩, hj'⟩)
  choose T hT hT' using fun j : InfinitePlace E → {j : Fin n // j ≤ ρ} => step_chart ρ hρ ih hα hαc hαs hB hBe hC
    (fun y g hg h => (hDC y g hg h).2) (j := fun w => (j w).1) (fun w => (j w).2) (hφ j).1 (hφ j).2.1 (hφ j).2.2
  refine ⟨_, GlobalTheory.T.isArchimedeanRapidKernelOperator_finset_sum E n Y _ T hT, fun W hW hWe y g hg => ?_⟩
  simp only [hT' _ W hW hWe y g hg, ← Finset.sum_mul]
  by_cases h : B (y, matInf g) = 0
  · simp [h]
  · obtain ⟨hy, u, hu, hu'⟩ := hDC y g hg h
    have hc : u⁻¹ * g ∈ levSetInf E n (ρ + 1) := hl1 _ (hl3 _ (inv_mem hu)) _ hg
    rw [hφ1 _ ⟨hy, u⁻¹ * g, ⟨hu', hc⟩, (GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero E n ρ g hg).1 _ (inv_mem hu)⟩, one_mul]

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => exact fun _ W₀ _ h => ⟨_, h, levRepInf_zero n⟩`. Consider the case `succ r ih`. Introduce `hr W₀ hW h`. Take `⟨α, hα, hαc, hαs, hα1⟩` from `GlobalTheory.T.exists_archimedeanMatrixSmoothing_ne_zero_at_one E n W₀ hW.1 h`.

Take `⟨lam, h1, h2⟩` from `ih (by omega) _ (GlobalTheory.T.isArchimedeanModerateGrowth_matrixSmoothingIntegral E n α hα.continuous hαc hαs W₀ hW) hα1`. Conclude with `⟨_, h1, levRepInf_succ ⟨r, by omega⟩ hr h2 hα hαc hαs⟩`.
-/
theorem exists_levRepInf (r : ℕ) :
    r < n → ∀ W₀ : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W₀ → W₀ 1 ≠ 0 → ∃ lam, lam W₀ ≠ 0 ∧ LevRepInf E n r lam := by
  induction r with
  | zero => exact fun _ W₀ _ h => ⟨_, h, levRepInf_zero n⟩
  | succ r ih =>
    intro hr W₀ hW h
    obtain ⟨α, hα, hαc, hαs, hα1⟩ := GlobalTheory.T.exists_archimedeanMatrixSmoothing_ne_zero_at_one E n W₀ hW.1 h
    obtain ⟨lam, h1, h2⟩ := ih (by omega) _ (GlobalTheory.T.isArchimedeanModerateGrowth_matrixSmoothingIntegral E n α hα.continuous hαc hαs W₀ hW) hα1
    exact ⟨_, h1, levRepInf_succ ⟨r, by omega⟩ hr h2 hα hαc hαs⟩

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[mem_levSetInf]`. Use `⟨fun h i hi => ?_, fun h j => ?_⟩` and prove the remaining obligations. Take `rfl : i = Fin.last m` from `Fin.ext (by have := i.2; simp; omega)`. Conclude with `⟨fun j hj => by simp [h j, hj.ne], by simp [h _]⟩`.

Use `h (Fin.last m) (by simp) split_ifs with hj` as an intermediate fact. Rewrite using `[hj]`. Conclude with `this.2`. Conclude with `this.1 j (Fin.lt_last_iff_ne_last.2 hj)`.
-/
theorem mirSet_eq_levSetInf (m : ℕ) : mirSet (Cinf E) m = levSetInf E (m + 1) m := by
  ext g
  rw [mem_levSetInf]
  refine ⟨fun h i hi => ?_, fun h j => ?_⟩
  · obtain rfl : i = Fin.last m := Fin.ext (by have := i.2; simp; omega)
    exact ⟨fun j hj => by simp [h j, hj.ne], by simp [h _]⟩
  · have := h (Fin.last m) (by simp)
    split_ifs with hj
    · rw [hj]; exact this.2
    · exact this.1 j (Fin.lt_last_iff_ne_last.2 hj)

/- English proof (translation)
Introduce `E _ _ _ m β f hβe ⟨Bβ, hBβ, hBβv⟩ ⟨C, hC, hβC⟩ hfe hfc ⟨Cf, Nf, hf⟩ hf1`. Establish `hC0 : 0 ≤ Cf`. Establish `h` using `(norm_nonneg _).trans (hf 1)`. Conclude with `nonneg_of_mul_nonneg_left h (pow_pos (by unfold height; positivity) _)`. Establish `hfm : IsModGrowthInf f` using `⟨hfc, Cf * 3 ^ Nf, Nf, fun y => by`.

Establish `h0 : 0 ≤ height y` using `by unfold height; positivity`. Combine the equalities or inequalities in the displayed calculation. Take `⟨lam, hl, hrep⟩` from `exists_levRepInf (E := E) (n := m + 1) m (Nat.lt_succ_self m) f hfm hf1`. Establish `hv : ∀ g : GL (Fin (m + 1)) (Cinf E), Bβ (matInf g) = β g` using `fun g => hBβv g`. Take `⟨T, ⟨X, _, ν, _, k, γ, η, hk, hT⟩, hT'⟩` from `hrep Unit (fun p => Bβ p.2) (hBβ.comp contDiff_snd.contDiffOn fun p hp => hp) (fun _ => by simp only [hv]; exact hβe) ⟨Set.univ, C, isCompact_univ, hC, fun y g hg h => ⟨trivial, hβC g ((mirSet_eq_levSetInf (E := E) m) ▸ hg) (by rwa [hv] at h)⟩⟩`.

Use `⟨X, inferInstance, ν, inferInstance, fun x => (lam f)⁻¹ * k x, γ, ?_, fun p hp => ?_⟩` and prove the remaining obligations. Use `IsRapidInf.of_htInf (hk.1.const_mul _) hk.2.1 fun N => ?_` and prove the remaining obligations. Use `((hk.2.2.2 N).const_mul ‖(lam f)⁻¹‖).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `: η x = 0` using `Subsingleton.elim _ _`. Simplify using `[this, mul_assoc]`.

Establish `e` using `hT' f hfm hfe 0 p ((mirSet_eq_levSetInf (E := E) m) ▸ hp)`. Rewrite `e` using `[hT f hfm, hv]`. Simplify using `only [map_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at e`. Simplify using `only [mul_assoc]`. Rewrite using `[integral_const_mul, e, mul_comm, mul_assoc, mul_inv_cancel₀ hl, mul_one]`.
-/
theorem kirillov_cinf : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (β f : GL (Fin (m + 1)) (Cinf E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y, β (u * y) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * β y) → (∃ B : Lie E (m + 1) → ℂ, ContDiffOn ℝ ∞ B (invSet E (m + 1)) ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), B (toL y.val) = β y) → (∃ C : Set (GL (Fin (m + 1)) (Cinf E)), IsCompact C ∧ ∀ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m, β y ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), u⁻¹ * y ∈ C) → (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y, f (u * y) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * f y) → Continuous f → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) → f 1 ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m, ∫ x, k x * f (y * γ x) ∂ν = β y := by
  intro E _ _ _ m β f hβe ⟨Bβ, hBβ, hBβv⟩ ⟨C, hC, hβC⟩ hfe hfc ⟨Cf, Nf, hf⟩ hf1
  have hC0 : 0 ≤ Cf := by
    have h := (norm_nonneg _).trans (hf 1)
    exact nonneg_of_mul_nonneg_left h (pow_pos (by unfold height; positivity) _)
  have hfm : IsModGrowthInf f := ⟨hfc, Cf * 3 ^ Nf, Nf, fun y => by
    have h0 : 0 ≤ height y := by unfold height; positivity
    calc ‖f y‖ ≤ Cf * height y ^ Nf := hf y
      _ ≤ Cf * (3 * htInf y) ^ Nf :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (height_le_htInf y) Nf) hC0
      _ = Cf * 3 ^ Nf * htInf y ^ Nf := by rw [mul_pow]; ring⟩
  obtain ⟨lam, hl, hrep⟩ := exists_levRepInf (E := E) (n := m + 1) m (Nat.lt_succ_self m) f hfm hf1
  have hv : ∀ g : GL (Fin (m + 1)) (Cinf E), Bβ (matInf g) = β g := fun g => hBβv g
  obtain ⟨T, ⟨X, _, ν, _, k, γ, η, hk, hT⟩, hT'⟩ := hrep Unit (fun p => Bβ p.2)
    (hBβ.comp contDiff_snd.contDiffOn fun p hp => hp) (fun _ => by simp only [hv]; exact hβe)
    ⟨Set.univ, C, isCompact_univ, hC, fun y g hg h =>
      ⟨trivial, hβC g ((mirSet_eq_levSetInf (E := E) m) ▸ hg) (by rwa [hv] at h)⟩⟩
  refine ⟨X, inferInstance, ν, inferInstance, fun x => (lam f)⁻¹ * k x, γ, ?_, fun p hp => ?_⟩
  · refine IsRapidInf.of_htInf (hk.1.const_mul _) hk.2.1 fun N => ?_
    refine ((hk.2.2.2 N).const_mul ‖(lam f)⁻¹‖).congr (Filter.Eventually.of_forall fun x => ?_)
    have : η x = 0 := Subsingleton.elim _ _
    simp [this, mul_assoc]
  · have e := hT' f hfm hfe 0 p ((mirSet_eq_levSetInf (E := E) m) ▸ hp)
    rw [hT f hfm, hv] at e
    simp only [map_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at e
    simp only [mul_assoc]
    rw [integral_const_mul, e, mul_comm, mul_assoc, mul_inv_cancel₀ hl, mul_one]

end GlobalTheory.JSW.MirCinf
