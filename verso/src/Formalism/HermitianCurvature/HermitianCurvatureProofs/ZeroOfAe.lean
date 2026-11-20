import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability

variable {k r : ℕ}

local notation "MX" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
local notation "UHk" => Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)

/- English proof (translation)
Establish `hc : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => ((Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]`. Use `fun_prop`. Conclude with `(isClosed_eq hc continuous_const).measurableSet`.
-/
theorem uh_meas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  have hc : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r =>
      ((Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    fun_prop
  exact (isClosed_eq hc continuous_const).measurableSet

/- English proof (translation)
Take `⟨P, hP, hD⟩` from `hds`. Establish `h1` using `hD.2.2.1.1.1`. Establish `hPu : IsUnit P.det` using `Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hP.2)`. Simplify `h1` using `[Matrix.nonsing_inv_mul P hPu]`.
-/
theorem sigma_one {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : MX → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ) : σ 1 = 1 := by
  obtain ⟨P, hP, hD⟩ := hds
  have h1 := hD.2.2.1.1.1
  have hPu : IsUnit P.det :=
    Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hP.2)
  simpa [Matrix.nonsing_inv_mul P hPu] using h1

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨V, hVo, hV⟩` from `(continuousOn_iff'.mp hf) {0}ᶜ isOpen_compl_singleton`. Establish `hg0V : g0 ∈ V`. Establish `hm : g0 ∈ f ⁻¹' {0}ᶜ ∩ UHk` using `⟨hne, hg0⟩`. Rewrite `hm` using `[hV]`.

Conclude with `hm.1`. Establish `hnull0 : μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ V ∧ Matrix.of x ∈ UHk} = 0`. Rewrite `hae` using `[ae_iff]`. Use `measure_mono_null ?_ hae` and prove the remaining obligations. Introduce `x hx`.

Take `⟨hxV, hxU⟩` from `hx`. Establish `hm : Matrix.of x ∈ V ∩ UHk` using `⟨hxV, hxU⟩`. Rewrite `hm` using `[← hV]`. Conclude with `fun h => hm.1 (h hxU)`. Establish `hc0 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX))` using `continuous_id`.

Set `O : UHk → Set (Formalism.QuantumDeterminants.Mt k r)` to `fun g => {y | (g : MX)⁻¹ * Matrix.of y ∈ V}`. Establish `hO : ∀ g, IsOpen (O g)` using `fun g => hVo.preimage (continuous_const.matrix_mul hc0)`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable O hO`. Establish `hcover : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of y ∈ UHk → ∃ g ∈ T, y ∈ O g`. Introduce `y hy`.

Establish `hy' : y ∈ ⋃ g, O g`. Use `Set.mem_iUnion.2 ⟨⟨Matrix.of y * g0⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hy (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hg0)⟩, ?_⟩` and prove the remaining obligations. Use `show (Matrix.of y * g0⁻¹)⁻¹ * Matrix.of y ∈ V`. Rewrite using `[Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0), Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy), Matrix.mul_one]`. Conclude with `hg0V`.

Rewrite `hy'` using `[← hTU]`. Take `⟨g, hgT, hyg⟩` from `Set.mem_iUnion₂.1 hy'`. Conclude with `⟨g, hgT, hyg⟩`. Establish `hnullg : ∀ g : UHk, μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g} = 0`. Introduce `g`.

Establish `hinv` using `hμ.2.2.2 g g.2`. Establish `hc1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX))` using `continuous_id`. Establish `hmeasO : MeasurableSet (O g)` using `(hO g).measurableSet`. Establish `hmeas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g}` using `uh_meas.inter hmeasO`. Establish `hcm : Continuous (Formalism.QuantumDeterminants.lmulM (k` using `k) (r := r) (g : MX)) := by`.

Unfold `Formalism.QuantumDeterminants.lmulM`. Conclude with `continuous_const.matrix_mul hc1`. Establish `hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k` using `k) (r := r) (g : MX)) := hcm.measurable`. Rewrite using `[← hinv, Measure.map_apply hlm hmeas]`. Use `measure_mono_null ?_ hnull0` and prove the remaining obligations.

Introduce `x hx`. Take `⟨hxU, hxO⟩` from `hx`. Establish `hgu` using `Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh g.2`. Establish `h1 : (g : MX)⁻¹ * ((g : MX) * Matrix.of x) = Matrix.of x`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul]`.

Establish `hxO' : (g : MX)⁻¹ * ((g : MX) * Matrix.of x) ∈ V` using `hxO`. Establish `hxU' : (g : MX) * Matrix.of x ∈ UHk` using `hxU`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hxO'` using `[h1]`. Conclude with `hxO'`.

Use `Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv g.2) hxU'` as an intermediate fact. Rewrite `this` using `[h1]`. Then use the resulting hypothesis. Establish `hUnull : μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk} = 0`. Use `measure_mono_null (t := ⋃ g ∈ T, {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g}) ?_ ((measure_biUnion_null_iff hTc).2 (fun g _ => hnullg g))` and prove the remaining obligations. Introduce `x hx`.

Take `⟨g, hgT, hxg⟩` from `hcover x hx`. Conclude with `Set.mem_iUnion₂.2 ⟨g, hgT, hx, hxg⟩`. Apply `hμ.2.1` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero]`. Establish `hsplit : (Set.univ : Set (Formalism.QuantumDeterminants.Mt k r)) = {x | Matrix.of x ∈ UHk} ∪ {x | Matrix.of x ∉ UHk}`.

Use extensionality with `x`. Simplify using `only [Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, true_iff]`. Conclude with `em _`. Rewrite using `[hsplit]`. Conclude with `measure_union_null hUnull hμ.2.2.1`.
-/
theorem zero_of_ae {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : PI.BesselPeriodGGP.IsHaarOn UHk μG)
    {E : Type*} [NormedAddCommGroup E] {f : MX → E} (hf : ContinuousOn f UHk)
    (hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UHk → f (Matrix.of x) = 0)
    {g0 : MX} (hg0 : g0 ∈ UHk) : f g0 = 0 := by
  by_contra hne
  obtain ⟨V, hVo, hV⟩ := (continuousOn_iff'.mp hf) {0}ᶜ isOpen_compl_singleton
  have hg0V : g0 ∈ V := by
    have hm : g0 ∈ f ⁻¹' {0}ᶜ ∩ UHk := ⟨hne, hg0⟩
    rw [hV] at hm
    exact hm.1
  have hnull0 : μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ V ∧ Matrix.of x ∈ UHk} = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null ?_ hae
    intro x hx
    obtain ⟨hxV, hxU⟩ := hx
    have hm : Matrix.of x ∈ V ∩ UHk := ⟨hxV, hxU⟩
    rw [← hV] at hm
    exact fun h => hm.1 (h hxU)
  have hc0 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX)) := continuous_id
  let O : UHk → Set (Formalism.QuantumDeterminants.Mt k r) := fun g => {y | (g : MX)⁻¹ * Matrix.of y ∈ V}
  have hO : ∀ g, IsOpen (O g) := fun g => hVo.preimage (continuous_const.matrix_mul hc0)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  have hcover : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of y ∈ UHk → ∃ g ∈ T, y ∈ O g := by
    intro y hy
    have hy' : y ∈ ⋃ g, O g := by
      refine Set.mem_iUnion.2 ⟨⟨Matrix.of y * g0⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hy (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hg0)⟩, ?_⟩
      show (Matrix.of y * g0⁻¹)⁻¹ * Matrix.of y ∈ V
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0),
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy), Matrix.mul_one]
      exact hg0V
    rw [← hTU] at hy'
    obtain ⟨g, hgT, hyg⟩ := Set.mem_iUnion₂.1 hy'
    exact ⟨g, hgT, hyg⟩
  have hnullg : ∀ g : UHk,
      μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g} = 0 := by
    intro g
    have hinv := hμ.2.2.2 g g.2
    have hc1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX)) := continuous_id
    have hmeasO : MeasurableSet (O g) := (hO g).measurableSet
    have hmeas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g} :=
      uh_meas.inter hmeasO
    have hcm : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (g : MX)) := by
      unfold Formalism.QuantumDeterminants.lmulM
      exact continuous_const.matrix_mul hc1
    have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (g : MX)) := hcm.measurable
    rw [← hinv, Measure.map_apply hlm hmeas]
    refine measure_mono_null ?_ hnull0
    intro x hx
    obtain ⟨hxU, hxO⟩ := hx
    have hgu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh g.2
    have h1 : (g : MX)⁻¹ * ((g : MX) * Matrix.of x) = Matrix.of x := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul]
    have hxO' : (g : MX)⁻¹ * ((g : MX) * Matrix.of x) ∈ V := hxO
    have hxU' : (g : MX) * Matrix.of x ∈ UHk := hxU
    refine ⟨?_, ?_⟩
    · rw [h1] at hxO'
      exact hxO'
    · have := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv g.2) hxU'
      rwa [h1] at this
  have hUnull : μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk} = 0 := by
    refine measure_mono_null
      (t := ⋃ g ∈ T, {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g})
      ?_ ((measure_biUnion_null_iff hTc).2 (fun g _ => hnullg g))
    intro x hx
    obtain ⟨g, hgT, hxg⟩ := hcover x hx
    exact Set.mem_iUnion₂.2 ⟨g, hgT, hx, hxg⟩
  apply hμ.2.1
  rw [← Measure.measure_univ_eq_zero]
  have hsplit : (Set.univ : Set (Formalism.QuantumDeterminants.Mt k r)) =
      {x | Matrix.of x ∈ UHk} ∪ {x | Matrix.of x ∉ UHk} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, true_iff]
    exact em _
  rw [hsplit]
  exact measure_union_null hUnull hμ.2.2.1

/- English proof (translation)
Use `hμW.1` as an intermediate fact. Use `hμN.1` as an intermediate fact. Set `S : Set (Formalism.QuantumDeterminants.Mt k r)` to `{x | Matrix.of x ∈ UHk}`. Set `G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞` to `S.piecewise (fun x => (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) (fun _ => 0)`. Establish `hSm : MeasurableSet S` using `uh_meas`.

Establish `hc1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX))` using `continuous_id`. Establish `hGc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) S`. Establish `h2 : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) S` using `hFc.comp hc1.continuousOn (fun x hx => hx)`. Conclude with `(ENNReal.continuous_pow 2).comp_continuousOn ((ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn h2)`. Establish `hGm : Measurable G` using `hGc.measurable_piecewise continuousOn_const hSm`.

Establish `hGle : ∀ x, G x ≤ (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2`. Introduce `x`. Distinguish the cases in `hx : x ∈ S`. Simplify using `[G, hx]`. Simplify using `[G, hx]`.

Establish `hνG : ∫⁻ x, G x ∂νq = 0`. Use `nonpos_iff_eq_zero.mp ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hGae : ∀ᵐ x ∂νq, G x = 0` using `(lintegral_eq_zero_iff hGm).1 hνG`. Establish `hGval : ∀ x, x ∈ S → G x = 0 → F (Matrix.of x) = 0`.

Introduce `x hx h0`. Simplify using `only [G, Set.piecewise, hx, if_true] at h0`. Establish `: (‖F (Matrix.of x)‖₊ : ℝ≥0∞) = 0` using `pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0`. Simplify using `using this`. Establish `hmul : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))`.

Establish `h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : MX))` using `continuous_fst`. Establish `h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : MX))` using `continuous_snd`. Conclude with `h1.matrix_mul h2`. Establish `hW : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z` using `Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hμW.2.2.1)`. Establish `hN : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r` using `Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 hμN.2.2.1)`.

Establish `hμGint : ∫⁻ x, G x ∂μG = 0`. Rewrite using `[hQ G hGm]`. Use `(lintegral_congr_ae ?_).trans lintegral_zero` and prove the remaining obligations. Use `filter_upwards [hGae] with x hx`. Use `show ∫⁻ s, G (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) = 0`.

Establish `hrm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => G (fun i j => (Matrix.of s * Matrix.of x) i j))` using `hGm.comp ((show Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r)) from hc1.matrix_mul continuous_const).measurable)`. Rewrite using `[Formalism.FourierDecayAlt.ThreeDimData.muSof, lintegral_map hrm hmul.measurable]`. Use `(lintegral_congr_ae ?_).trans lintegral_zero` and prove the remaining obligations. Use `filter_upwards [hW, hN] with p hp1 hp2`. Establish `hsU : Matrix.of p.1 * Matrix.of p.2 ∈ UHk` using `Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hp1.1 hp2.1`.

Use `show G (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j) = 0`. Distinguish the cases in `hxU : x ∈ S`. Establish `hFx` using `hGval x hxU hx`. Establish `hmem : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r) ∈ S` using `Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hsU hxU`. Simplify using `only [G, Set.piecewise, hmem, if_true]`.

Use `show (‖F (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 = 0`. Rewrite using `[hFeq _ hp1 _ hp2 (Matrix.of x) hxU, hFx, map_zero, smul_zero]`. Simplify using the standard rewrite rules. Establish `hnot : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r) ∉ S`. Introduce `hm`.

Conclude with `hxU (DDSmoothness.uh_cancel hsU hm)`. Simplify using `only [G, Set.piecewise, hnot, if_false]`. Establish `hGaeG : ∀ᵐ x ∂μG, G x = 0` using `(lintegral_eq_zero_iff hGm).1 hμGint`. Establish `hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UHk → F (Matrix.of x) = 0` using `by filter_upwards [hGaeG] with x hx hxU`. Conclude with `hGval x hxU hx`.

Introduce `g hg`. Conclude with `zero_of_ae hμG hFc hae hg`.
-/
theorem aez {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : MX → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hμN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hμG : PI.BesselPeriodGGP.IsHaarOn UHk μG)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) νq)
    (F : MX → Wp) (hFc : ContinuousOn F UHk)
    (hFeq : ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ UHk,
      F (h * n * g) = Formalism.QuantumDeterminants.psi k r z c n • π h (F g))
    (hl2 : PI.BesselPeriodGGP.l2SG νq F = 0) : ∀ g ∈ UHk, F g = 0 := by
  classical
  have := hμW.1
  have := hμN.1
  let S : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ UHk}
  let G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    S.piecewise (fun x => (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) (fun _ => 0)
  have hSm : MeasurableSet S := uh_meas
  have hc1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX)) := continuous_id
  have hGc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) S := by
    have h2 : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) S :=
      hFc.comp hc1.continuousOn (fun x hx => hx)
    exact (ENNReal.continuous_pow 2).comp_continuousOn
      ((ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn h2)
  have hGm : Measurable G := hGc.measurable_piecewise continuousOn_const hSm
  have hGle : ∀ x, G x ≤ (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
    intro x
    by_cases hx : x ∈ S
    · simp [G, hx]
    · simp [G, hx]
  have hνG : ∫⁻ x, G x ∂νq = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc ∫⁻ x, G x ∂νq ≤ ∫⁻ x, (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νq := lintegral_mono hGle
      _ = PI.BesselPeriodGGP.l2SG νq F := rfl
      _ = 0 := hl2
  have hGae : ∀ᵐ x ∂νq, G x = 0 := (lintegral_eq_zero_iff hGm).1 hνG
  have hGval : ∀ x, x ∈ S → G x = 0 → F (Matrix.of x) = 0 := by
    intro x hx h0
    simp only [G, Set.piecewise, hx, if_true] at h0
    have : (‖F (Matrix.of x)‖₊ : ℝ≥0∞) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
    simpa using this
  have hmul : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : MX)) := continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : MX)) := continuous_snd
    exact h1.matrix_mul h2
  have hW : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hμW.2.2.1)
  have hN : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 hμN.2.2.1)
  have hμGint : ∫⁻ x, G x ∂μG = 0 := by
    rw [hQ G hGm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hGae] with x hx
    show ∫⁻ s, G (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) = 0
    have hrm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r =>
        G (fun i j => (Matrix.of s * Matrix.of x) i j)) :=
      hGm.comp ((show Continuous (fun s : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r)) from
          hc1.matrix_mul continuous_const).measurable)
    rw [Formalism.FourierDecayAlt.ThreeDimData.muSof, lintegral_map hrm hmul.measurable]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hW, hN] with p hp1 hp2
    have hsU : Matrix.of p.1 * Matrix.of p.2 ∈ UHk := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hp1.1 hp2.1
    show G (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j) = 0
    by_cases hxU : x ∈ S
    · have hFx := hGval x hxU hx
      have hmem : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j :
          Formalism.QuantumDeterminants.Mt k r) ∈ S := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hsU hxU
      simp only [G, Set.piecewise, hmem, if_true]
      show (‖F (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 = 0
      rw [hFeq _ hp1 _ hp2 (Matrix.of x) hxU, hFx, map_zero, smul_zero]
      simp
    · have hnot : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j :
          Formalism.QuantumDeterminants.Mt k r) ∉ S := by
        intro hm
        exact hxU (DDSmoothness.uh_cancel hsU hm)
      simp only [G, Set.piecewise, hnot, if_false]
  have hGaeG : ∀ᵐ x ∂μG, G x = 0 := (lintegral_eq_zero_iff hGm).1 hμGint
  have hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UHk → F (Matrix.of x) = 0 := by
    filter_upwards [hGaeG] with x hx hxU
    exact hGval x hxU hx
  intro g hg
  exact zero_of_ae hμG hFc hae hg

end UnipotentHaarMeasurability

end Formalism.FourierDecayAlt.P
