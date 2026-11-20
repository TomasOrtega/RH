import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrameConjUnitaryBlockEqUnitaryComplement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Schur

/- English proof (translation)
Establish `hci : ∀ s : V, Integrable (fun x => ‖⟪s, f x⟫_ℂ‖ ^ 2) μ`. Introduce `s`. Use `Integrable.of_bound (((aestronglyMeasurable_const (b := s)).inner hf).norm.pow 2) ((‖s‖ * c) ^ 2) ?_` and prove the remaining obligations. Use `filter_upwards [hn] with x hx`. Rewrite using `[norm_pow, norm_norm, ← hx]`.

Conclude with `pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2`. Use `⟨hci w, ?_⟩` and prove the remaining obligations. Break down `subsingleton_or_nontrivial V with hV | hV` into its components or cases. Rewrite using `[Subsingleton.elim w 0]`. Simplify using the standard rewrite rules.

Use `haveI : CompleteSpace V := FiniteDimensional.complete ℂ V`. Set `Fy : V → X → V` to `fun y x => ⟪f x, y⟫_ℂ • f x`. Establish `hFm : ∀ y, AEStronglyMeasurable (Fy y) μ` using `fun y => (hf.inner (aestronglyMeasurable_const (b := y))).smul hf`. Establish `hFi : ∀ y, Integrable (Fy y) μ`. Introduce `y`.

Use `Integrable.of_bound (hFm y) (c * ‖y‖ * c) ?_` and prove the remaining obligations. Use `filter_upwards [hn] with x hx`. Simplify using `only [Fy]`. Rewrite using `[norm_smul, ← hx]`. Conclude with `mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)`.

Set `R : V →ₗ[ℂ] V` to `{ toFun := fun y => ∫ h, Fy y h ∂μ map_add' := by`. Introduce `y z`. Rewrite using `[← integral_add (hFi y) (hFi z)]`. Use `congr 1`. Use function extensionality and compare the values at `h`.

Simplify using `only [Fy, inner_add_right, add_smul]`. Use the proof step `map_smul' := by`. Introduce `c y`. Rewrite using `[RingHom.id_apply, ← integral_smul]`. Use `congr 1`.

Use function extensionality and compare the values at `h`. Simplify using `only [Fy, inner_smul_right, mul_smul] }`. Establish `hRdef : ∀ y, R y = ∫ h, Fy y h ∂μ` using `fun _ => rfl`. Establish `hcomm : ∀ i y, R (T i y) = T i (R y)`. Introduce `i y`.

Rewrite using `[hRdef, hRdef, ← (T i).integral_comp_comm (hFi y)]`. Establish `h1 : ∫ h, Fy (T i y) h ∂μ = ∫ h, Fy (T i y) (m i h) ∂μ`. Use `integral_map (μ := μ) (φ := m i) (hm i).measurable.aemeasurable (f := Fy (T i y)) (by rw [(hm i).map_eq]; exact hFm _)` as an intermediate fact. Rewrite `this` using `[(hm i).map_eq]`. Then use the resulting hypothesis. Rewrite using `[h1]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hfm i] with x hx`. Simplify using `only [Fy, hx, map_smul, hT]`. Take `⟨lam, hlam⟩` from `Module.End.exists_eigenvalue R`. Establish `hE : Module.End.eigenspace R lam = ⊤` using `(hirr _ (fun h x hx => by`.

Rewrite `hx`, the goal using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[hcomm, hx, map_smul])).resolve_left hlam`. Establish `hR : ∀ y, R y = lam • y` using `fun y => Module.End.mem_eigenspace_iff.mp (hE ▸ Submodule.mem_top)`. Establish `h4 : ∀ s : V, lam * ((‖s‖ ^ 2 : ℝ) : ℂ) = ((∫ h, ‖⟪s, f h⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ)`. Introduce `s`.

Establish `a : ⟪s, R s⟫_ℂ = lam * ((‖s‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[hR, inner_smul_right, inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression. Establish `b : ⟪s, R s⟫_ℂ = ∫ h, ⟪s, Fy s h⟫_ℂ ∂μ` using `(integral_inner (hFi s) s).symm`.

Establish `c : ∀ h, ⟪s, Fy s h⟫_ℂ = ((‖⟪s, f h⟫_ℂ‖ ^ 2 : ℝ) : ℂ)`. Introduce `h`. Simplify using `only [Fy, inner_smul_right]`. Rewrite using `[← inner_conj_symm (f h) s, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite using `[← a, b]`.

Repeatedly rewrite using `[c]`. Conclude with `integral_ofReal`. Establish `h5 : lam * (Module.finrank ℂ V : ℂ) = ((c ^ 2 : ℝ) : ℂ)`. Set `b` to `stdOrthonormalBasis ℂ V`. Establish `e1 : ∫ h, ∑ i, ‖⟪b i, f h⟫_ℂ‖ ^ 2 ∂μ = c ^ 2`.

Establish `: ∫ h, ∑ i, ‖⟪b i, f h⟫_ℂ‖ ^ 2 ∂μ = ∫ _h, c ^ 2 ∂μ`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hn] with x hx`. Rewrite using `[b.sum_sq_norm_inner_right, hx]`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Rewrite using `[← e1, integral_finsetSum _ fun i _ => hci (b i)]`. Use `push_cast`. Repeatedly rewrite using `[← h4]`. Establish `hb : ∀ i, ‖b i‖ = 1` using `fun i => b.orthonormal.1 i`.

Simplify using `[hb, mul_comm]`. Establish `hd : (Module.finrank ℂ V : ℂ) ≠ 0` using `by exact_mod_cast Module.finrank_pos.ne'`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← h4, Complex.ofReal_div, Complex.ofReal_mul, ← h5]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem avg_sq {X V ι : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (f : X → V) (hf : AEStronglyMeasurable f μ) (c : ℝ) (hn : ∀ᵐ x ∂μ, ‖f x‖ = c)
    (T : ι → V →L[ℂ] V) (hT : ∀ i a b, ⟪T i a, T i b⟫_ℂ = ⟪a, b⟫_ℂ)
    (m : ι → X → X) (hm : ∀ i, MeasurePreserving (m i) μ μ)
    (hfm : ∀ i, ∀ᵐ x ∂μ, f (m i x) = T i (f x))
    (hirr : ∀ S : Submodule ℂ V, (∀ i, ∀ v ∈ S, T i v ∈ S) → S = ⊥ ∨ S = ⊤) (w : V) :
    Integrable (fun x => ‖⟪w, f x⟫_ℂ‖ ^ 2) μ ∧
      ∫ x, ‖⟪w, f x⟫_ℂ‖ ^ 2 ∂μ = ‖w‖ ^ 2 * c ^ 2 / Module.finrank ℂ V := by
  have hci : ∀ s : V, Integrable (fun x => ‖⟪s, f x⟫_ℂ‖ ^ 2) μ := by
    intro s
    refine Integrable.of_bound (((aestronglyMeasurable_const (b := s)).inner hf).norm.pow 2)
      ((‖s‖ * c) ^ 2) ?_
    filter_upwards [hn] with x hx
    rw [norm_pow, norm_norm, ← hx]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  refine ⟨hci w, ?_⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [Subsingleton.elim w 0]; simp
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let Fy : V → X → V := fun y x => ⟪f x, y⟫_ℂ • f x
  have hFm : ∀ y, AEStronglyMeasurable (Fy y) μ := fun y =>
    (hf.inner (aestronglyMeasurable_const (b := y))).smul hf
  have hFi : ∀ y, Integrable (Fy y) μ := by
    intro y
    refine Integrable.of_bound (hFm y) (c * ‖y‖ * c) ?_
    filter_upwards [hn] with x hx
    simp only [Fy]
    rw [norm_smul, ← hx]
    exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
  let R : V →ₗ[ℂ] V :=
    { toFun := fun y => ∫ h, Fy y h ∂μ
      map_add' := by
        intro y z
        rw [← integral_add (hFi y) (hFi z)]
        congr 1; funext h; simp only [Fy, inner_add_right, add_smul]
      map_smul' := by
        intro c y
        rw [RingHom.id_apply, ← integral_smul]
        congr 1; funext h; simp only [Fy, inner_smul_right, mul_smul] }
  have hRdef : ∀ y, R y = ∫ h, Fy y h ∂μ := fun _ => rfl
  have hcomm : ∀ i y, R (T i y) = T i (R y) := by
    intro i y
    rw [hRdef, hRdef, ← (T i).integral_comp_comm (hFi y)]
    have h1 : ∫ h, Fy (T i y) h ∂μ = ∫ h, Fy (T i y) (m i h) ∂μ := by
      have := integral_map (μ := μ) (φ := m i) (hm i).measurable.aemeasurable (f := Fy (T i y))
        (by rw [(hm i).map_eq]; exact hFm _)
      rwa [(hm i).map_eq] at this
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hfm i] with x hx
    simp only [Fy, hx, map_smul, hT]
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue R
  have hE : Module.End.eigenspace R lam = ⊤ :=
    (hirr _ (fun h x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hcomm, hx, map_smul])).resolve_left hlam
  have hR : ∀ y, R y = lam • y := fun y =>
    Module.End.mem_eigenspace_iff.mp (hE ▸ Submodule.mem_top)
  have h4 : ∀ s : V, lam * ((‖s‖ ^ 2 : ℝ) : ℂ) = ((∫ h, ‖⟪s, f h⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro s
    have a : ⟪s, R s⟫_ℂ = lam * ((‖s‖ ^ 2 : ℝ) : ℂ) := by
      rw [hR, inner_smul_right, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have b : ⟪s, R s⟫_ℂ = ∫ h, ⟪s, Fy s h⟫_ℂ ∂μ := (integral_inner (hFi s) s).symm
    have c : ∀ h, ⟪s, Fy s h⟫_ℂ = ((‖⟪s, f h⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro h
      simp only [Fy, inner_smul_right]
      rw [← inner_conj_symm (f h) s, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← a, b]
    simp_rw [c]
    exact integral_ofReal
  have h5 : lam * (Module.finrank ℂ V : ℂ) = ((c ^ 2 : ℝ) : ℂ) := by
    let b := stdOrthonormalBasis ℂ V
    have e1 : ∫ h, ∑ i, ‖⟪b i, f h⟫_ℂ‖ ^ 2 ∂μ = c ^ 2 := by
      have : ∫ h, ∑ i, ‖⟪b i, f h⟫_ℂ‖ ^ 2 ∂μ = ∫ _h, c ^ 2 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hn] with x hx
        rw [b.sum_sq_norm_inner_right, hx]
      rw [this]; simp
    rw [← e1, integral_finsetSum _ fun i _ => hci (b i)]
    push_cast
    simp_rw [← h4]
    have hb : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
    simp [hb, mul_comm]
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  apply Complex.ofReal_injective
  rw [← h4, Complex.ofReal_div, Complex.ofReal_mul, ← h5]
  push_cast
  field_simp

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

/- English proof (translation)
Establish `hπ' : PI.UpqRep.IsHCTypeW k r z u π` using `hπ`. Take `⟨h1, h2, h3, h4⟩` from `Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ'`. Take `⟨g, hg, hρ⟩` from `hπ`. Use `⟨hρ.1, ⟨⟨h1, h2⟩, h3, h4⟩, fun S _ hS => ?_⟩` and prove the remaining obligations. Use `hρ.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ ?_ v hv` and prove the remaining obligations.

Establish `hg' : PI.UpqRep.IsFrameW k r z g` using `hg`. Establish `hx' : x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k)` using `PI.HwUniqW.mem_UJset_allPos.mpr (Matrix.mem_unitaryGroup_iff'.mp hx.1)`. Conclude with `GlobalTheory.BesselFrame.conj_mem_UW hg' hx'`.
-/
theorem type_irred {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} (hT : 0 < Tz k r z)
    {u : Fin k → ℝ} (hπ : IsHCTypeW k r z u π) :
    Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π := by
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨h1, h2, h3, h4⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ'
  obtain ⟨g, hg, hρ⟩ := hπ
  refine ⟨hρ.1, ⟨⟨h1, h2⟩, h3, h4⟩, fun S _ hS => ?_⟩
  refine hρ.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ ?_ v hv
  have hg' : PI.UpqRep.IsFrameW k r z g := hg
  have hx' : x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k) :=
    PI.HwUniqW.mem_UJset_allPos.mpr (Matrix.mem_unitaryGroup_iff'.mp hx.1)
  exact GlobalTheory.BesselFrame.conj_mem_UW hg' hx'

/- English proof (translation)
Use `haveI : IsProbabilityMeasure μW := ⟨h1⟩`. Establish `hW` using `isClosedSub_UWset (k := k) (r := r) z`. Establish `hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z` using `ae_iff.mpr hH.2.2.1`. Establish `hof : Continuous (fun y : Mt k r => (Matrix.of y : Mat k r))` using `continuous_id`. Establish `hf : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x) ξ) μW`.

Establish `hc : ContinuousOn (fun x : Mt k r => π (Matrix.of x) ξ) {x : Mt k r | Matrix.of x ∈ UWset k r z}` using `hU.2.2 ξ`. Use `hc.aestronglyMeasurable (μ := μW) (hW.2.1.preimage hof).measurableSet` as an intermediate fact. Rewrite `this` using `[Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r z}) hae]`. Then use the resulting hypothesis. Establish `hlm : ∀ s : Mat k r, Continuous (lmulM s : Mt k r → Mt k r)` using `fun s => (continuous_const (y := s)).matrix_mul hof`. Take `⟨hi, hv⟩` from `avg_sq μW (fun x : Mt k r => π (Matrix.of x) ξ) hf ‖ξ‖ (hae.mono fun x hx => hU.2.1 _ hx ξ) (fun s : UWset k r z => π s) (fun s => (LinearMap.norm_map_iff_inner_map_map ((π s : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1 (hU.2.1 s s.2)) (fun s => lmulM (s : Mat k r)) (fun s => ⟨(hlm s).measur …`.

Rewrite using `[← hv, ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]`. Both sides reduce to the same expression.
-/
theorem avg_UW [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    {μW : Measure (Mt k r)} (hU : IsURepOn (UWset k r z) π) (hI : IsIrredOn (UWset k r z) π)
    (hH : IsHaarOn (UWset k r z) μW) (h1 : μW Set.univ = 1) (w ξ : Wp) :
    ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW =
      ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) := by
  haveI : IsProbabilityMeasure μW := ⟨h1⟩
  have hW := isClosedSub_UWset (k := k) (r := r) z
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := ae_iff.mpr hH.2.2.1
  have hof : Continuous (fun y : Mt k r => (Matrix.of y : Mat k r)) := continuous_id
  have hf : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x) ξ) μW := by
    have hc : ContinuousOn (fun x : Mt k r => π (Matrix.of x) ξ) {x : Mt k r | Matrix.of x ∈ UWset k r z} :=
      hU.2.2 ξ
    have := hc.aestronglyMeasurable (μ := μW) (hW.2.1.preimage hof).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r z}) hae] at this
  have hlm : ∀ s : Mat k r, Continuous (lmulM s : Mt k r → Mt k r) := fun s =>
    (continuous_const (y := s)).matrix_mul hof
  obtain ⟨hi, hv⟩ := avg_sq μW (fun x : Mt k r => π (Matrix.of x) ξ) hf ‖ξ‖
    (hae.mono fun x hx => hU.2.1 _ hx ξ) (fun s : UWset k r z => π s)
    (fun s => (LinearMap.norm_map_iff_inner_map_map ((π s : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1 (hU.2.1 s s.2))
    (fun s => lmulM (s : Mat k r))
    (fun s => ⟨(hlm s).measurable, hH.2.2.2 s s.2⟩)
    (fun s => hae.mono fun x hx => DFunLike.congr_fun (hU.1.2 s s.2 _ hx) ξ)
    (fun S hS => hI S S.closed_of_finiteDimensional fun g hg => hS ⟨g, hg⟩) w
  rw [← hv, ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ hT` and use `⟨fun _ hπ => type_irred hT hπ, fun _ hU hI hH h1 w ξ => avg_UW hU hI hH h1 w ξ⟩`.
-/
theorem type_irred_and_avg : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → (∀ u, IsHCTypeW k r z u π → Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π) ∧ ∀ μW : Measure (Mt k r), IsURepOn (UWset k r z) π → IsIrredOn (UWset k r z) π → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → ∀ w ξ : Wp, ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW = ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) :=
  fun _ _ _ _ _ _ _ _ _ hT => ⟨fun _ hπ => type_irred hT hπ, fun _ hU hI hH h1 w ξ => avg_UW hU hI hH h1 w ξ⟩

end GlobalTheory.Amp.Schur
