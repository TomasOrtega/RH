import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviFormGbPotOne
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

def openAtlas {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    FinHolAtlas D Ω where
  n := 1
  chart _ := Ω.openPartialHomeomorphSubtypeCoe hΩ
  cover _ := ⟨0, by simp⟩
  holo _ _ := by
    intro y hy
    have hy' : y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target := hy.1
    have hev : (Ω.openPartialHomeomorphSubtypeCoe hΩ ∘ (Ω.openPartialHomeomorphSubtypeCoe hΩ).symm)
        =ᶠ[𝓝 y] id := by
      filter_upwards [(Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target.mem_nhds hy'] with z hz
      exact (Ω.openPartialHomeomorphSubtypeCoe hΩ).right_inv hz
    exact analyticAt_id.congr hev.symm

/- English proof (translation)
Establish `hy' : y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target` using `by simpa using hy`. Use `filter_upwards [(Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target.mem_nhds hy'] with z hz`. Establish `h` using `(Ω.openPartialHomeomorphSubtypeCoe hΩ).right_inv hz`. Simplify using `only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] at h`. Express the relevant statement in the definitionally equal form `F ((Ω.openPartialHomeomorphSubtypeCoe hΩ).symm z : Fin D → ℂ) = F z`.

Rewrite using `[h]`.
-/
theorem openAtlas_symm_eventuallyEq {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ))
    (hΩ : Nonempty Ω) (j : Fin (openAtlas Ω hΩ).n) (F : (Fin D → ℂ) → ℝ) {y : Fin D → ℂ}
    (hy : y ∈ Ω) :
    (fun z => F (((openAtlas Ω hΩ).chart j).symm z : Fin D → ℂ)) =ᶠ[𝓝 y] F := by
  have hy' : y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target := by simpa using hy
  filter_upwards [(Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target.mem_nhds hy'] with z hz
  have h := (Ω.openPartialHomeomorphSubtypeCoe hΩ).right_inv hz
  simp only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] at h
  change F ((Ω.openPartialHomeomorphSubtypeCoe hΩ).symm z : Fin D → ℂ) = F z
  rw [h]

def openAtlasPartition {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    ChartPartition (openAtlas Ω hΩ) where
  χ _ _ := 1
  smooth _ _ := contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := by
    change _ ⊆ (Ω.openPartialHomeomorphSubtypeCoe hΩ).source
    simp
  sum_eq_one _ := by
    change ∑ _ : Fin 1, (1 : ℝ) = 1
    simp

instance {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    Subsingleton (Fin (openAtlas Ω hΩ).n) :=
  (inferInstance : Subsingleton (Fin 1))

/- English proof (translation)
Establish `hne : Nonempty (ChartPartition (openAtlas Ω hΩ))` using `⟨openAtlasPartition Ω hΩ⟩`. Set `j : Fin (openAtlas Ω hΩ).n` to `⟨0, Nat.one_pos⟩`. Establish `hχ : ∀ x, hne.some.χ j x = 1`. Introduce `x`. Establish `h` using `hne.some.sum_eq_one x`.

Rewrite `h` using `[Fintype.sum_subsingleton _ j]`. Then use the resulting hypothesis. Establish `hT : ((openAtlas Ω hΩ).chart j).target = (Ω : Set (Fin D → ℂ))`. Express the relevant statement in the definitionally equal form `(Ω.openPartialHomeomorphSubtypeCoe hΩ).target = _`. Simplify using the standard rewrite rules. Establish `hmeas : AEMeasurable ((openAtlas Ω hΩ).chart j).symm (volume.restrict ((openAtlas Ω hΩ).chart j).target)` using `((openAtlas Ω hΩ).chart j).continuousOn_symm.aemeasurable ((openAtlas Ω hΩ).chart j).open_target.measurableSet`.

Rewrite using `[maMeasure, dif_pos hne, Measure.finsetSum_apply, Fintype.sum_subsingleton _ j, Measure.map_apply_of_aemeasurable (hmeas.mono_ac (withDensity_absolutelyContinuous _ _)) MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hT]`. Use `setLIntegral_congr_fun Ω.isOpen.measurableSet fun y hy => ?_` and prove the remaining obligations. Rewrite using `[hχ, one_mul]`. Use `congr 1`. Establish `hev : (fun z => Q.φ (((openAtlas Ω hΩ).chart j).symm y) (((openAtlas Ω hΩ).chart j).symm z)) =ᶠ[𝓝 y] fun z => F z / 2` using `by filter_upwards [openAtlas_symm_eventuallyEq Ω hΩ j F hy] with z hz`.

Rewrite using `[hQ, hz]`. Establish `hH` using `(hev.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)`. Unfold `locDens topDens maDens maDensity mdisc mixedDisc hessC cxHessian`. Simplify using `only [hH]`.
-/
theorem openAtlas_mass {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω)
    (Q : LocPot Ω) (F : (Fin D → ℂ) → ℝ) (hQ : ∀ x z, Q.φ x z = F z / 2) :
    maMeasure (openAtlas Ω hΩ) (fun _ => Q) Set.univ =
      ∫⁻ z in (Ω : Set (Fin D → ℂ)), ENNReal.ofReal (topDens F z) := by
  have hne : Nonempty (ChartPartition (openAtlas Ω hΩ)) := ⟨openAtlasPartition Ω hΩ⟩
  let j : Fin (openAtlas Ω hΩ).n := ⟨0, Nat.one_pos⟩
  have hχ : ∀ x, hne.some.χ j x = 1 := by
    intro x
    have h := hne.some.sum_eq_one x
    rwa [Fintype.sum_subsingleton _ j] at h
  have hT : ((openAtlas Ω hΩ).chart j).target = (Ω : Set (Fin D → ℂ)) := by
    change (Ω.openPartialHomeomorphSubtypeCoe hΩ).target = _
    simp
  have hmeas : AEMeasurable ((openAtlas Ω hΩ).chart j).symm
      (volume.restrict ((openAtlas Ω hΩ).chart j).target) :=
    ((openAtlas Ω hΩ).chart j).continuousOn_symm.aemeasurable
      ((openAtlas Ω hΩ).chart j).open_target.measurableSet
  rw [maMeasure, dif_pos hne, Measure.finsetSum_apply, Fintype.sum_subsingleton _ j,
    Measure.map_apply_of_aemeasurable (hmeas.mono_ac (withDensity_absolutelyContinuous _ _))
      MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hT]
  refine setLIntegral_congr_fun Ω.isOpen.measurableSet fun y hy => ?_
  rw [hχ, one_mul]
  congr 1
  have hev : (fun z => Q.φ (((openAtlas Ω hΩ).chart j).symm y)
      (((openAtlas Ω hΩ).chart j).symm z)) =ᶠ[𝓝 y] fun z => F z / 2 := by
    filter_upwards [openAtlas_symm_eventuallyEq Ω hΩ j F hy] with z hz
    rw [hQ, hz]
  have hH := (hev.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  unfold locDens topDens maDens maDensity mdisc mixedDisc hessC cxHessian
  simp only [hH]

/- English proof (translation)
Introduce `j`. Establish `hsub : ((openAtlas Ω hΩ).chart j).target ∩ ((openAtlas Ω hΩ).chart j).symm ⁻¹' Set.univ ⊆ (Ω : Set (Fin D → ℂ))`. Introduce `y hy`. Establish `h` using `hy.1`. Express the relevant statement in the definitionally equal form `y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target at h`.

Simplify using `using h`. Conclude with `(hF.mono hsub).congr fun y hy => (openAtlas_symm_eventuallyEq Ω hΩ j F (hsub hy)).eq_of_nhds`.
-/
theorem openAtlas_smooth {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω)
    (F : (Fin D → ℂ) → ℝ) (hF : ContDiffOn ℝ ∞ F Ω) :
    (openAtlas Ω hΩ).Smooth fun x => F x := by
  intro j
  have hsub : ((openAtlas Ω hΩ).chart j).target ∩ ((openAtlas Ω hΩ).chart j).symm ⁻¹' Set.univ ⊆
      (Ω : Set (Fin D → ℂ)) := by
    intro y hy
    have h := hy.1
    change y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target at h
    simpa using h
  exact (hF.mono hsub).congr fun y hy =>
    (openAtlas_symm_eventuallyEq Ω hΩ j F (hsub hy)).eq_of_nhds

/- English proof (translation)
Introduce `x j y hy w`. Establish `hyΩ : y ∈ (Ω : Set (Fin D → ℂ))`. Establish `h` using `hy.1`. Express the relevant statement in the definitionally equal form `y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target at h`. Simplify using `using h`.

Establish `hev : (Q.φ x ∘ ((openAtlas Ω hΩ).chart j).symm) =ᶠ[𝓝 y] fun z => (fun _ => (0 : ℝ)) z + (1 / 2 : ℝ) * F z` using `by filter_upwards [openAtlas_symm_eventuallyEq Ω hΩ j F hyΩ] with z hz`. Simplify using `only [Function.comp_apply, hQ, hz]`. Expand and normalize the polynomial expressions, which then agree. Establish `hC : ContDiffAt ℝ 2 F y` using `(hF.contDiffAt (Ω.isOpen.mem_nhds hyΩ)).of_le (WithTop.coe_le_coe.2 le_top)`. Rewrite using `[levi_congr hev, levi_add_smul (f := fun _ => (0 : ℝ)) (1 / 2) contDiffAt_const hC]`.

Establish `h0 : levi (fun _ : Fin D → ℂ => (0 : ℝ)) y w = 0` using `by simp [levi]`. Establish `h1 : levi F y w = leviForm F y w` using `rfl`. Establish `h2` using `hL y hyΩ w`. Rewrite using `[h0, h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem openAtlas_isPsh {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω)
    (Q : LocPot Ω) (F : (Fin D → ℂ) → ℝ) (hQ : ∀ x z, Q.φ x z = F z / 2)
    (hF : ContDiffOn ℝ ∞ F Ω) (hL : ∀ z ∈ (Ω : Set (Fin D → ℂ)), ∀ w, 0 ≤ leviForm F z w) :
    IsPsh (openAtlas Ω hΩ) Q := by
  intro x j y hy w
  have hyΩ : y ∈ (Ω : Set (Fin D → ℂ)) := by
    have h := hy.1
    change y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target at h
    simpa using h
  have hev : (Q.φ x ∘ ((openAtlas Ω hΩ).chart j).symm) =ᶠ[𝓝 y]
      fun z => (fun _ => (0 : ℝ)) z + (1 / 2 : ℝ) * F z := by
    filter_upwards [openAtlas_symm_eventuallyEq Ω hΩ j F hyΩ] with z hz
    simp only [Function.comp_apply, hQ, hz]
    ring
  have hC : ContDiffAt ℝ 2 F y :=
    (hF.contDiffAt (Ω.isOpen.mem_nhds hyΩ)).of_le (WithTop.coe_le_coe.2 le_top)
  rw [levi_congr hev, levi_add_smul (f := fun _ => (0 : ℝ)) (1 / 2) contDiffAt_const hC]
  have h0 : levi (fun _ : Fin D → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
  have h1 : levi F y w = leviForm F y w := rfl
  have h2 := hL y hyΩ w
  rw [h0, h1]
  linarith

/- English proof (translation)
Introduce `hA D Ω φ a b hyp`. Take `⟨hΩo, hφ, ha, hb, hpa, hpb, hK⟩` from `hyp`. Break down `Set.eq_empty_or_nonempty Ω with h0 | hne` into its components or cases. Simplify using `[h0]`. Set `U : TopologicalSpace.Opens (Fin D → ℂ)` to `⟨Ω, hΩo⟩`.

Establish `hU : Nonempty U` using `hne.to_subtype`. Set `P : LocPot U` to `LocPot.ofFun fun x => φ x / 2`. Establish `hsum : ∀ c : (Fin D → ℂ) → ℝ, ∀ x z, (P + LocPot.ofFun fun x : U => c x / 2).φ x z = (φ + c) z / 2`. Introduce `c x z`. Express the relevant statement in the definitionally equal form `φ z / 2 + c z / 2 = _`.

Rewrite using `[Pi.add_apply, add_div]`. Establish `key` using `hA (openAtlas U hU) P (fun x => a x / 2) (fun x => b x / 2) ⟨isPotential_ofFun _ _ (openAtlas_smooth U hU (fun z => φ z / 2) (hφ.div_const 2)), openAtlas_smooth U hU (fun z => a z / 2) (ha.div_const 2), openAtlas_smooth U hU (fun z => b z / 2) (hb.div_const 2), openAtlas_isPsh U …`. Rewrite `key` using `[openAtlas_mass U hU _ _ (hsum b), openAtlas_mass U hU _ _ (hsum a)]`. Conclude with `key`. Rewrite using `[Subtype.isCompact_iff]`.

Use `hK (2 * k) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `only [Set.mem_ofPred_eq] at hx`.

Conclude with `⟨x.2, by linarith⟩`. Introduce and unpack `⟨hz, h⟩`. Conclude with `⟨⟨z, hz⟩, by simp only [Set.mem_ofPred_eq]; linarith, rfl⟩`.
-/
theorem MAComparison.of_manifold :
    GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison.Statement → MAComparison.Statement := by
  intro hA D Ω φ a b hyp
  obtain ⟨hΩo, hφ, ha, hb, hpa, hpb, hK⟩ := hyp
  rcases Set.eq_empty_or_nonempty Ω with h0 | hne
  · simp [h0]
  let U : TopologicalSpace.Opens (Fin D → ℂ) := ⟨Ω, hΩo⟩
  have hU : Nonempty U := hne.to_subtype
  let P : LocPot U := LocPot.ofFun fun x => φ x / 2
  have hsum : ∀ c : (Fin D → ℂ) → ℝ, ∀ x z,
      (P + LocPot.ofFun fun x : U => c x / 2).φ x z = (φ + c) z / 2 := by
    intro c x z
    change φ z / 2 + c z / 2 = _
    rw [Pi.add_apply, add_div]
  have key := hA (openAtlas U hU) P (fun x => a x / 2) (fun x => b x / 2)
    ⟨isPotential_ofFun _ _ (openAtlas_smooth U hU (fun z => φ z / 2) (hφ.div_const 2)),
     openAtlas_smooth U hU (fun z => a z / 2) (ha.div_const 2),
     openAtlas_smooth U hU (fun z => b z / 2) (hb.div_const 2),
     openAtlas_isPsh U hU _ (φ + a) (hsum a) (hφ.add ha) hpa,
     openAtlas_isPsh U hU _ (φ + b) (hsum b) (hφ.add hb) hpb, fun k => ?_⟩
  · rw [openAtlas_mass U hU _ _ (hsum b), openAtlas_mass U hU _ _ (hsum a)] at key
    exact key
  · rw [Subtype.isCompact_iff]
    convert hK (2 * k) using 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq] at hx
      exact ⟨x.2, by linarith⟩
    · rintro ⟨hz, h⟩
      exact ⟨⟨z, hz⟩, by simp only [Set.mem_ofPred_eq]; linarith, rfl⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
