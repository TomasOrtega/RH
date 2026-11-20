import Formalism.PeriodIntegrals.AmpRootH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupHaar.ContinuousGS

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace PI.AmpRootHaarW

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon PI.AmpRootJacW

/- English proof (translation)
Use extensionality with `A hA`. Establish `hAS : MeasurableSet (A ∩ S)` using `hA.inter hS`. Establish `himg : MeasurableSet (f '' (A ∩ S))` using `hAS.image_of_continuousOn_injOn hf.continuousOn (hinj.mono Set.inter_subset_right)`. Establish `hpre : f ⁻¹' (f '' (A ∩ S)) ∩ S = A ∩ S`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨y, hy, hxy⟩, hx⟩`. Rewrite using `[← hinj hy.2 hx hxy]`. Conclude with `hy`. Introduce `hx`.

Conclude with `⟨⟨x, hx, rfl⟩, hx.2⟩`. Establish `key : ∀ ρ : Measure α, ρ Sᶜ = 0 → ρ A = ρ.map f (f '' (A ∩ S))`. Introduce `ρ hρ`. Rewrite using `[Measure.map_apply hf.measurable himg, ← measure_inter_conull (s := A) hρ, ← measure_inter_conull (s := f ⁻¹' (f '' (A ∩ S))) hρ, hpre]`. Rewrite using `[key μ hμ, key ν hν, h]`.
-/
theorem ext_of_injOn {α β : Type*} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [T2Space β] [MeasurableSpace β] [BorelSpace β] {f : α → β} {S : Set α}
    (hS : MeasurableSet S) (hf : Continuous f) (hinj : Set.InjOn f S) {μ ν : Measure α}
    (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0) (h : μ.map f = ν.map f) : μ = ν := by
  ext A hA
  have hAS : MeasurableSet (A ∩ S) := hA.inter hS
  have himg : MeasurableSet (f '' (A ∩ S)) :=
    hAS.image_of_continuousOn_injOn hf.continuousOn (hinj.mono Set.inter_subset_right)
  have hpre : f ⁻¹' (f '' (A ∩ S)) ∩ S = A ∩ S := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hxy⟩, hx⟩
      rw [← hinj hy.2 hx hxy]
      exact hy
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, hx.2⟩
  have key : ∀ ρ : Measure α, ρ Sᶜ = 0 → ρ A = ρ.map f (f '' (A ∩ S)) := by
    intro ρ hρ
    rw [Measure.map_apply hf.measurable himg, ← measure_inter_conull (s := A) hρ,
      ← measure_inter_conull (s := f ⁻¹' (f '' (A ∩ S))) hρ, hpre]
  rw [key μ hμ, key ν hν, h]

/- English proof (translation)
Introduce `k r L p g₀ μ₀ hc hrep hG hnull hmap`. Take `⟨hg, hP⟩` from `hrep`. Establish `hz` using `L.hz.1`. Establish `hz'` using `L.hz'.1`. Use `set c : ℝ≥0∞ := ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) with hc_def`.

Use `set φ : Mt k r → Mt k r := fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j with hφ`. Use `set S : Set (Mt k r) := {x | Matrix.of x ∈ RStab k r g₀} with hS_def`. Use `set f := rootCoords k r L.z p with hf_def`. Establish `hφm : Measurable φ` using `measurable_conjM g₀ g₀⁻¹`. Establish `hSm : MeasurableSet S` using `measurableSet_RStab g₀`.

Establish `hfc : Continuous f` using `continuous_rootCoords L.z p`. Establish `hdet : (gramM k r L.z L.z' g₀).det ≠ 0`. Introduce `h0`. Establish `e` using `group_gram_holds k r L.z L.z' hz hz' g₀ hg`. Rewrite `e` using `[h0, mul_zero]`.

Establish `e' : Gf k r L.z L.z' g₀ = 0` using `by exact_mod_cast e`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinj : Set.InjOn f S` using `rootCoords_injOn hz hz' hg hP hdet`. Establish `hφS : ∀ x, Matrix.of x ∈ Rset k r g₀ → φ x ∈ S`. Introduce `x hx`.

Use `⟨hx.2, ?_⟩` and prove the remaining obligations. Use `show g₀⁻¹ * (g₀ * Matrix.of x * g₀⁻¹) * g₀ ∈ Nset k r`. Rewrite using `[conj_back hg]`. Conclude with `hx.1`. Establish `hnullS : μ₀.map φ Sᶜ = 0`.

Rewrite using `[Measure.map_apply hφm hSm.compl]`. Use `measure_mono_null ?_ hnull` and prove the remaining obligations. Introduce `x hx hxR`. Conclude with `hx (hφS x hxR)`. Establish `hνf : (μ₀.map φ).map f = c • volume`.

Rewrite using `[Measure.map_map hfc.measurable hφm]`. Establish `hR : ∀ᵐ x ∂μ₀, Matrix.of x ∈ Rset k r g₀` using `ae_iff.2 hnull`. Establish `hae : f ∘ φ =ᵐ[μ₀] phiR p ∘ rootCoords k r L.z' p` using `by filter_upwards [hR] with x hx`. Conclude with `rootCoords_conj hz hz' hg hP hx`. Rewrite using `[Measure.map_congr hae, ← Measure.map_map (phiR_mp p).measurable (continuous_rootCoords L.z' p).measurable, hmap, Measure.map_smul, (phiR_mp p).map_eq]`.

Establish `hc0 : c ≠ 0`. Rewrite using `[hc_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]`. Conclude with `pow_pos (div_pos (norm_pos_iff.2 hc) (by positivity)) _`. Establish `hsf : SigmaFinite (μ₀.map φ)`. Use `SigmaFinite.of_map _ hfc.measurable.aemeasurable ?_` and prove the remaining obligations.

Rewrite using `[hνf, ← ENNReal.coe_toNNReal (show c ≠ ⊤ from by rw [hc_def]; exact ENNReal.ofReal_ne_top), ← ENNReal.smul_def]`. Use `infer_instance`. Establish `hne : μ₀.map φ ≠ 0`. Introduce `h0`. Establish `e` using `hνf`.

Rewrite `e` using `[h0, Measure.map_zero]`. Establish `e2` using `congrArg (fun m : Measure (rootPat p → ℂ) => m Set.univ) e`. Simplify using `only [Measure.coe_zero, Pi.zero_apply, Measure.smul_apply, smul_eq_mul] at e2`. Break down `mul_eq_zero.1 e2.symm with h | h` into its components or cases. Conclude with `hc0 h`.

Conclude with `NeZero.ne (volume : Measure (rootPat p → ℂ)) (Measure.measure_univ_eq_zero.1 h)`. Use `⟨hsf, hne, hnullS, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Establish `hlm : Measurable (lmulM s : Mt k r → Mt k r)`. Use `measurable_conjM (k := k) (r := r) s 1 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x i j`. Simplify using `[lmulM]`. Establish `hνS : S ∈ ae (μ₀.map φ)` using `mem_ae_iff.2 hnullS`. Establish `hone : ∀ (v : rootPat p → ℂ) (q : rootPat p), (1 + vM (rootPat p) v) q.1.1 q.1.2 = v q`. Introduce `v q`.

Rewrite using `[Matrix.add_apply, vM_at, Matrix.one_apply_ne (ne_of_lt (rootPat_lt p q.1 q.2)), zero_add]`. Use `set s' := f (fun i j => s i j) with hs'`. Use `ext_of_injOn hSm hfc hinj ?_ hnullS ?_` and prove the remaining obligations. Rewrite using `[Measure.map_apply hlm hSm.compl]`. Use `measure_mono_null ?_ hnullS` and prove the remaining obligations.

Introduce `y hy hyS`. Apply `hy` to reduce the goal to its premises. Use `show s * Matrix.of y ∈ RStab k r g₀`. Conclude with `rstab_mul' hg hs hyS`. Rewrite using `[Measure.map_map hfc.measurable hlm]`.

Establish `hae : f ∘ lmulM s =ᵐ[μ₀.map φ] (fun v q => v q + gS p s' q v) ∘ f` using `by filter_upwards [hνS] with y hy`. Use function extensionality and compare the values at `q`. Establish `hsy : s * Matrix.of y ∈ RStab k r g₀` using `rstab_mul' hg hs hy`. Establish `e1` using `flagZ_eq hz hz' hg hP hsy`. Establish `e2` using `flagMat_mul hz hs.1 hy.1`.

Establish `e3` using `flagZ_eq hz hz' hg hP hs`. Establish `e4` using `flagZ_eq hz hz' hg hP (a := Matrix.of y) hy`. Establish `e5 : 1 + vM (rootPat p) (f (fun i j => (s * Matrix.of y) i j)) = (1 + vM (rootPat p) s') * (1 + vM (rootPat p) (f y))`. Rewrite using `[← e1, e2, e3, e4]`. Apply the tactic sequence `all_goals rfl`.

Establish `e6` using `congrFun (congrFun e5 q.1.1) q.1.2`. Rewrite `e6` using `[hone, lm_eq]`. Conclude with `e6`. Rewrite using `[Measure.map_congr hae, ← Measure.map_map (lm_mp p s').measurable hfc.measurable, hνf, Measure.map_smul, (lm_mp p s').map_eq]`.
-/
theorem rootHaar_main : PI.AmpRootH.RootHaar := by
  intro k r L p g₀ μ₀ hc hrep hG hnull hmap
  obtain ⟨hg, hP⟩ := hrep
  have hz := L.hz.1
  have hz' := L.hz'.1
  set c : ℝ≥0∞ := ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) with hc_def
  set φ : Mt k r → Mt k r := fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j with hφ
  set S : Set (Mt k r) := {x | Matrix.of x ∈ RStab k r g₀} with hS_def
  set f := rootCoords k r L.z p with hf_def
  have hφm : Measurable φ := measurable_conjM g₀ g₀⁻¹
  have hSm : MeasurableSet S := measurableSet_RStab g₀
  have hfc : Continuous f := continuous_rootCoords L.z p
  have hdet : (gramM k r L.z L.z' g₀).det ≠ 0 := by
    intro h0
    have e := group_gram_holds k r L.z L.z' hz hz' g₀ hg
    rw [h0, mul_zero] at e
    have e' : Gf k r L.z L.z' g₀ = 0 := by exact_mod_cast e
    linarith
  have hinj : Set.InjOn f S := rootCoords_injOn hz hz' hg hP hdet
  have hφS : ∀ x, Matrix.of x ∈ Rset k r g₀ → φ x ∈ S := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    show g₀⁻¹ * (g₀ * Matrix.of x * g₀⁻¹) * g₀ ∈ Nset k r
    rw [conj_back hg]
    exact hx.1
  have hnullS : μ₀.map φ Sᶜ = 0 := by
    rw [Measure.map_apply hφm hSm.compl]
    refine measure_mono_null ?_ hnull
    intro x hx hxR
    exact hx (hφS x hxR)
  have hνf : (μ₀.map φ).map f = c • volume := by
    rw [Measure.map_map hfc.measurable hφm]
    have hR : ∀ᵐ x ∂μ₀, Matrix.of x ∈ Rset k r g₀ := ae_iff.2 hnull
    have hae : f ∘ φ =ᵐ[μ₀] phiR p ∘ rootCoords k r L.z' p := by
      filter_upwards [hR] with x hx
      exact rootCoords_conj hz hz' hg hP hx
    rw [Measure.map_congr hae, ← Measure.map_map (phiR_mp p).measurable
      (continuous_rootCoords L.z' p).measurable, hmap, Measure.map_smul, (phiR_mp p).map_eq]
  have hc0 : c ≠ 0 := by
    rw [hc_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (div_pos (norm_pos_iff.2 hc) (by positivity)) _
  have hsf : SigmaFinite (μ₀.map φ) := by
    refine SigmaFinite.of_map _ hfc.measurable.aemeasurable ?_
    rw [hνf, ← ENNReal.coe_toNNReal (show c ≠ ⊤ from by rw [hc_def]; exact ENNReal.ofReal_ne_top),
      ← ENNReal.smul_def]
    infer_instance
  have hne : μ₀.map φ ≠ 0 := by
    intro h0
    have e := hνf
    rw [h0, Measure.map_zero] at e
    have e2 := congrArg (fun m : Measure (rootPat p → ℂ) => m Set.univ) e
    simp only [Measure.coe_zero, Pi.zero_apply, Measure.smul_apply, smul_eq_mul] at e2
    rcases mul_eq_zero.1 e2.symm with h | h
    · exact hc0 h
    · exact NeZero.ne (volume : Measure (rootPat p → ℂ)) (Measure.measure_univ_eq_zero.1 h)
  refine ⟨hsf, hne, hnullS, ?_⟩
  intro s hs
  have hlm : Measurable (lmulM s : Mt k r → Mt k r) := by
    convert measurable_conjM (k := k) (r := r) s 1 using 1
    funext x i j
    simp [lmulM]
  have hνS : S ∈ ae (μ₀.map φ) := mem_ae_iff.2 hnullS
  have hone : ∀ (v : rootPat p → ℂ) (q : rootPat p), (1 + vM (rootPat p) v) q.1.1 q.1.2 = v q := by
    intro v q
    rw [Matrix.add_apply, vM_at, Matrix.one_apply_ne (ne_of_lt (rootPat_lt p q.1 q.2)), zero_add]
  set s' := f (fun i j => s i j) with hs'
  refine ext_of_injOn hSm hfc hinj ?_ hnullS ?_
  · rw [Measure.map_apply hlm hSm.compl]
    refine measure_mono_null ?_ hnullS
    intro y hy hyS
    apply hy
    show s * Matrix.of y ∈ RStab k r g₀
    exact rstab_mul' hg hs hyS
  · rw [Measure.map_map hfc.measurable hlm]
    have hae : f ∘ lmulM s =ᵐ[μ₀.map φ] (fun v q => v q + gS p s' q v) ∘ f := by
      filter_upwards [hνS] with y hy
      funext q
      have hsy : s * Matrix.of y ∈ RStab k r g₀ := rstab_mul' hg hs hy
      have e1 := flagZ_eq hz hz' hg hP hsy
      have e2 := flagMat_mul hz hs.1 hy.1
      have e3 := flagZ_eq hz hz' hg hP hs
      have e4 := flagZ_eq hz hz' hg hP (a := Matrix.of y) hy
      have e5 : 1 + vM (rootPat p) (f (fun i j => (s * Matrix.of y) i j)) =
          (1 + vM (rootPat p) s') * (1 + vM (rootPat p) (f y)) := by
        rw [← e1, e2, e3, e4]
        all_goals rfl
      have e6 := congrFun (congrFun e5 q.1.1) q.1.2
      rw [hone, lm_eq] at e6
      exact e6
    rw [Measure.map_congr hae, ← Measure.map_map (lm_mp p s').measurable hfc.measurable, hνf,
      Measure.map_smul, (lm_mp p s').map_eq]

end PI.AmpRootHaarW
