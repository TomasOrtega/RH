import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal

namespace GlobalTheory.JR.WeilQuad.GaussTrans

/- English proof (translation)
Introduce `F E _ _ _ _ U A ψ x μ ω hH t s ⟨ℓ, hℓ⟩ G ⟨Λ₀, ho₀, hc₀, hG⟩`. Use `U.charZero` as an intermediate fact. Use `U.ultraF` as an intermediate fact. Use `U.lcF` as an intermediate fact. Establish `: ProperSpace F` using `.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F`.

Use `EtMeas.finite_L A` as an intermediate fact. Take `⟨⟨b⟩, hinj, hN, -, -⟩` from `GlobalTheory.JR.Et.quadratic_structure F E A`. Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A.K`. Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A.L`. Establish `: IsTopologicalRing A.L` using `IsModuleTopology.isTopologicalRing F A.L`.

Establish `: ContinuousStar A.L` using `⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩`. Establish `hμ : μ.IsAddHaarMeasure` using `hH.2.2.2.1.1`. Establish `hs' : algebraMap A.K A.L (s : A.K) = ℓ * star ℓ` using `by rw [← hℓ, hN]`. Establish `hu : IsUnit ℓ` using `isUnit_of_mul_isUnit_left (hs' ▸ (s.isUnit.map (algebraMap A.K A.L)))`. Use `set u : A.Lˣ := hu.unit with hu_def`.

Establish `hul : (u : A.L) = ℓ` using `hu.unit_spec`. Establish `hmod : distribHaarChar A.L u = distribHaarChar A.K s` using `GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F)) (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) u s (by rw [hul]; exact hs')`. Establish `hmap : μ.map (fun y => u • y) = (distribHaarChar A.L u⁻¹ : ℝ≥0∞) • μ`. Use extensionality with `S hS`. Rewrite using `[Measure.map_apply (measurable_const_smul u) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul, distribHaarChar_mul]`.

Establish `hemb : MeasurableEmbedding (fun y : A.L => u • y)` using `(Homeomorph.smul u).measurableEmbedding`. Establish `key : ∀ Λ : AddSubgroup A.L, gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ = ((A.absK s : ℂ))⁻¹ * gaussInt A ψ x μ t (u • Λ : AddSubgroup A.L)`. Introduce `Λ`. Establish `h1 : gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ = ∫ y in (Λ : Set A.L), A.psiK ψ ((t : A.K) * x * A.NL (u • y)) ∂μ`. Unfold `gaussInt`.

Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Establish `hNm : A.NL (u • y) = s * A.NL y`. Rewrite using `[Units.smul_def, hul, smul_eq_mul]`. Unfold `Et.NL`. Rewrite using `[map_mul]`.

Conclude with `congrArg (· * _) hℓ`. Simplify using `only`. Rewrite using `[hNm]`. Use `push_cast`. Put the polynomial expressions in normal form.

Establish `h2` using `hemb.setIntegral_map (μ := μ) (fun z => A.psiK ψ ((t : A.K) * x * A.NL z)) ((u • Λ : AddSubgroup A.L) : Set A.L)`. Establish `hpre : (fun y => u • y) ⁻¹' ((u • Λ : AddSubgroup A.L) : Set A.L) = Λ`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe]`. Conclude with `⟨fun h => by simpa using (AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.1 h), fun h => AddSubgroup.smul_mem_pointwise_smul _ _ _ h⟩`.

Rewrite `h2` using `[hpre, hmap, Measure.restrict_smul, integral_smul_measure]`. Rewrite using `[h1, ← h2]`. Unfold `gaussInt`. Rewrite using `[Complex.real_smul, EtMeas.absK_unit, ENNReal.coe_toReal, map_inv, hmod]`. Use `congr 1`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hcoe : ∀ (v : A.Lˣ) (M : AddSubgroup A.L), ((v • M : AddSubgroup A.L) : Set A.L) = v • (M : Set A.L)` using `fun v M => AddSubgroup.coe_pointwise_smul v M`. Use `⟨u⁻¹ • Λ₀, ?_, ?_, fun Λ hoΛ hcΛ hle => ?_⟩` and prove the remaining obligations. Rewrite using `[hcoe]`.

Conclude with `ho₀.smul _`. Rewrite using `[hcoe]`. Conclude with `hc₀.smul _`. Rewrite using `[key, hG (u • Λ) (by rw [hcoe]; exact hoΛ.smul _) (by rw [hcoe]; exact hcΛ.smul _) ?_, mul_comm]`. Introduce `z hz`.

Establish `: u⁻¹ • z ∈ Λ` using `hle (AddSubgroup.smul_mem_pointwise_smul _ _ _ hz)`. Conclude with `AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 this`.
-/
theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (t s : A.Kˣ), (∃ ℓ : A.L, A.NL ℓ = s) → ∀ G : ℂ, IsStableGauss A ψ x μ t G → IsStableGauss A ψ x μ ((t * s : A.Kˣ) : A.K) (G * ((A.absK s : ℂ))⁻¹) := by
  intro F E _ _ _ _ U A ψ x μ ω hH t s ⟨ℓ, hℓ⟩ G ⟨Λ₀, ho₀, hc₀, hG⟩
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := EtMeas.finite_L A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  have hμ : μ.IsAddHaarMeasure := hH.2.2.2.1.1
  have hs' : algebraMap A.K A.L (s : A.K) = ℓ * star ℓ := by rw [← hℓ, hN]
  have hu : IsUnit ℓ := isUnit_of_mul_isUnit_left (hs' ▸ (s.isUnit.map (algebraMap A.K A.L)))
  set u : A.Lˣ := hu.unit with hu_def
  have hul : (u : A.L) = ℓ := hu.unit_spec
  have hmod : distribHaarChar A.L u = distribHaarChar A.K s :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) u s
      (by rw [hul]; exact hs')
  have hmap : μ.map (fun y => u • y) = (distribHaarChar A.L u⁻¹ : ℝ≥0∞) • μ := by
    ext S hS
    rw [Measure.map_apply (measurable_const_smul u) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
      distribHaarChar_mul]
  have hemb : MeasurableEmbedding (fun y : A.L => u • y) :=
    (Homeomorph.smul u).measurableEmbedding
  have key : ∀ Λ : AddSubgroup A.L, gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
      ((A.absK s : ℂ))⁻¹ * gaussInt A ψ x μ t (u • Λ : AddSubgroup A.L) := by
    intro Λ
    have h1 : gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
        ∫ y in (Λ : Set A.L), A.psiK ψ ((t : A.K) * x * A.NL (u • y)) ∂μ := by
      unfold gaussInt
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have hNm : A.NL (u • y) = s * A.NL y := by
        rw [Units.smul_def, hul, smul_eq_mul]
        unfold Et.NL
        rw [map_mul]
        exact congrArg (· * _) hℓ
      simp only
      rw [hNm]
      push_cast; ring_nf
    have h2 := hemb.setIntegral_map (μ := μ) (fun z => A.psiK ψ ((t : A.K) * x * A.NL z)) ((u • Λ : AddSubgroup A.L) : Set A.L)
    have hpre : (fun y => u • y) ⁻¹' ((u • Λ : AddSubgroup A.L) : Set A.L) = Λ := by
      ext y
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun h => by simpa using (AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.1 h),
        fun h => AddSubgroup.smul_mem_pointwise_smul _ _ _ h⟩
    rw [hpre, hmap, Measure.restrict_smul, integral_smul_measure] at h2
    rw [h1, ← h2]
    unfold gaussInt
    rw [Complex.real_smul, EtMeas.absK_unit, ENNReal.coe_toReal, map_inv, hmod]
    congr 1
    push_cast
    rfl
  have hcoe : ∀ (v : A.Lˣ) (M : AddSubgroup A.L), ((v • M : AddSubgroup A.L) : Set A.L) = v • (M : Set A.L) :=
    fun v M => AddSubgroup.coe_pointwise_smul v M
  refine ⟨u⁻¹ • Λ₀, ?_, ?_, fun Λ hoΛ hcΛ hle => ?_⟩
  · rw [hcoe]; exact ho₀.smul _
  · rw [hcoe]; exact hc₀.smul _
  · rw [key, hG (u • Λ) (by rw [hcoe]; exact hoΛ.smul _) (by rw [hcoe]; exact hcΛ.smul _) ?_, mul_comm]
    intro z hz
    have : u⁻¹ • z ∈ Λ := hle (AddSubgroup.smul_mem_pointwise_smul _ _ _ hz)
    exact AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 this

end GlobalTheory.JR.WeilQuad.GaussTrans
