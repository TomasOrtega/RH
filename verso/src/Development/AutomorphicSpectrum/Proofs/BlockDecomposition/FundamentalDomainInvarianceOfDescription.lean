import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing ENNReal Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.RSGlobal

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Use `set Φ := glNormOneSplitting (K := K) hn with hΦ`. Set `ν : Measure (normOneGL K n)` to `Measure.haar`. Set `ρ : Measure {r : ℝ // 0 < r}` to `Measure.haar`. Use `haveI : ν.IsMulRightInvariant := isMulRightInvariant_normOneGL ν`. Set `m : Measure (normOneGL K n × {r : ℝ // 0 < r})` to `ν.prod ρ`.

Use `haveI : m.IsHaarMeasure := inferInstanceAs (ν.prod ρ).IsHaarMeasure`. Use `haveI : m.IsMulRightInvariant := inferInstanceAs (ν.prod ρ).IsMulRightInvariant`. Establish `hc : Measurable (Φ.symm : normOneGL K n × {r : ℝ // 0 < r} → AdelicGLn.AdelicGL K n)` using `Φ.symm.continuous.measurable`. Use `⟨m.map Φ.symm, ContinuousMulEquiv.isHaarMeasure_map m Φ.symm, ⟨fun g => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Measure.map_map (measurable_mul_const g) hc]`.

Establish `h : (· * g) ∘ (Φ.symm : normOneGL K n × {r : ℝ // 0 < r} → AdelicGLn.AdelicGL K n) = Φ.symm ∘ (· * Φ g)`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, map_mul, ContinuousMulEquiv.symm_apply_apply]`. Rewrite using `[h, ← Measure.map_map hc (measurable_mul_const (Φ g)), map_mul_right_eq_self]`.
-/
theorem exists_isHaarMeasure_isMulRightInvariant (hn : 0 < n) :
    ∃ μ : Measure (AdelicGLn.AdelicGL K n), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant := by
  set Φ := glNormOneSplitting (K := K) hn with hΦ
  let ν : Measure (normOneGL K n) := Measure.haar
  let ρ : Measure {r : ℝ // 0 < r} := Measure.haar
  haveI : ν.IsMulRightInvariant := isMulRightInvariant_normOneGL ν
  let m : Measure (normOneGL K n × {r : ℝ // 0 < r}) := ν.prod ρ
  haveI : m.IsHaarMeasure := inferInstanceAs (ν.prod ρ).IsHaarMeasure
  haveI : m.IsMulRightInvariant := inferInstanceAs (ν.prod ρ).IsMulRightInvariant
  have hc : Measurable (Φ.symm : normOneGL K n × {r : ℝ // 0 < r} → AdelicGLn.AdelicGL K n) :=
    Φ.symm.continuous.measurable
  refine ⟨m.map Φ.symm, ContinuousMulEquiv.isHaarMeasure_map m Φ.symm, ⟨fun g => ?_⟩⟩
  rw [Measure.map_map (measurable_mul_const g) hc]
  have h : (· * g) ∘ (Φ.symm : normOneGL K n × {r : ℝ // 0 < r} → AdelicGLn.AdelicGL K n) =
      Φ.symm ∘ (· * Φ g) := by
    funext p
    simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.symm_apply_apply]
  rw [h, ← Measure.map_map hc (measurable_mul_const (Φ g)), map_mul_right_eq_self]

/- English proof (translation)
Take `⟨ω, hω, hωB, t, ht, hsieg⟩` from `exists_siegelSet (K := K) n`. Use `choose c₁ c₂ hc₁ hbd using fun w => exists_norm_det_infAt_bounds (K := K) hω t w`. Use `set S : ∀ w : InfinitePlace K, Set (GL (Fin n) w.Completion) := fun w => localSiegel w (infAt w '' ω) t (c₁ w) (c₂ w) with hSdef`. Establish `hS : ∀ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w) < ⊤` using `fun w => measure_localSiegel_lt_top w _ (hω.image (continuous_infAt w)) (by rintro _ ⟨b, hb, rfl⟩; exact infAt_isUpperTriangular (hωB hb)) ht (hc₁ w)`. Use `set p2 : AdelicGLn.AdelicGL K n → AdelicGLn.FiniteAdelicGL K n := fun g => (AdelicGLn.prodEquiv K n g).2 with hp2`.

Establish `hp2c : Continuous p2` using `continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous`. Use `set F : Set (AdelicGLn.FiniteAdelicGL K n) := (p2 '' ω) * (p2 '' (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n))) with hFdef`. Establish `hF : IsCompact F` using `(hω.image hp2c).mul (isCompact_maxCompact.image hp2c)`. Use `set E : Set (AdelicGLn.AdelicGL K n) := {g | g ∈ siegelSet n ω t ∧ 1 ≤ (ideleModule K (AdelicGLn.det K n g) : ℝ) ∧ (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ Real.exp 1} with hEdef`. Establish `hE : μ E < ⊤`.

Use `measure_lt_top_of_forall_mem μ S hS hF fun g hg => ⟨fun w => ?_, ?_⟩` and prove the remaining obligations. Take `⟨hgs, h1, h2⟩` from `hg`. Establish `hb` using `hbd w g hgs h1 h2`. Take `⟨b, hbω, _, ⟨r, hr, hratio, rfl⟩, k, hk, rfl⟩` from `hgs`. Use `⟨hb.1, hb.2, infAt w b, ⟨b, hbω, rfl⟩, r, hr, hratio, infAt w k, hk.1 w, ?_⟩` and prove the remaining obligations.

Rewrite using `[infAt_mul, infAt_mul, infAt_diagUnits_posIdele w r hr]`. Take `⟨⟨b, hbω, _, ⟨r, hr, -, rfl⟩, k, hk, rfl⟩, -, -⟩` from `hg`. Use `⟨p2 b, ⟨b, hbω, rfl⟩, p2 k, ⟨k, hk, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [hp2, map_mul, Prod.snd_mul, prodEquiv_diagUnits_posIdele_snd r hr, mul_one]`. Use `⟨E, hE, fun g h1 h2 => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ⟩` from `hsieg g`. Establish `hmod : (ideleModule K (AdelicGLn.det K n (AdelicGLn.diagonal K n γ * g)) : ℝ) = (ideleModule K (AdelicGLn.det K n g) : ℝ)`. Establish `h0 : (ideleModule K (AdelicGLn.det K n (AdelicGLn.diagonal K n γ)) : ℝ) = 1` using `mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩)`. Rewrite using `[map_mul, map_mul, Positive.val_mul, h0, one_mul]`. Conclude with `⟨γ, hγ, hmod ▸ h1, hmod ▸ h2⟩`.
-/
theorem exists_measure_lt_top_slab (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ E : Set (AdelicGLn.AdelicGL K n), μ E < ⊤ ∧ ∀ g : AdelicGLn.AdelicGL K n,
      1 ≤ (ideleModule K (AdelicGLn.det K n g) : ℝ) → (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ Real.exp 1 →
        ∃ γ : GL (Fin n) K, AdelicGLn.diagonal K n γ * g ∈ E := by
  classical
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := K) n
  choose c₁ c₂ hc₁ hbd using fun w => exists_norm_det_infAt_bounds (K := K) hω t w
  set S : ∀ w : InfinitePlace K, Set (GL (Fin n) w.Completion) :=
    fun w => localSiegel w (infAt w '' ω) t (c₁ w) (c₂ w) with hSdef
  have hS : ∀ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w) < ⊤ := fun w =>
    measure_localSiegel_lt_top w _ (hω.image (continuous_infAt w))
      (by rintro _ ⟨b, hb, rfl⟩; exact infAt_isUpperTriangular (hωB hb)) ht (hc₁ w)
  set p2 : AdelicGLn.AdelicGL K n → AdelicGLn.FiniteAdelicGL K n :=
    fun g => (AdelicGLn.prodEquiv K n g).2 with hp2
  have hp2c : Continuous p2 := continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous
  set F : Set (AdelicGLn.FiniteAdelicGL K n) :=
    (p2 '' ω) * (p2 '' (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n))) with hFdef
  have hF : IsCompact F := (hω.image hp2c).mul (isCompact_maxCompact.image hp2c)
  set E : Set (AdelicGLn.AdelicGL K n) := {g | g ∈ siegelSet n ω t ∧
    1 ≤ (ideleModule K (AdelicGLn.det K n g) : ℝ) ∧
      (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ Real.exp 1} with hEdef
  have hE : μ E < ⊤ := by
    refine measure_lt_top_of_forall_mem μ S hS hF fun g hg => ⟨fun w => ?_, ?_⟩
    · obtain ⟨hgs, h1, h2⟩ := hg
      have hb := hbd w g hgs h1 h2
      obtain ⟨b, hbω, _, ⟨r, hr, hratio, rfl⟩, k, hk, rfl⟩ := hgs
      refine ⟨hb.1, hb.2, infAt w b, ⟨b, hbω, rfl⟩, r, hr, hratio, infAt w k, hk.1 w, ?_⟩
      rw [infAt_mul, infAt_mul, infAt_diagUnits_posIdele w r hr]
    · obtain ⟨⟨b, hbω, _, ⟨r, hr, -, rfl⟩, k, hk, rfl⟩, -, -⟩ := hg
      refine ⟨p2 b, ⟨b, hbω, rfl⟩, p2 k, ⟨k, hk, rfl⟩, ?_⟩
      simp only [hp2, map_mul, Prod.snd_mul, prodEquiv_diagUnits_posIdele_snd r hr, mul_one]
  refine ⟨E, hE, fun g h1 h2 => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg g
  have hmod : (ideleModule K (AdelicGLn.det K n (AdelicGLn.diagonal K n γ * g)) : ℝ) =
      (ideleModule K (AdelicGLn.det K n g) : ℝ) := by
    have h0 : (ideleModule K (AdelicGLn.det K n (AdelicGLn.diagonal K n γ)) : ℝ) = 1 :=
      mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩)
    rw [map_mul, map_mul, Positive.val_mul, h0, one_mul]
  exact ⟨γ, hγ, hmod ▸ h1, hmod ▸ h2⟩

instance countable_GL_rat : Countable (GL (Fin 2) ℚ) :=
  Function.Injective.countable
    (f := fun g : GL (Fin 2) ℚ => (fun i j => (g : Matrix (Fin 2) (Fin 2) ℚ) i j : Fin 2 → Fin 2 → ℚ))
    fun _ _ h => Units.ext (by ext i j; exact congrFun (congrFun h i) j)

/- English proof (translation)
Take `⟨E, hE, hcov⟩` from `exists_measure_lt_top_slab (K := ℚ) (n := 2) μ`. Use `haveI : Countable (AdelicGLn.diagonal ℚ 2).range := Function.Surjective.countable (AdelicGLn.diagonal ℚ 2).rangeRestrict_surjective`. Use `lt_of_le_of_lt ?_ hE` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `measure_mono fun x hx => ?_` and prove the remaining obligations.

Establish `h2 : (2 : ℝ) ≤ Real.exp 1`. Use `Real.exp_one_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨γ, hγ⟩` from `hcov x hx.2.1 (hx.2.2.le.trans h2)`. Use `mem_iUnion.2 ⟨⟨AdelicGLn.diagonal ℚ 2 γ, ⟨γ, rfl⟩⟩⁻¹, ?_, hx.1⟩` and prove the remaining obligations.

Rewrite using `[Set.mem_inv_smul_set_iff]`. Conclude with `hγ`. Use `_ ≤ ∑' γ : (AdelicGLn.diagonal ℚ 2).range, μ (γ • E ∩ 𝓕) := measure_iUnion_le _`. Use `_ = μ E := (hF.measure_eq_tsum E).symm`.
-/
theorem measure_inter_band_lt_top (μ : Measure Ad3.R.G2) [μ.IsHaarMeasure] {𝓕 : Set Ad3.R.G2}
    (hF : IsFundamentalDomain (AdelicGLn.diagonal ℚ 2).range 𝓕 μ) : μ (𝓕 ∩ Ad3.R.band) < ⊤ := by
  obtain ⟨E, hE, hcov⟩ := exists_measure_lt_top_slab (K := ℚ) (n := 2) μ
  haveI : Countable (AdelicGLn.diagonal ℚ 2).range :=
    Function.Surjective.countable (AdelicGLn.diagonal ℚ 2).rangeRestrict_surjective
  refine lt_of_le_of_lt ?_ hE
  calc μ (𝓕 ∩ Ad3.R.band) ≤ μ (⋃ γ : (AdelicGLn.diagonal ℚ 2).range, γ • E ∩ 𝓕) := by
        refine measure_mono fun x hx => ?_
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
        obtain ⟨γ, hγ⟩ := hcov x hx.2.1 (hx.2.2.le.trans h2)
        refine mem_iUnion.2 ⟨⟨AdelicGLn.diagonal ℚ 2 γ, ⟨γ, rfl⟩⟩⁻¹, ?_, hx.1⟩
        rw [Set.mem_inv_smul_set_iff]
        exact hγ
    _ ≤ ∑' γ : (AdelicGLn.diagonal ℚ 2).range, μ (γ • E ∩ 𝓕) := measure_iUnion_le _
    _ = μ E := (hF.measure_eq_tsum E).symm

/- English proof (translation)
Use `haveI : CompactSpace Ad3.R.KA := isCompact_iff_compactSpace.1 isCompact_maxCompact`. Set `K₀ : TopologicalSpace.PositiveCompacts Ad3.R.KA` to `⊤`. Use `⟨Measure.haarMeasure K₀, inferInstance, ⟨?_⟩⟩` and prove the remaining obligations. Establish `h` using `Measure.haarMeasure_self (K₀ := K₀)`. Simplify `h` using `[K₀]`.
-/
theorem exists_probability_haar :
    ∃ m : Measure Ad3.R.KA, m.IsHaarMeasure ∧ IsProbabilityMeasure m := by
  haveI : CompactSpace Ad3.R.KA := isCompact_iff_compactSpace.1 isCompact_maxCompact
  let K₀ : TopologicalSpace.PositiveCompacts Ad3.R.KA := ⊤
  refine ⟨Measure.haarMeasure K₀, inferInstance, ⟨?_⟩⟩
  have h := Measure.haarMeasure_self (K₀ := K₀)
  simpa [K₀] using h

/- English proof (translation)
Introduce and unpack `⟨𝓓, h1, h2, h3⟩`. Take `⟨μ, hμ, hr⟩` from `exists_isHaarMeasure_isMulRightInvariant (K := ℚ) (n := 2) (by norm_num)`. Take `⟨mK, hK, hP⟩` from `exists_probability_haar`. Use `haveI : DiscreteTopology (AdelicGLn.rationalGL ℚ 2) := AdelicGLn.discreteTopology_rationalGL ℚ 2`. Establish `hF : IsFundamentalDomain (AdelicGLn.diagonal ℚ 2).range (RightCosetSpace.fundamentalDomain (AdelicGLn.rationalGL ℚ 2)) μ` using `RightCosetSpace.isFundamentalDomain_fundamentalDomain (AdelicGLn.rationalGL ℚ 2) μ`.

Conclude with `⟨μ, _, mK, 𝓓, ⟨hμ, hr, hF, RightCosetSpace.measurableSet_fundamentalDomain _, measure_inter_band_lt_top μ hF, hK, hP, h1, h2, h3⟩⟩`.
-/
theorem setup_of_ideleDomain : Ad3.R.D0 → Ad3.R.G0 := by
  rintro ⟨𝓓, h1, h2, h3⟩
  obtain ⟨μ, hμ, hr⟩ := exists_isHaarMeasure_isMulRightInvariant (K := ℚ) (n := 2) (by norm_num)
  obtain ⟨mK, hK, hP⟩ := exists_probability_haar
  haveI : DiscreteTopology (AdelicGLn.rationalGL ℚ 2) := AdelicGLn.discreteTopology_rationalGL ℚ 2
  have hF : IsFundamentalDomain (AdelicGLn.diagonal ℚ 2).range
      (RightCosetSpace.fundamentalDomain (AdelicGLn.rationalGL ℚ 2)) μ :=
    RightCosetSpace.isFundamentalDomain_fundamentalDomain (AdelicGLn.rationalGL ℚ 2) μ
  exact ⟨μ, _, mK, 𝓓, ⟨hμ, hr, hF, RightCosetSpace.measurableSet_fundamentalDomain _,
    measure_inter_band_lt_top μ hF, hK, hP, h1, h2, h3⟩⟩

end GlobalTheory.CompanionTheory.RSGlobal

end
