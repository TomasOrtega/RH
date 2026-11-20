import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SBSep

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨z₀, hz₀⟩` from `Function.ne_iff.1 hne`. Use `set D : K → ℂ := fun z => P z - Q z with hDdef`. Establish `hDc : Continuous D` using `hP.sub hQ`. Establish `hD0 : D z₀ ≠ 0` using `sub_ne_zero.2 hz₀`.

Establish `hn : 0 < ‖D z₀‖` using `norm_pos_iff.2 hD0`. Establish `hW : {x : K | ‖D (z₀ + x) - D z₀‖ < ‖D z₀‖ / 2} ∩ (valBall K 0 : Set K) ∈ 𝓝 (0 : K)`. Use `Filter.inter_mem ?_ (valBall_mem_nhds 0)` and prove the remaining obligations. Establish `hc : Continuous fun x : K => ‖D (z₀ + x) - D z₀‖` using `by fun_prop`. Use `(isOpen_lt hc continuous_const).mem_nhds ?_` and prove the remaining obligations.

Simplify using `using half_pos hn`. Take `⟨V, hV⟩` from `NonarchimedeanAddGroup.is_nonarchimedean _ hW`. Set `B : Set K` to `(fun z => z - z₀) ⁻¹' (V : Set K)`. Establish `hBo : IsOpen B` using `V.isOpen.preimage (by fun_prop)`. Establish `hBcl : IsClosed B` using `V.isClosed.preimage (by fun_prop)`.

Establish `hVc : IsCompact (V : Set K)` using `(isCompact_valBall 0).of_isClosed_subset V.isClosed (fun x hx => (hV hx).2)`. Establish `hBc : IsCompact B` using `(Homeomorph.subRight z₀).isCompact_preimage.2 hVc`. Establish `hB0 : z₀ ∈ B`. Express the relevant statement in the definitionally equal form `z₀ - z₀ ∈ (V : Set K)`. Rewrite using `[sub_self]`.

Conclude with `zero_mem V`. Establish `hBm : MeasurableSet B` using `hBo.measurableSet`. Establish `hμ : 0 < μ B` using `hBo.measure_pos μ ⟨z₀, hB0⟩`. Establish `hμt : μ B < ⊤` using `hBc.measure_lt_top`. Set `Φ : K → ℂ` to `B.indicator fun _ => 1`.

Establish `hΦ : Φ ∈ SBE K` using `⟨(LocallyConstant.indicator (LocallyConstant.const K (1 : ℂ)) ⟨hBcl, hBo⟩).isLocallyConstant, HasCompactSupport.intro hBc fun x hx => Set.indicator_of_notMem hx _⟩`. Establish `hI : ∀ R : K → ℂ, ∫ z, Φ z * R z ∂μ = ∫ z in B, R z ∂μ`. Introduce `R`. Rewrite using `[← integral_indicator hBm]`. Use `congr 1`.

Use extensionality with `z`. Apply the tactic sequence `by_cases hz : z ∈ B <;> simp [Φ, hz]`. Establish `hPB : IntegrableOn P B μ` using `hP.continuousOn.integrableOn_compact hBc`. Establish `hQB : IntegrableOn Q B μ` using `hQ.continuousOn.integrableOn_compact hBc`. Establish `hDB : IntegrableOn D B μ` using `hDc.continuousOn.integrableOn_compact hBc`.

Establish `h0 : ∫ z in B, D z ∂μ = 0`. Establish `h1` using `h Φ hΦ`. Rewrite `h1` using `[hI, hI]`. Rewrite using `[hDdef, integral_sub hPB hQB, h1, sub_self]`. Establish `hconst : ∫ z in B, (D z - D z₀) ∂μ = -(μ.real B • D z₀)`.

Rewrite using `[integral_sub hDB (integrableOn_const hμt.ne), h0, setIntegral_const, zero_sub]`. Establish `hle : ‖∫ z in B, (D z - D z₀) ∂μ‖ ≤ (‖D z₀‖ / 2) * μ.real B`. Use `norm_setIntegral_le_of_norm_le_const hμt fun z hz => ?_` and prove the remaining obligations. Establish `h2` using `(hV (show z - z₀ ∈ (V : Set K) from hz)).1`. Establish `h3 : ‖D (z₀ + (z - z₀)) - D z₀‖ < ‖D z₀‖ / 2` using `h2`.

Rewrite `h3` using `[add_sub_cancel]`. Conclude with `h3.le`. Establish `hpos : 0 < μ.real B` using `ENNReal.toReal_pos hμ.ne' hμt.ne`. Rewrite `hle` using `[hconst, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le]`. Use polynomial arithmetic with `[mul_pos hpos hn]`.
-/
theorem eq_of_integral_SBE_eq (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsAddHaarMeasure] (P Q : K → ℂ) (hP : Continuous P) (hQ : Continuous Q)
    (h : ∀ Φ ∈ SBE K, ∫ z, Φ z * P z ∂μ = ∫ z, Φ z * Q z ∂μ) : P = Q := by
  by_contra hne
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  set D : K → ℂ := fun z => P z - Q z with hDdef
  have hDc : Continuous D := hP.sub hQ
  have hD0 : D z₀ ≠ 0 := sub_ne_zero.2 hz₀
  have hn : 0 < ‖D z₀‖ := norm_pos_iff.2 hD0
  have hW : {x : K | ‖D (z₀ + x) - D z₀‖ < ‖D z₀‖ / 2} ∩ (valBall K 0 : Set K) ∈ 𝓝 (0 : K) := by
    refine Filter.inter_mem ?_ (valBall_mem_nhds 0)
    have hc : Continuous fun x : K => ‖D (z₀ + x) - D z₀‖ := by fun_prop
    refine (isOpen_lt hc continuous_const).mem_nhds ?_
    simpa using half_pos hn
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hW
  let B : Set K := (fun z => z - z₀) ⁻¹' (V : Set K)
  have hBo : IsOpen B := V.isOpen.preimage (by fun_prop)
  have hBcl : IsClosed B := V.isClosed.preimage (by fun_prop)
  have hVc : IsCompact (V : Set K) :=
    (isCompact_valBall 0).of_isClosed_subset V.isClosed (fun x hx => (hV hx).2)
  have hBc : IsCompact B := (Homeomorph.subRight z₀).isCompact_preimage.2 hVc
  have hB0 : z₀ ∈ B := by
    change z₀ - z₀ ∈ (V : Set K)
    rw [sub_self]
    exact zero_mem V
  have hBm : MeasurableSet B := hBo.measurableSet
  have hμ : 0 < μ B := hBo.measure_pos μ ⟨z₀, hB0⟩
  have hμt : μ B < ⊤ := hBc.measure_lt_top
  let Φ : K → ℂ := B.indicator fun _ => 1
  have hΦ : Φ ∈ SBE K :=
    ⟨(LocallyConstant.indicator (LocallyConstant.const K (1 : ℂ)) ⟨hBcl, hBo⟩).isLocallyConstant,
      HasCompactSupport.intro hBc fun x hx => Set.indicator_of_notMem hx _⟩
  have hI : ∀ R : K → ℂ, ∫ z, Φ z * R z ∂μ = ∫ z in B, R z ∂μ := by
    intro R
    rw [← integral_indicator hBm]
    congr 1
    ext z
    by_cases hz : z ∈ B <;> simp [Φ, hz]
  have hPB : IntegrableOn P B μ := hP.continuousOn.integrableOn_compact hBc
  have hQB : IntegrableOn Q B μ := hQ.continuousOn.integrableOn_compact hBc
  have hDB : IntegrableOn D B μ := hDc.continuousOn.integrableOn_compact hBc
  have h0 : ∫ z in B, D z ∂μ = 0 := by
    have h1 := h Φ hΦ
    rw [hI, hI] at h1
    rw [hDdef, integral_sub hPB hQB, h1, sub_self]
  have hconst : ∫ z in B, (D z - D z₀) ∂μ = -(μ.real B • D z₀) := by
    rw [integral_sub hDB (integrableOn_const hμt.ne), h0, setIntegral_const, zero_sub]
  have hle : ‖∫ z in B, (D z - D z₀) ∂μ‖ ≤ (‖D z₀‖ / 2) * μ.real B := by
    refine norm_setIntegral_le_of_norm_le_const hμt fun z hz => ?_
    have h2 := (hV (show z - z₀ ∈ (V : Set K) from hz)).1
    have h3 : ‖D (z₀ + (z - z₀)) - D z₀‖ < ‖D z₀‖ / 2 := h2
    rw [add_sub_cancel] at h3
    exact h3.le
  have hpos : 0 < μ.real B := ENNReal.toReal_pos hμ.ne' hμt.ne
  rw [hconst, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le] at hle
  nlinarith [mul_pos hpos hn]

end GlobalTheory.CompanionTheory.SBSep
