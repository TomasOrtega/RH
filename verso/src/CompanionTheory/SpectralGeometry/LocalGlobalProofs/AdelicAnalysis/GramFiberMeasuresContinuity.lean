import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresIntegralFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianLocalContinuousCongruenceSectionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LocFin

/- English proof (translation)
Establish `key` using `h.2.1 (W.indicator 1) (measurable_one.indicator hW)`. Simplify using `only [lintegral_indicator_one hW, h0, lintegral_zero] at key`. Rewrite `key` using `[Measure.restrict_apply hW]`. Then use the resulting hypothesis.
-/
theorem null_of_fibres_null {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) {W : Set V} (hW : MeasurableSet W)
    (h0 : ∀ b, fib b W = 0) : μ (W ∩ U) = 0 := by
  have key := h.2.1 (W.indicator 1) (measurable_one.indicator hW)
  simp only [lintegral_indicator_one hW, h0, lintegral_zero] at key
  rwa [Measure.restrict_apply hW] at key

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm S`. Use `haveI : IsTopologicalRing R := hR.1`. Use `haveI : LocallyCompactSpace R := hR.2.1`. Use `haveI : SecondCountableTopology R := hR.2.2.1`. Use `haveI : T2Space R := hR.2.2.2.1`.

Take `⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R`. Use `haveI := tK1`. Use `haveI := tK2`. Use `haveI := tK3`. Use `haveI := tK4`.

Use `haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := tK8 n M`. Take `⟨h1, h2, h3, h4, h5⟩` from `HermTop.herm_top F E σ hσ R n`. Use `haveI := h1`. Use `haveI := h2`. Use `haveI := h3`.

Use `haveI := h4`. Take `⟨g, hgc, hg⟩` from `h5 M J hJ`. Establish `hKU` using `GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR`. Establish `hBo : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}`. Establish `hdet : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det` using `continuous_subtype_val.matrix_det`.

Conclude with `hKU.isOpen_range.preimage hdet`. Establish `hUeq : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}`. Use extensionality with `X`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, hg]`. Establish `hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}) ν {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m`.

Rewrite using `[← hUeq]`. Conclude with `hm`. Take `⟨hloc, -, -, -⟩` from `FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val Subtype.val_injective hgc hg _ hBo m hfib`. Use `⟨hloc S, ?_⟩` and prove the remaining obligations. Introduce and unpack `U hU ⟨X₀, hX₀U, hX₀S, hX₀⟩ h0`.

Take `⟨κ, -, -, -, hκ⟩` from `GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hσ M J hJ R hR n μ ν m hμ hν hm`. Establish `hSdet : IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det`. Rewrite using `[← hX₀S]`. Conclude with `hX₀`. Take `⟨B₁, gs, hB₁, hSB₁, hgs, hgs1, hgsS⟩` from `GlobalTheory.T.hermitian_local_continuous_congruence_section F E σ hσ R hR n S hSdet`.

Take `⟨a1, a2, a3, -, -⟩` from `GramAlg.gram_algebra F E σ hσ M J hJ R n`. Establish `hgX₀ : g X₀ = S` using `Subtype.ext ((hg X₀).symm.trans hX₀S)`. Establish `hr : Continuous fun p : (Fin n → Fin M → R ⊗[F] E) × Matrix (Fin n) (Fin n) (R ⊗[F] E) => rmul R p.1 p.2`. Unfold `rmul`. Use `continuous_pi fun a => continuous_pi fun i => continuous_finset_sum _ fun c _ => ?_` and prove the remaining obligations.

Conclude with `((continuous_apply_apply c i).comp continuous_fst).mul (continuous_snd.matrix_elem c a)`. Set `T : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E)` to `fun X => rmul R X (((gs (g X))⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))`. Establish `hTc : ContinuousOn T (g ⁻¹' B₁)`. Use `hr.comp_continuousOn (ContinuousOn.prodMk continuousOn_id ?_)` and prove the remaining obligations. Conclude with `Units.continuous_val.comp_continuousOn ((hgs.comp hgc.continuousOn fun X hX => hX).inv)`.

Establish `hU'o : IsOpen (g ⁻¹' B₁ ∩ T ⁻¹' U)` using `hTc.isOpen_inter_preimage (hB₁.preimage hgc) hU`. Establish `hnull : ∀ S' : HermR R σ n, m S' (g ⁻¹' B₁ ∩ T ⁻¹' U) = 0`. Introduce `S'`. Distinguish the cases in `hS' : S' ∈ B₁`. Establish `e` using `hκ (gs S') S S' (hgsS S' hS')`.

Establish `hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))` using `(hr.comp (Continuous.prodMk continuous_id continuous_const)).measurable`. Rewrite using `[e, Measure.smul_apply, Measure.map_apply hmeas hU'o.measurableSet]`. Establish `hsub : (fun X : Fin n → Fin M → R ⊗[F] E => rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ⁻¹' (g ⁻¹' B₁ ∩ T ⁻¹' U) ⊆ U ∪ (gramR R σ J ⁻¹' {Subtype.val S} ∩ {X | IsUnit (gramR R σ J X).det})ᶜ`. Introduce `X hX`. Distinguish the cases in `hXf : X ∈ gramR R σ J ⁻¹' {Subtype.val S} ∩ {X | IsUnit (gramR R σ J X).det}`.

Use `left`. Establish `hXS : gramR R σ J X = S` using `hXf.1`. Establish `hgr : g (rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) = S'`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hg, a1, hXS, ← hgsS S' hS']`.

Establish `hT : T (rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) = X`. Simplify using `only [T]`. Rewrite using `[hgr, a2, Units.mul_inv, a3]`. Use `hX.2` as an intermediate fact. Simplify using `only [Set.mem_preimage] at this`.

Rewrite `this` using `[hT]`. Then use the resulting hypothesis. Conclude with `Or.inr hXf`. Establish `hz : m S ((fun X : Fin n → Fin M → R ⊗[F] E => rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ⁻¹' (g ⁻¹' B₁ ∩ T ⁻¹' U)) = 0` using `measure_mono_null hsub (measure_union_null h0 (hm.1 S))`. Rewrite using `[hz, smul_zero]`. Use `measure_mono_null ?_ (hm.1 S')` and prove the remaining obligations.

Introduce `X hX hXf`. Establish `hgX : g X = S'` using `Subtype.ext ((hg X).symm.trans hXf.1)`. Conclude with `hS' (hgX ▸ hX.1)`. Establish `hμ0` using `null_of_fibres_null hm hU'o.measurableSet hnull`. Establish `hO : IsOpen ((g ⁻¹' B₁ ∩ T ⁻¹' U) ∩ {X | IsUnit (gramR R σ J X).det})`.

Rewrite using `[hUeq]`. Conclude with `hU'o.inter (hBo.preimage hgc)`. Use `hO.measure_ne_zero μ ⟨X₀, ⟨?_, ?_⟩, hX₀⟩ hμ0` and prove the remaining obligations. Use `show g X₀ ∈ B₁`. Rewrite using `[hgX₀]`.

Conclude with `hSB₁`. Use `show T X₀ ∈ U`. Simplify using `only [T]`. Rewrite using `[hgX₀, hgs1, inv_one, Units.val_one, a3]`. Conclude with `hX₀U`.
-/
theorem fibre_loc_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ S : HermR R σ n, IsLocallyFiniteMeasure (m S) ∧ ∀ U : Set (Fin n → Fin M → R ⊗[F] E), IsOpen U → (∃ X ∈ U, gramR R σ J X = S ∧ IsUnit (gramR R σ J X).det) → m S U ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm S
  haveI : IsTopologicalRing R := hR.1
  haveI : LocallyCompactSpace R := hR.2.1
  haveI : SecondCountableTopology R := hR.2.2.1
  haveI : T2Space R := hR.2.2.2.1
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := tK8 n M
  obtain ⟨h1, h2, h3, h4, h5⟩ := HermTop.herm_top F E σ hσ R n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g, hgc, hg⟩ := h5 M J hJ
  have hKU := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  have hBo : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hdet : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      continuous_subtype_val.matrix_det
    exact hKU.isOpen_range.preimage hdet
  have hUeq : {X | IsUnit (gramR R σ J X).det} =
      g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hg]
  have hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val
      (g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}) ν
      {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m := by
    rw [← hUeq]
    exact hm
  obtain ⟨hloc, -, -, -⟩ := FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hgc hg _ hBo m hfib
  refine ⟨hloc S, ?_⟩
  rintro U hU ⟨X₀, hX₀U, hX₀S, hX₀⟩ h0
  obtain ⟨κ, -, -, -, hκ⟩ := GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hσ M J hJ R hR n μ ν m hμ hν hm
  have hSdet : IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
    rw [← hX₀S]
    exact hX₀
  obtain ⟨B₁, gs, hB₁, hSB₁, hgs, hgs1, hgsS⟩ := GlobalTheory.T.hermitian_local_continuous_congruence_section F E σ hσ R hR n S hSdet
  obtain ⟨a1, a2, a3, -, -⟩ := GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hgX₀ : g X₀ = S := Subtype.ext ((hg X₀).symm.trans hX₀S)
  have hr : Continuous fun p : (Fin n → Fin M → R ⊗[F] E) × Matrix (Fin n) (Fin n) (R ⊗[F] E) =>
      rmul R p.1 p.2 := by
    unfold rmul
    refine continuous_pi fun a => continuous_pi fun i => continuous_finset_sum _ fun c _ => ?_
    exact ((continuous_apply_apply c i).comp continuous_fst).mul (continuous_snd.matrix_elem c a)
  let T : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) := fun X =>
    rmul R X (((gs (g X))⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
  have hTc : ContinuousOn T (g ⁻¹' B₁) := by
    refine hr.comp_continuousOn (ContinuousOn.prodMk continuousOn_id ?_)
    exact Units.continuous_val.comp_continuousOn
      ((hgs.comp hgc.continuousOn fun X hX => hX).inv)
  have hU'o : IsOpen (g ⁻¹' B₁ ∩ T ⁻¹' U) := hTc.isOpen_inter_preimage (hB₁.preimage hgc) hU
  have hnull : ∀ S' : HermR R σ n, m S' (g ⁻¹' B₁ ∩ T ⁻¹' U) = 0 := by
    intro S'
    by_cases hS' : S' ∈ B₁
    · have e := hκ (gs S') S S' (hgsS S' hS')
      have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
        (hr.comp (Continuous.prodMk continuous_id continuous_const)).measurable
      rw [e, Measure.smul_apply, Measure.map_apply hmeas hU'o.measurableSet]
      have hsub : (fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ⁻¹'
            (g ⁻¹' B₁ ∩ T ⁻¹' U) ⊆
          U ∪ (gramR R σ J ⁻¹' {Subtype.val S} ∩ {X | IsUnit (gramR R σ J X).det})ᶜ := by
        intro X hX
        by_cases hXf : X ∈ gramR R σ J ⁻¹' {Subtype.val S} ∩ {X | IsUnit (gramR R σ J X).det}
        · left
          have hXS : gramR R σ J X = S := hXf.1
          have hgr : g (rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) :
              Matrix (Fin n) (Fin n) (R ⊗[F] E))) = S' := by
            apply Subtype.ext
            rw [← hg, a1, hXS, ← hgsS S' hS']
          have hT : T (rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) :
              Matrix (Fin n) (Fin n) (R ⊗[F] E))) = X := by
            simp only [T]
            rw [hgr, a2, Units.mul_inv, a3]
          have := hX.2
          simp only [Set.mem_preimage] at this
          rwa [hT] at this
        · exact Or.inr hXf
      have hz : m S ((fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ⁻¹'
            (g ⁻¹' B₁ ∩ T ⁻¹' U)) = 0 :=
        measure_mono_null hsub (measure_union_null h0 (hm.1 S))
      rw [hz, smul_zero]
    · refine measure_mono_null ?_ (hm.1 S')
      intro X hX hXf
      have hgX : g X = S' := Subtype.ext ((hg X).symm.trans hXf.1)
      exact hS' (hgX ▸ hX.1)
  have hμ0 := null_of_fibres_null hm hU'o.measurableSet hnull
  have hO : IsOpen ((g ⁻¹' B₁ ∩ T ⁻¹' U) ∩ {X | IsUnit (gramR R σ J X).det}) := by
    rw [hUeq]
    exact hU'o.inter (hBo.preimage hgc)
  refine hO.measure_ne_zero μ ⟨X₀, ⟨?_, ?_⟩, hX₀⟩ hμ0
  · show g X₀ ∈ B₁
    rw [hgX₀]
    exact hSB₁
  · show T X₀ ∈ U
    simp only [T]
    rw [hgX₀, hgs1, inv_one, Units.val_one, a3]
    exact hX₀U

end GlobalTheory.CompanionTheory.SW.LocFin
