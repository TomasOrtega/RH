import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import GroundTheory.AutomorphicForms.ReductionMeasure

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.EulerBox

section Box

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Distinguish the cases in `hX : ∀ v, projV v (projFin X) ∈ A v`. Establish `hI : X ∈ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))` using `fun v hv => by`. Rewrite using `[← hS v hv]`. Conclude with `hX v`. Establish `hB : X ∈ {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v}` using `hX`.

Rewrite using `[pureL, Set.indicator_of_mem hI, Set.indicator_of_mem hB, Finset.prod_eq_one (fun v _ => Set.indicator_of_mem (hX v) _), mul_one]`. Establish `hB : X ∉ {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v}` using `hX`. Rewrite using `[Set.indicator_of_notMem hB]`. Take `⟨v, hv⟩` from `not_forall.1 hX`. Distinguish the cases in `hvS : v ∈ S`.

Distinguish the cases in `hI : X ∈ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))`. Rewrite using `[pureL, Set.indicator_of_mem hI, Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _), mul_zero]`. Rewrite using `[pureL, Set.indicator_of_notMem hI]`. Establish `hI : X ∉ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))` using `fun h => hv (by`. Rewrite using `[hS v hvS]`.

Conclude with `h v hvS)`. Rewrite using `[pureL, Set.indicator_of_notMem hI]`.
-/
theorem pureL_indicator_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hS : ∀ v, v ∉ S → A v = latV b v) (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b S φinf (fun v => (A v).indicator 1) X =
      {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v}.indicator
        (fun X => φinf (projInf X)) X := by
  by_cases hX : ∀ v, projV v (projFin X) ∈ A v
  · have hI : X ∈ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := fun v hv => by
      rw [← hS v hv]; exact hX v
    have hB : X ∈ {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := hX
    rw [pureL, Set.indicator_of_mem hI, Set.indicator_of_mem hB,
      Finset.prod_eq_one (fun v _ => Set.indicator_of_mem (hX v) _), mul_one]
  · have hB : X ∉ {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := hX
    rw [Set.indicator_of_notMem hB]
    obtain ⟨v, hv⟩ := not_forall.1 hX
    by_cases hvS : v ∈ S
    · by_cases hI : X ∈ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))
      · rw [pureL, Set.indicator_of_mem hI,
          Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _), mul_zero]
      · rw [pureL, Set.indicator_of_notMem hI]
    · have hI : X ∉ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := fun h => hv (by
        rw [hS v hvS]; exact h v hvS)
      rw [pureL, Set.indicator_of_notMem hI]

/- English proof (translation)
Use extensionality with `X`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun v hv => by rw [← hS v hv]; exact h v, fun v _ => h v⟩`.

Introduce and unpack `⟨h1, h2⟩ v`. Distinguish the cases in `hv : v ∈ S`. Conclude with `h2 v hv`. Rewrite using `[hS v hv]`. Conclude with `h1 v hv`.
-/
theorem box_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hS : ∀ v, v ∉ S → A v = latV b v) :
    {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} =
      intOff b S ∩ ⋂ v ∈ S, (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) ⁻¹' A v := by
  ext X
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro h
    exact ⟨fun v hv => by rw [← hS v hv]; exact h v, fun v _ => h v⟩
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ S
    · exact h2 v hv
    · rw [hS v hv]; exact h1 v hv

end Box

/- English proof (translation)
Establish `: LocallyCompactSpace (AF F)` using `GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Take `⟨-, -, -, -, -, -, -, hB, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)`. Establish `: BorelSpace (Fin n → Fin M → AF F ⊗[F] E)` using `hB n M`. Take `⟨-, hFin, hV, -, hOff, -⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M`. Establish `hmeas : ∀ v, Measurable (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X))` using `fun v => by`.

Establish `hc : Continuous (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X))` using `(hV v).comp hFin`. Use `measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_` and prove the remaining obligations. Establish `: BorelSpace (Fv F v ⊗[F] E)` using `⟨rfl⟩`. Conclude with `(((continuous_apply i).comp (continuous_apply a)).comp hc).measurable`. Rewrite using `[box_eq b S A hS]`.

Conclude with `(hOff S).measurableSet.inter (Finset.measurableSet_biInter S fun v _ => hmeas v (hA v))`.
-/
theorem measurableSet_box (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := by
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨-, -, -, -, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  have : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := hB n M
  obtain ⟨-, hFin, hV, -, hOff, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M
  have hmeas : ∀ v, Measurable
      (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) := fun v => by
    have hc : Continuous (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) :=
      (hV v).comp hFin
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
    have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
    exact (((continuous_apply i).comp (continuous_apply a)).comp hc).measurable
  rw [box_eq b S A hS]
  exact (hOff S).measurableSet.inter
    (Finset.measurableSet_biInter S fun v _ => hmeas v (hA v))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ d b n M I c minf m hE φinf A hφ hA hfin hcof`. Take `⟨-, hsum, S₀, hS₀⟩` from `hE`. Establish `hfinite : {v | ¬ A v = latV b v}.Finite` using `Filter.eventually_cofinite.1 hcof`. Use `set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ hfinite.toFinset with hSdef`. Establish `hS : ∀ v, v ∉ S → A v = latV b v` using `fun v hv => by`.

Assume the negation of the conclusion as `hne`. Conclude with `hv (Finset.mem_union_right _ (hfinite.mem_toFinset.2 hne))`. Establish `hsumA : Summable (fun v => |(m v (A v)).toReal - 1|)` using `hsum.congr_cofinite (hcof.mono fun v hv => by simp only [hv])`. Take `⟨hmul, hsplit, -, hnn⟩` from `GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ _ hsumA`. Use `⟨hmul, ?_⟩` and prove the remaining obligations.

Establish `hbox` using `measurableSet_box F E σ hσ b n M S A hA hS`. Establish `hform` using `hS₀ S Finset.subset_union_left φinf (fun v => (A v).indicator 1) hφ (fun v => measurable_one.indicator (hA v))`. Establish `hlhs : ∫⁻ X, pureL b S φinf (fun v => (A v).indicator 1) X ∂I = ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I`. Repeatedly rewrite using `[pureL_indicator_eq b S φinf A hS]`. Conclude with `lintegral_indicator hbox _`.

Establish `hloc : ∀ v, ∫⁻ X, (A v).indicator 1 X ∂(m v) = ENNReal.ofReal (m v (A v)).toReal` using `fun v => by`. Rewrite using `[lintegral_indicator_one (hA v), ENNReal.ofReal_toReal (hfin v).ne]`. Establish `htail : ∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal = ∏' v : {v // v ∉ S}, (m v.1 (A v.1)).toReal` using `tprod_congr fun v => by rw [hS v.1 v.2]`. Rewrite `hform` using `[hlhs]`. Rewrite using `[hform, htail, (hsplit S).2]`.

Repeatedly rewrite using `[hloc]`. Rewrite using `[ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => ENNReal.toReal_nonneg), ENNReal.ofReal_prod_of_nonneg fun v _ => ENNReal.toReal_nonneg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem euler_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I c minf m → ∀ (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable φinf → (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) < ⊤) → (∀ᶠ v in Filter.cofinite, A v = latV b v) → Multipliable (fun v => (m v (A v)).toReal) ∧ ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I = (c : ℝ≥0∞) * (∫⁻ X, φinf X ∂minf) * ENNReal.ofReal (∏' v, (m v (A v)).toReal) := by
  intro F E _ _ _ _ _ σ hσ d b n M I c minf m hE φinf A hφ hA hfin hcof
  classical
  obtain ⟨-, hsum, S₀, hS₀⟩ := hE
  have hfinite : {v | ¬ A v = latV b v}.Finite := Filter.eventually_cofinite.1 hcof
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ hfinite.toFinset with hSdef
  have hS : ∀ v, v ∉ S → A v = latV b v := fun v hv => by
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfinite.mem_toFinset.2 hne))
  have hsumA : Summable (fun v => |(m v (A v)).toReal - 1|) :=
    hsum.congr_cofinite (hcof.mono fun v hv => by simp only [hv])
  obtain ⟨hmul, hsplit, -, hnn⟩ := GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ _ hsumA
  refine ⟨hmul, ?_⟩
  have hbox := measurableSet_box F E σ hσ b n M S A hA hS
  have hform := hS₀ S Finset.subset_union_left φinf (fun v => (A v).indicator 1) hφ
    (fun v => measurable_one.indicator (hA v))
  have hlhs : ∫⁻ X, pureL b S φinf (fun v => (A v).indicator 1) X ∂I =
      ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I := by
    simp_rw [pureL_indicator_eq b S φinf A hS]
    exact lintegral_indicator hbox _
  have hloc : ∀ v, ∫⁻ X, (A v).indicator 1 X ∂(m v) = ENNReal.ofReal (m v (A v)).toReal := fun v => by
    rw [lintegral_indicator_one (hA v), ENNReal.ofReal_toReal (hfin v).ne]
  have htail : ∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal =
      ∏' v : {v // v ∉ S}, (m v.1 (A v.1)).toReal :=
    tprod_congr fun v => by rw [hS v.1 v.2]
  rw [hlhs] at hform
  rw [hform, htail, (hsplit S).2]
  simp_rw [hloc]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_prod_of_nonneg fun v _ => ENNReal.toReal_nonneg]
  ring

end GlobalTheory.CompanionTheory.SW.EulerBox
