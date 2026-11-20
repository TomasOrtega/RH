import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMapIntegrableDistributionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceNondegenerateCoordinateChangeStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.SubspaceInt

/- English proof (translation)
Introduce `F E _ _ _ _ _ n κ κa κb _ _ _ ε C hC μ₁ hμ₁ μ hμ`. Take `⟨D, h, hD, hPD⟩` from `GlobalTheory.T.trace_nondegenerate_coordinate_change F E n κ κa κb ε C hC`. Use `letI mY : MeasurableSpace (Fin n → AE F E) := borel _`. Use `haveI : BorelSpace (Fin n → AE F E) := ⟨rfl⟩`. Use `letI mI : MeasurableSpace ((Fin n × Fin (Module.finrank F E)) → AF F) := borel _`.

Use `haveI : BorelSpace ((Fin n × Fin (Module.finrank F E)) → AF F) := ⟨rfl⟩`. Use `letI mU : MeasurableSpace (κb → AF F) := borel _`. Use `haveI : BorelSpace (κb → AF F) := ⟨rfl⟩`. Use `letI mS : MeasurableSpace ((Fin n × Fin (Module.finrank F E)) ⊕ κb → AF F) := borel _`. Use `haveI : BorelSpace ((Fin n × Fin (Module.finrank F E)) ⊕ κb → AF F) := ⟨rfl⟩`.

Use `haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI : IsModuleTopology (AF F) (AE F E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop`. Use `haveI : IsTopologicalAddGroup (AE F E) := IsModuleTopology.topologicalAddGroup (AF F) (AE F E)`. Use `haveI : μ.IsAddHaarMeasure := hμ`. Use `haveI : μ₁.IsAddHaarMeasure := hμ₁`.

Use `haveI : (μ.map h).IsAddHaarMeasure := h.isAddHaarMeasure_map μ`. Apply the tactic sequence `let e : (((Fin n × Fin (Module.finrank F E)) → AF F) × (κb → AF F)) ≃ₜ+ ((Fin n × Fin (Module.finrank F E)) ⊕ κb → AF F) := { toFun := fun p => Sum.elim p.1 p.2 invFun := fun z => (fun i => z (Sum.inl i), fun b => z (Sum.inr b)) left_inv := fun p => rfl right_inv := fun z => by f …`. Consider the cases of `i`. Conclude with `(continuous_apply _).comp continuous_fst`. Conclude with `(continuous_apply _).comp continuous_snd`.

Use `continuous_invFun := (continuous_pi fun i => continuous_apply _).prodMk (continuous_pi fun i => continuous_apply _) }`. Use `haveI : (((μ.map h).prod μ₁).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _`. Take `⟨hint, hT⟩` from `GlobalTheory.T.siegel_map_integrable_distribution F ((Fin n × Fin (Module.finrank F E)) ⊕ κb) κ D hD (((μ.map h).prod μ₁).map e) inferInstance`. Establish `hkey : ∀ Ψ : (κ → AF F) → ℂ, ∀ y, GlobalTheory.DiagSiegel.diagInt μ₁ (fun v => Ψ (GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F` using `F) (AF F) (C k j) * y j)) v)) = ∫ u, Ψ ((D.map (algebraMap F (AF F))) *ᵥ e (h y, u)) ∂μ₁ := fun Ψ y => by`. Simplify using `only [GlobalTheory.DiagSiegel.diagInt, hPD]`.

Both sides reduce to the same expression. Establish `me : MeasurableEmbedding e` using `e.toHomeomorph.measurableEmbedding`. Establish `mh : MeasurableEmbedding h` using `h.toHomeomorph.measurableEmbedding`. Establish `hint2 : ∀ Ψ ∈ schA F κ, Integrable (fun p => Ψ ((D.map (algebraMap F (AF F))) *ᵥ e p)) ((μ.map h).prod μ₁)` using `fun Ψ hΨ => (me.integrable_map_iff).1 (hint Ψ hΨ)`. Establish `hI : ∀ Ψ ∈ schA F κ, Integrable (fun y => ∫ u, Ψ ((D.map (algebraMap F (AF F))) *ᵥ e (h y, u)) ∂μ₁) μ` using `fun Ψ hΨ => (mh.integrable_map_iff).1 (hint2 Ψ hΨ).integral_prod_left`.

Establish `hE : ∀ Ψ ∈ schA F κ, ∫ y, (∫ u, Ψ ((D.map (algebraMap F (AF F))) *ᵥ e (h y, u)) ∂μ₁) ∂μ = ∫ z, Ψ ((D.map (algebraMap F (AF F))) *ᵥ z) ∂(((μ.map h).prod μ₁).map e)` using `fun Ψ hΨ => by`. Rewrite using `[me.integral_map, integral_prod _ (hint2 Ψ hΨ)]`. Conclude with `(mh.integral_map (fun x => ∫ u, Ψ ((D.map (algebraMap F (AF F))) *ᵥ e (x, u)) ∂μ₁)).symm`. Use `⟨fun Ψ hΨ => by simpa only [hkey] using hI Ψ hΨ, ?_⟩` and prove the remaining obligations. Set `I0 : schA F κ →ₗ[ℂ] ℂ` to `{ toFun := fun Ψ => ∫ z, (Ψ : (κ → AF F) → ℂ) ((D.map (algebraMap F (AF F))) *ᵥ z) ∂(((μ.map h).prod μ₁).map e) map_add' := fun Ψ Ψ' => integral_add (hint _ Ψ.2) (hint _ Ψ'.2) map_smul' := fun c Ψ => integral_smul c _ }`.

Take `⟨Λ, hΛ⟩` from `LinearMap.exists_extend I0`. Establish `hΛa : ∀ Ψ ∈ schA F κ, Λ Ψ = ∫ z, Ψ ((D.map (algebraMap F (AF F))) *ᵥ z) ∂(((μ.map h).prod μ₁).map e)` using `fun Ψ hΨ => LinearMap.congr_fun hΛ ⟨Ψ, hΨ⟩`. Use `⟨Λ, fun g hg => ?_, fun Ψ hΨ => ?_⟩` and prove the remaining obligations. Take `⟨T, hT'⟩` from `hT g hg`. Use `⟨T, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[hΛa _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)]`. Conclude with `hT' f`. Rewrite using `[hΛa Ψ hΨ, ← hE Ψ hΨ]`. Simplify using `only [hkey]`.
-/
theorem integrable_and_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (κ κa κb : Type) [Fintype κ] [Fintype κa] [Fintype κb] (ε : κ ≃ κa ⊕ (κb ⊕ κb)) (C : Matrix κa (Fin n) E),
    (∀ z : Fin n → E, (∀ k, ∑ j, Algebra.trace F E (C k j * z j) = 0) → z = 0) →
    ∀ μ₁ : @Measure (κb → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ₁ →
    ∀ μ : @Measure (Fin n → AE F E) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
      (∀ Ψ ∈ schA F κ, (letI : MeasurableSpace (Fin n → AE F E) := borel _;
        Integrable (fun y => GlobalTheory.DiagSiegel.diagInt μ₁ (fun v => Ψ (GlobalTheory.ThK.Adapt.glue ε
          (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) v))) μ)) ∧
      ∃ Λ ∈ (adeleClass F).adm κ, ∀ Ψ ∈ schA F κ, Λ Ψ = (letI : MeasurableSpace (Fin n → AE F E) := borel _;
        ∫ y, GlobalTheory.DiagSiegel.diagInt μ₁ (fun v => Ψ (GlobalTheory.ThK.Adapt.glue ε
          (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) v)) ∂μ) := by
  intro F E _ _ _ _ _ n κ κa κb _ _ _ ε C hC μ₁ hμ₁ μ hμ
  obtain ⟨D, h, hD, hPD⟩ := GlobalTheory.T.trace_nondegenerate_coordinate_change F E n κ κa κb ε C hC
  letI mY : MeasurableSpace (Fin n → AE F E) := borel _
  haveI : BorelSpace (Fin n → AE F E) := ⟨rfl⟩
  letI mI : MeasurableSpace ((Fin n × Fin (Module.finrank F E)) → AF F) := borel _
  haveI : BorelSpace ((Fin n × Fin (Module.finrank F E)) → AF F) := ⟨rfl⟩
  letI mU : MeasurableSpace (κb → AF F) := borel _
  haveI : BorelSpace (κb → AF F) := ⟨rfl⟩
  letI mS : MeasurableSpace ((Fin n × Fin (Module.finrank F E)) ⊕ κb → AF F) := borel _
  haveI : BorelSpace ((Fin n × Fin (Module.finrank F E)) ⊕ κb → AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : IsModuleTopology (AF F) (AE F E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI : IsTopologicalAddGroup (AE F E) := IsModuleTopology.topologicalAddGroup (AF F) (AE F E)
  haveI : μ.IsAddHaarMeasure := hμ
  haveI : μ₁.IsAddHaarMeasure := hμ₁
  haveI : (μ.map h).IsAddHaarMeasure := h.isAddHaarMeasure_map μ
  let e : (((Fin n × Fin (Module.finrank F E)) → AF F) × (κb → AF F)) ≃ₜ+ ((Fin n × Fin (Module.finrank F E)) ⊕ κb → AF F) :=
    { toFun := fun p => Sum.elim p.1 p.2
      invFun := fun z => (fun i => z (Sum.inl i), fun b => z (Sum.inr b))
      left_inv := fun p => rfl
      right_inv := fun z => by funext i; cases i <;> rfl
      map_add' := fun p q => by funext i; cases i <;> rfl
      continuous_toFun := continuous_pi fun i => by
        cases i
        · exact (continuous_apply _).comp continuous_fst
        · exact (continuous_apply _).comp continuous_snd
      continuous_invFun := (continuous_pi fun i => continuous_apply _).prodMk (continuous_pi fun i => continuous_apply _) }
  haveI : (((μ.map h).prod μ₁).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  obtain ⟨hint, hT⟩ := GlobalTheory.T.siegel_map_integrable_distribution F ((Fin n × Fin (Module.finrank F E)) ⊕ κb) κ D hD (((μ.map h).prod μ₁).map e) inferInstance
  have hkey : ∀ Ψ : (κ → AF F) → ℂ, ∀ y, GlobalTheory.DiagSiegel.diagInt μ₁ (fun v => Ψ (GlobalTheory.ThK.Adapt.glue ε
      (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) v)) =
      ∫ u, Ψ ((D.map (algebraMap F (AF F))) *ᵥ e (h y, u)) ∂μ₁ := fun Ψ y => by
    simp only [GlobalTheory.DiagSiegel.diagInt, hPD]
    rfl
  have me : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have mh : MeasurableEmbedding h := h.toHomeomorph.measurableEmbedding
  have hint2 : ∀ Ψ ∈ schA F κ, Integrable (fun p => Ψ ((D.map (algebraMap F (AF F))) *ᵥ e p)) ((μ.map h).prod μ₁) := fun Ψ hΨ =>
    (me.integrable_map_iff).1 (hint Ψ hΨ)
  have hI : ∀ Ψ ∈ schA F κ, Integrable (fun y => ∫ u, Ψ ((D.map (algebraMap F (AF F))) *ᵥ e (h y, u)) ∂μ₁) μ := fun Ψ hΨ =>
    (mh.integrable_map_iff).1 (hint2 Ψ hΨ).integral_prod_left
  have hE : ∀ Ψ ∈ schA F κ, ∫ y, (∫ u, Ψ ((D.map (algebraMap F (AF F))) *ᵥ e (h y, u)) ∂μ₁) ∂μ = ∫ z, Ψ ((D.map (algebraMap F (AF F))) *ᵥ z) ∂(((μ.map h).prod μ₁).map e) := fun Ψ hΨ => by
    rw [me.integral_map, integral_prod _ (hint2 Ψ hΨ)]
    exact (mh.integral_map (fun x => ∫ u, Ψ ((D.map (algebraMap F (AF F))) *ᵥ e (x, u)) ∂μ₁)).symm
  refine ⟨fun Ψ hΨ => by simpa only [hkey] using hI Ψ hΨ, ?_⟩
  let I0 : schA F κ →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => ∫ z, (Ψ : (κ → AF F) → ℂ) ((D.map (algebraMap F (AF F))) *ᵥ z) ∂(((μ.map h).prod μ₁).map e)
      map_add' := fun Ψ Ψ' => integral_add (hint _ Ψ.2) (hint _ Ψ'.2)
      map_smul' := fun c Ψ => integral_smul c _ }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend I0
  have hΛa : ∀ Ψ ∈ schA F κ, Λ Ψ = ∫ z, Ψ ((D.map (algebraMap F (AF F))) *ᵥ z) ∂(((μ.map h).prod μ₁).map e) := fun Ψ hΨ => LinearMap.congr_fun hΛ ⟨Ψ, hΨ⟩
  refine ⟨Λ, fun g hg => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨T, hT'⟩ := hT g hg
    refine ⟨T, fun f => ?_⟩
    rw [hΛa _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)]
    exact hT' f
  · rw [hΛa Ψ hΨ, ← hE Ψ hΨ]
    simp only [hkey]

end GlobalTheory.SubspaceInt

end
