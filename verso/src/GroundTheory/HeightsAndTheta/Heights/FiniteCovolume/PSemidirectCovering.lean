import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectCovering

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal

noncomputable section

/- English proof (translation)
Introduce `i q j hi hq hj hqi hker μL _ μN _ hconj Γ C T hC hT hTfin hCcov hTcov ν _`. Establish `hqj : ∀ n, q (j n) = 1` using `fun n => (hker _).2 ⟨n, rfl⟩`. Establish `hmem : ∀ g, g * (i (q g))⁻¹ ∈ Set.range j` using `fun g => (hker _).1 (by simp [hqi])`. Set `e` to `Equiv.ofInjective j hj.injective`. Set `k : H → N` to `fun g => e.symm ⟨g * (i (q g))⁻¹, hmem g⟩`.

Establish `hjk : ∀ g, j (k g) = g * (i (q g))⁻¹` using `fun g => Equiv.apply_ofInjective_symm hj.injective _`. Establish `hk : Continuous k`. Rewrite using `[hj.isEmbedding.continuous_iff]`. Establish `: (j ∘ k) = fun g => g * (i (q g))⁻¹` using `funext hjk`. Rewrite using `[this]`.

Use `fun_prop`. Set `Φ : N × L ≃ₜ H` to `{ toFun := fun p => j p.1 * i p.2 invFun := fun g => (k g, q g) left_inv := fun p => by`. Establish `h1 : q (j p.1 * i p.2) = p.2` using `by simp [hqj, hqi]`. Use `Prod.ext (hj.injective ?_) h1` and prove the remaining obligations. Rewrite using `[hjk, h1]`.

Simplify using the standard rewrite rules. Use `right_inv := fun g => by simp [hjk]`. Use `continuous_toFun := by fun_prop`. Use `continuous_invFun := hk.prodMk hq }`. Establish `hΦ : ∀ p, Φ p = j p.1 * i p.2` using `fun _ => rfl`.

Set `μ' : Measure H` to `(μN.prod μL).map Φ`. Establish `: IsFiniteMeasureOnCompacts μ'` using `⟨fun K hK => by`. Rewrite using `[Measure.map_apply Φ.continuous.measurable hK.isClosed.measurableSet]`. Conclude with `(Φ.isCompact_preimage.2 hK).measure_lt_top⟩`. Establish `: IsOpenPosMeasure μ'` using `Φ.continuous.isOpenPosMeasure_map Φ.surjective`.

Establish `: IsMulLeftInvariant μ'`. Use `⟨fun h => ?_⟩` and prove the remaining obligations. Take `⟨⟨n₀, l₀⟩, rfl⟩` from `Φ.surjective h`. Set `c : N → N` to `fun n => k (i l₀ * j n * (i l₀)⁻¹)`. Establish `hjc : ∀ n, j (c n) = i l₀ * j n * (i l₀)⁻¹` using `fun n => by`.

Simplify using `only [c, hjk, map_mul, map_inv, hqj, hqi]`. Simplify using the standard rewrite rules. Establish `hcc : Continuous c` using `by fun_prop`. Establish `hcμ : MeasurePreserving c μN μN`. Use `⟨hcc.measurable, ?_⟩` and prove the remaining obligations.

Establish `hjm` using `hj.measurableEmbedding`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Measure.map_map hjm.measurable hcc.measurable, show j ∘ c = fun n => i l₀ * j n * (i l₀)⁻¹ from funext hjc, hconj l₀]`. Use `_ = μN := hjm.comap_map _`. Establish `hF : MeasurePreserving (Prod.map (fun n => n₀ * c n) (fun l => l₀ * l)) (μN.prod μL) (μN.prod μL)` using `((measurePreserving_mul_left μN n₀).comp hcμ).prod (measurePreserving_mul_left μL l₀)`.

Establish `hcomp : (fun g => Φ (n₀, l₀) * g) ∘ Φ = Φ ∘ Prod.map (fun n => n₀ * c n) (fun l => l₀ * l)`. Use function extensionality and compare the values at `⟨n, l⟩`. Simplify using `only [Function.comp_apply, hΦ, Prod.map_fst, Prod.map_snd, map_mul, hjc]`. Use `group`. Simplify using `only [μ']`.

Rewrite using `[Measure.map_map (measurable_const_mul _) Φ.continuous.measurable, hcomp, ← Measure.map_map Φ.continuous.measurable hF.measurable, hF.map_eq]`. Establish `: IsHaarMeasure μ'` using `{}`. Use `⟨Φ.symm ⁻¹' (C ×ˢ T), Φ.symm.continuous.measurable (hC.isClosed.measurableSet.prod hT), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[isMulLeftInvariant_eq_smul ν μ', Measure.smul_apply, Measure.map_apply Φ.continuous.measurable (Φ.symm.continuous.measurable (hC.isClosed.measurableSet.prod hT))]`. Establish `: Φ ⁻¹' (Φ.symm ⁻¹' (C ×ˢ T)) = C ×ˢ T` using `by ext p; simp`.

Rewrite using `[this, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]`. Conclude with `ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top hC.measure_lt_top hTfin)`. Introduce `g`. Take `⟨γ₁, hγ₁, hγ₁T⟩` from `hTcov (q g)`. Take `⟨δ, hδ, hδC⟩` from `hCcov (k (γ₁ * g))`.

Use `⟨j δ * γ₁, Γ.mul_mem hδ hγ₁, ?_⟩` and prove the remaining obligations. Establish `h1 : q (j δ * γ₁ * g) = q γ₁ * q g` using `by simp [hqj]`. Establish `h2 : k (j δ * γ₁ * g) = δ * k (γ₁ * g)`. Apply `hj.injective` to reduce the goal to its premises. Rewrite using `[hjk, h1, map_mul j, hjk, map_mul i]`.

Simplify using `[mul_assoc]`. Use `show (k (j δ * γ₁ * g), q (j δ * γ₁ * g)) ∈ C ×ˢ T`. Rewrite using `[h1, h2]`. Conclude with `⟨hδC, hγ₁T⟩`.
-/
theorem SemidirectCovering.proof (H L N : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [SecondCountableTopology L] [T2Space L] [MeasurableSpace L]
    [BorelSpace L] [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] :
    SemidirectCovering.Statement H L N := by
  intro i q j hi hq hj hqi hker μL _ μN _ hconj Γ C T hC hT hTfin hCcov hTcov ν _
  have hqj : ∀ n, q (j n) = 1 := fun n => (hker _).2 ⟨n, rfl⟩
  have hmem : ∀ g, g * (i (q g))⁻¹ ∈ Set.range j := fun g =>
    (hker _).1 (by simp [hqi])
  let e := Equiv.ofInjective j hj.injective
  let k : H → N := fun g => e.symm ⟨g * (i (q g))⁻¹, hmem g⟩
  have hjk : ∀ g, j (k g) = g * (i (q g))⁻¹ := fun g =>
    Equiv.apply_ofInjective_symm hj.injective _
  have hk : Continuous k := by
    rw [hj.isEmbedding.continuous_iff]
    have : (j ∘ k) = fun g => g * (i (q g))⁻¹ := funext hjk
    rw [this]; fun_prop

  let Φ : N × L ≃ₜ H :=
    { toFun := fun p => j p.1 * i p.2
      invFun := fun g => (k g, q g)
      left_inv := fun p => by
        have h1 : q (j p.1 * i p.2) = p.2 := by simp [hqj, hqi]
        refine Prod.ext (hj.injective ?_) h1
        rw [hjk, h1]; simp
      right_inv := fun g => by simp [hjk]
      continuous_toFun := by fun_prop
      continuous_invFun := hk.prodMk hq }
  have hΦ : ∀ p, Φ p = j p.1 * i p.2 := fun _ => rfl
  let μ' : Measure H := (μN.prod μL).map Φ
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun K hK => by
    rw [Measure.map_apply Φ.continuous.measurable hK.isClosed.measurableSet]
    exact (Φ.isCompact_preimage.2 hK).measure_lt_top⟩
  have : IsOpenPosMeasure μ' := Φ.continuous.isOpenPosMeasure_map Φ.surjective
  have : IsMulLeftInvariant μ' := by
    refine ⟨fun h => ?_⟩
    obtain ⟨⟨n₀, l₀⟩, rfl⟩ := Φ.surjective h

    let c : N → N := fun n => k (i l₀ * j n * (i l₀)⁻¹)
    have hjc : ∀ n, j (c n) = i l₀ * j n * (i l₀)⁻¹ := fun n => by
      simp only [c, hjk, map_mul, map_inv, hqj, hqi]; simp
    have hcc : Continuous c := by fun_prop
    have hcμ : MeasurePreserving c μN μN := by
      refine ⟨hcc.measurable, ?_⟩
      have hjm := hj.measurableEmbedding
      calc μN.map c = (((μN.map c).map j).comap j) := (hjm.comap_map _).symm
        _ = ((μN.map j).comap j) := by
          rw [Measure.map_map hjm.measurable hcc.measurable,
            show j ∘ c = fun n => i l₀ * j n * (i l₀)⁻¹ from funext hjc, hconj l₀]
        _ = μN := hjm.comap_map _
    have hF : MeasurePreserving (Prod.map (fun n => n₀ * c n) (fun l => l₀ * l))
        (μN.prod μL) (μN.prod μL) :=
      ((measurePreserving_mul_left μN n₀).comp hcμ).prod (measurePreserving_mul_left μL l₀)
    have hcomp : (fun g => Φ (n₀, l₀) * g) ∘ Φ =
        Φ ∘ Prod.map (fun n => n₀ * c n) (fun l => l₀ * l) := by
      funext ⟨n, l⟩
      simp only [Function.comp_apply, hΦ, Prod.map_fst, Prod.map_snd, map_mul, hjc]
      group
    simp only [μ']
    rw [Measure.map_map (measurable_const_mul _) Φ.continuous.measurable, hcomp,
      ← Measure.map_map Φ.continuous.measurable hF.measurable, hF.map_eq]
  have : IsHaarMeasure μ' := {}

  refine ⟨Φ.symm ⁻¹' (C ×ˢ T), Φ.symm.continuous.measurable (hC.isClosed.measurableSet.prod hT),
    ?_, ?_⟩
  · rw [isMulLeftInvariant_eq_smul ν μ', Measure.smul_apply,
      Measure.map_apply Φ.continuous.measurable
        (Φ.symm.continuous.measurable (hC.isClosed.measurableSet.prod hT))]
    have : Φ ⁻¹' (Φ.symm ⁻¹' (C ×ˢ T)) = C ×ˢ T := by ext p; simp
    rw [this, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top hC.measure_lt_top hTfin)
  · intro g
    obtain ⟨γ₁, hγ₁, hγ₁T⟩ := hTcov (q g)
    obtain ⟨δ, hδ, hδC⟩ := hCcov (k (γ₁ * g))
    refine ⟨j δ * γ₁, Γ.mul_mem hδ hγ₁, ?_⟩
    have h1 : q (j δ * γ₁ * g) = q γ₁ * q g := by simp [hqj]
    have h2 : k (j δ * γ₁ * g) = δ * k (γ₁ * g) := by
      apply hj.injective
      rw [hjk, h1, map_mul j, hjk, map_mul i]
      simp [mul_assoc]
    show (k (j δ * γ₁ * g), q (j δ * γ₁ * g)) ∈ C ×ˢ T
    rw [h1, h2]
    exact ⟨hδC, hγ₁T⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
