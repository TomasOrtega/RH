import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem measure_fund_le_card_mul_of_cover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Λ : Subgroup G) [Countable Λ] (ν : Measure N) (DN : Set N) (b : G) (κ : ℝ≥0∞) (V : Set G) (Y : Finset G), ν.IsHaarMeasure → IsFundamentalDomain (Λ.subgroupOf N) DN ν → IsCompact V → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * b⁻¹ * w * b) → ν DN ≤ Y.card * (κ * ν {u | (u : G) ∈ V}) := by
  intro G _ _ _ _ _ _ _ _ N Λ _ ν DN b κ V Y hν hD hV hconj hY hcov
  have hVm : MeasurableSet V := hV.isClosed.measurableSet
  have hconjm : Measurable fun u : N => b * (u : G) * b⁻¹ :=
    (measurable_const.mul measurable_subtype_coe).mul measurable_const
  have hS₀m : MeasurableSet {u : N | b * (u : G) * b⁻¹ ∈ V} := hconjm hVm
  have hVNm : MeasurableSet {u : N | (u : G) ∈ V} := measurable_subtype_coe hVm
  have hS₀ : ν {u : N | b * (u : G) * b⁻¹ ∈ V} = κ * ν {u : N | (u : G) ∈ V} := by
    have h := hconj (V.indicator 1) (measurable_one.indicator hVm)
    have e1 : (fun u : N => V.indicator (1 : G → ℝ≥0∞) (b * u * b⁻¹))
        = {u : N | b * (u : G) * b⁻¹ ∈ V}.indicator 1 := by
      ext u; simp [Set.indicator]
    have e2 : (fun u : N => V.indicator (1 : G → ℝ≥0∞) u) = {u : N | (u : G) ∈ V}.indicator 1 := by
      ext u; simp [Set.indicator]
    rw [e1, e2, lintegral_indicator hS₀m, lintegral_indicator hVNm] at h
    simpa using h
  have hΛN : Countable (Λ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Λ.subgroupOf N => (⟨(x : N), x.2⟩ : Λ)) ?_
    intro x y h
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg (fun z : Λ => (z : G)) h
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (Λ.subgroupOf N)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (Λ.subgroupOf N) ν
  let T : G → Set N := fun y => {v : N | b * (y⁻¹ * (v : G)) * b⁻¹ ∈ V}
  have hle : ν DN ≤ ν (⋃ y ∈ Y, T y) := by
    refine GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers hD (.of_forall fun u => ?_)
    obtain ⟨γ, hγΛ, hγN, y, hy, w, hw, heq⟩ := hcov u u.2
    refine ⟨⟨⟨γ, hγN⟩, (Subgroup.mem_subgroupOf).2 hγΛ⟩, Set.mem_biUnion hy ?_⟩
    show b * (y⁻¹ * (γ * (u : G))) * b⁻¹ ∈ V
    rw [heq]
    convert hw using 1
    group
  have hT : ∀ y ∈ Y, ν (T y) = κ * ν {u : N | (u : G) ∈ V} := by
    intro y hy
    have hyN : y⁻¹ ∈ N := N.inv_mem (hY y hy)
    have : T y = (fun v : N => (⟨y⁻¹, hyN⟩ : N) * v) ⁻¹' {u : N | b * (u : G) * b⁻¹ ∈ V} := by
      ext v; simp [T, mul_assoc]
    rw [this, measure_preimage_mul, hS₀]
  refine hle.trans ((measure_biUnion_finset_le _ _).trans ?_)
  rw [Finset.sum_congr rfl hT, Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.SphEis
