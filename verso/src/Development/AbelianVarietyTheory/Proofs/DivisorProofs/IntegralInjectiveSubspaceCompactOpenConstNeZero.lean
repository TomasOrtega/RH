import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `F _ _ v κ _ N ν hν j hj c hc U hUo hUc h0`. Use `letI : MeasurableSpace (Fin N → Fv F v) := borel _`. Use `haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)`. Establish `hjc : Continuous j` using `IsModuleTopology.continuous_of_linearMap j`.

Establish `hgc : Continuous g` using `IsModuleTopology.continuous_of_linearMap g`. Use `set S : Set (Fin N → Fv F v) := j ⁻¹' U with hSdef`. Establish `hSo : IsOpen S` using `hUo.preimage hjc`. Establish `hSsub : S ⊆ g '' U`. Introduce `y hy`.

Use `⟨j y, hy, ?_⟩` and prove the remaining obligations. Use `congrArg (fun f => f y) hg` as an intermediate fact. Simplify using `using this`. Establish `hfin : ν S < ⊤` using `lt_of_le_of_lt (measure_mono hSsub) ((hUc.image hgc).measure_lt_top)`. Establish `hpos : 0 < ν S` using `hSo.measure_pos ν ⟨0, by simp [hSdef, h0]⟩`.

Establish `heq : (fun y => U.indicator (fun _ => c) (j y)) = S.indicator (fun _ => c)`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : j y ∈ U`. Establish `: y ∈ S` using `hy`. Simplify using `[Set.indicator_of_mem hy, Set.indicator_of_mem this]`.

Establish `: y ∉ S` using `hy`. Simplify using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem this]`. Rewrite using `[heq, integral_indicator_const c hSo.measurableSet]`. Use `smul_ne_zero ?_ hc` and prove the remaining obligations. Rewrite using `[Measure.real]`.

Conclude with `ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩`.
-/
theorem GlobalTheory.integral_indicator_preimage_injective_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  intro F _ _ v κ _ N ν hν j hj c hc U hUo hUc h0
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hgc : Continuous g := IsModuleTopology.continuous_of_linearMap g
  set S : Set (Fin N → Fv F v) := j ⁻¹' U with hSdef
  have hSo : IsOpen S := hUo.preimage hjc
  have hSsub : S ⊆ g '' U := by
    intro y hy
    refine ⟨j y, hy, ?_⟩
    have := congrArg (fun f => f y) hg
    simpa using this
  have hfin : ν S < ⊤ := lt_of_le_of_lt (measure_mono hSsub) ((hUc.image hgc).measure_lt_top)
  have hpos : 0 < ν S := hSo.measure_pos ν ⟨0, by simp [hSdef, h0]⟩
  have heq : (fun y => U.indicator (fun _ => c) (j y)) = S.indicator (fun _ => c) := by
    funext y
    by_cases hy : j y ∈ U
    · have : y ∈ S := hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : y ∉ S := hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [heq, integral_indicator_const c hSo.measurableSet]
  refine smul_ne_zero ?_ hc
  rw [Measure.real]
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
