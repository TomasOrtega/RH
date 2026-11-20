import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField TensorProduct GroundTheory.Heights₂.Heights

noncomputable section

def IsOrthogonalFamily {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K) {X : Type*}
    (L : X → Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (σ : K →+* ℂ) (x y : X), x ≠ y → ∀ l ∈ L x, ∀ l' ∈ L y,
    (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l') = 0

def S6.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (X : Type) [Fintype X]
    [DecidableEq X] (L : X → Submodule (𝓞 K) E.carrier) (μ : ℝ),
    DirectSum.IsInternal L → (∀ x, E.rank (L x) = 1) → IsOrthogonalFamily E L →
    (∀ x, μ ≤ E.normDegree (L x)) →
    ∀ (E' E'' : HermitianBundle.{0} K), HermitianExtension E' E E'' →
      (E''.rank ⊤ : ℝ) * μ ≤ E''.normDegree ⊤

def coordLines (K : Type*) [Field K] : Fin 2 → Submodule (𝓞 K) (Fin 2 → 𝓞 K) :=
  fun x => LinearMap.range (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x)

/- English proof (translation)
Apply `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` to reduce the goal to its premises. Apply the tactic sequence `rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)]`. Rewrite using `[disjoint_iff_inf_le]`. Introduce and unpack `v ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩`. Establish `h0` using `congrFun hb 0`.

Establish `h1` using `congrFun hb 1`. Simplify using `at h0 h1`. Apply the tactic sequence `ext i; fin_cases i <;> simp [h0.symm]`. Conclude with `LinearMap.iSup_range_single _ _`.
-/
theorem coordLines_isInternal (K : Type*) [Field K] : DirectSum.IsInternal (coordLines K) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)]
    rw [disjoint_iff_inf_le]
    rintro v ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h0 := congrFun hb 0
    have h1 := congrFun hb 1
    simp at h0 h1
    ext i; fin_cases i <;> simp [h0.symm]
  · exact LinearMap.iSup_range_single _ _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Module.finrank (𝓞 K) (LinearMap.range (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x)) = 1`. Establish `hinj : Function.Injective (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x)`. Introduce `a b h`. Simplify using `using congrFun h x`. Rewrite using `[← (LinearEquiv.ofInjective _ hinj).finrank_eq, Module.finrank_self]`.
-/
theorem coordLines_rank (K : Type*) [Field K] [NumberField K] (x : Fin 2) :
    (HermitianBundle.standard K 2).rank (coordLines K x) = 1 := by
  change Module.finrank (𝓞 K) (LinearMap.range (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x)) = 1
  have hinj : Function.Injective (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x) := by
    intro a b h; simpa using congrFun h x
  rw [← (LinearEquiv.ofInjective _ hinj).finrank_eq, Module.finrank_self]

/- English proof (translation)
Rewrite using `[HermitianMetric.standard_inner]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[standardCoord_tmul, standardCoord_tmul]`. Distinguish the cases in `hi : i = x`. Substitute `hi` using the available equality.

Simplify using `[hxy]`. Simplify using `[Pi.single_apply, hi]`.
-/
theorem standard_inner_single_ne (K : Type*) [Field K] [NumberField K] (σ : K →+* ℂ)
    (x y : Fin 2) (hxy : x ≠ y) (a b : 𝓞 K) :
    ((HermitianMetric.standard K (Fin 2)).form σ).inner
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (Pi.single x a : Fin 2 → 𝓞 K))
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (Pi.single y b : Fin 2 → 𝓞 K)) = 0 := by
  rw [HermitianMetric.standard_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [standardCoord_tmul, standardCoord_tmul]
  by_cases hi : i = x
  · subst hi
    simp [hxy]
  · simp [Pi.single_apply, hi]

/- English proof (translation)
Introduce `σ x y hxy l hl l' hl'`. Take `⟨a, rfl⟩` from `hl`. Take `⟨b, rfl⟩` from `hl'`. Conclude with `standard_inner_single_ne K σ x y hxy a b`.
-/
theorem coordLines_orthogonal (K : Type*) [Field K] [NumberField K] :
    IsOrthogonalFamily (HermitianBundle.standard K 2) (coordLines K) := by
  intro σ x y hxy l hl l' hl'
  obtain ⟨a, rfl⟩ := hl
  obtain ⟨b, rfl⟩ := hl'
  exact standard_inner_single_ne K σ x y hxy a b

/- English proof (translation)
Use `⟨coordLines_isInternal ℚ, coordLines_rank ℚ, coordLines_orthogonal ℚ, fun x => ?_, ⟨HermitianExtension.standardSplit ℚ⟩⟩` and prove the remaining obligations. Use `fin_cases x`. Conclude with `min_le_left _ _`. Conclude with `min_le_right _ _`.
-/
theorem S6.hypotheses_inhabited :
    DirectSum.IsInternal (coordLines ℚ) ∧
      (∀ x, (HermitianBundle.standard ℚ 2).rank (coordLines ℚ x) = 1) ∧
      IsOrthogonalFamily (HermitianBundle.standard ℚ 2) (coordLines ℚ) ∧
      (∀ x, min ((HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ 0))
          ((HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ 1)) ≤
        (HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ x)) ∧
      Nonempty (HermitianExtension (HermitianBundle.integers ℚ) (HermitianBundle.standard ℚ 2)
        (HermitianBundle.integers ℚ)) := by
  refine ⟨coordLines_isInternal ℚ, coordLines_rank ℚ, coordLines_orthogonal ℚ, fun x => ?_,
    ⟨HermitianExtension.standardSplit ℚ⟩⟩
  fin_cases x
  · exact min_le_left _ _
  · exact min_le_right _ _

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
