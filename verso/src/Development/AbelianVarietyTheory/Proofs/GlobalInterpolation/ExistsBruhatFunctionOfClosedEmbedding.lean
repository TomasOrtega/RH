import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionClosedSubgroup
open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Set `H : Subgroup T` to `j.range`. Establish `hH : IsClosed (H : Set T)`. Simplify `hj.isClosed_range` using `[H, MonoidHom.coe_range]`. Set `e : T' ≃* H` to `MonoidHom.ofInjective hj.injective`. Establish `he : Continuous e` using `hj.continuous.subtype_mk _`.

Establish `hes : Continuous e.symm`. Rewrite using `[hj.isEmbedding.isInducing.continuous_iff]`. Establish `: (fun x : H => j (e.symm x)) = fun x : H => (x : T)`. Use function extensionality and compare the values at `x`. Conclude with `MonoidHom.apply_ofInjective_symm hj.injective x`.

Rewrite using `[Function.comp_def, this]`. Conclude with `continuous_subtype_val`. Establish `: (Measure.map e m').IsHaarMeasure` using `e.isHaarMeasure_map m' he hes`. Take `⟨φ, hφ, hint, -⟩` from `exists_bruhat_function_closed_subgroup T H hH (Measure.map e m')`. Use `⟨fun x => φ x⁻¹, hφ.comp measurable_inv, fun t => ?_⟩` and prove the remaining obligations.

Use `show ∫⁻ s, φ (j s * t)⁻¹ ∂m' = 1`. Establish `h1` using `hint t⁻¹`. Establish `hm : Measurable (fun h : H => φ (t⁻¹ * (h : T)))` using `hφ.comp (continuous_const.mul continuous_subtype_val).measurable`. Rewrite `h1` using `[lintegral_map hm he.measurable]`. Establish `h2 : ∀ s : T', ((e s : H) : T) = j s` using `fun s => rfl`.

Simplify using `only [h2] at h1`. Establish `h3 : ∀ s : T', (j s * t)⁻¹ = t⁻¹ * j s⁻¹` using `fun s => by`. Rewrite using `[mul_inv_rev, map_inv]`. Simplify using `only [h3]`. Rewrite using `[lintegral_inv_eq_self (fun s => φ (t⁻¹ * j s))]`.

Conclude with `h1`.
-/
theorem exists_bruhat_function_closedEmbedding
    (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (m' : Measure T') [m'.IsHaarMeasure]
    [m'.IsInvInvariant] :
    ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  classical
  let H : Subgroup T := j.range
  have hH : IsClosed (H : Set T) := by
    simpa [H, MonoidHom.coe_range] using hj.isClosed_range
  let e : T' ≃* H := MonoidHom.ofInjective hj.injective
  have he : Continuous e := hj.continuous.subtype_mk _
  have hes : Continuous e.symm := by
    rw [hj.isEmbedding.isInducing.continuous_iff]
    have : (fun x : H => j (e.symm x)) = fun x : H => (x : T) := by
      funext x
      exact MonoidHom.apply_ofInjective_symm hj.injective x
    rw [Function.comp_def, this]
    exact continuous_subtype_val
  have : (Measure.map e m').IsHaarMeasure := e.isHaarMeasure_map m' he hes
  obtain ⟨φ, hφ, hint, -⟩ := exists_bruhat_function_closed_subgroup T H hH (Measure.map e m')
  refine ⟨fun x => φ x⁻¹, hφ.comp measurable_inv, fun t => ?_⟩
  show ∫⁻ s, φ (j s * t)⁻¹ ∂m' = 1
  have h1 := hint t⁻¹
  have hm : Measurable (fun h : H => φ (t⁻¹ * (h : T))) :=
    hφ.comp (continuous_const.mul continuous_subtype_val).measurable
  rw [lintegral_map hm he.measurable] at h1
  have h2 : ∀ s : T', ((e s : H) : T) = j s := fun s => rfl
  simp only [h2] at h1
  have h3 : ∀ s : T', (j s * t)⁻¹ = t⁻¹ * j s⁻¹ := fun s => by
    rw [mul_inv_rev, map_inv]
  simp only [h3]
  rw [lintegral_inv_eq_self (fun s => φ (t⁻¹ * j s))]
  exact h1

end GlobalTheory
