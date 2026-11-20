import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.DualAverage

/- English proof (translation)
Use `(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_` and prove the remaining obligations. Establish `ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' {x : G | σ x u = u})` using `(hσ u).preimage (by fun_prop)`. Use `filter_upwards [ho.mem_nhds (by simp)] with x hx`. Establish `hx' : σ (g⁻¹ * x) u = u` using `hx`. Use `conv_rhs => rw [← hx']`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`.
-/
theorem isLocallyConstant_orbit {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} (hσ : IsSmooth σ) (u : W) :
    IsLocallyConstant fun g : G => σ g u := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' {x : G | σ x u = u}) := (hσ u).preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (by simp)] with x hx
  have hx' : σ (g⁻¹ * x) u = u := hx
  conv_rhs => rw [← hx']
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

/- English proof (translation)
Establish `: CompactSpace H` using `isCompact_iff_compactSpace.1 hH`. Use `borelize ↥H`. Set `η : Measure H` to `Measure.haar`. Establish `hne : ((η.real Set.univ : ℝ) : ℂ) ≠ 0`. Establish `: η.real Set.univ ≠ 0`.

Rewrite using `[Measure.real, ENNReal.toReal_ne_zero]`. Conclude with `⟨(isOpen_univ.measure_pos η Set.univ_nonempty).ne', measure_ne_top _ _⟩`. Conclude with `this` after adjusting the coercions. Establish `hint : ∀ w, Integrable (fun h : H => l₀ (σ ((h : G)⁻¹) w)) η`. Introduce `w`.

Establish `hc : Continuous fun h : H => l₀ (σ ((h : G)⁻¹) w)` using `(((isLocallyConstant_orbit hσ w).comp_continuous (continuous_subtype_val.inv : Continuous fun h : H => (h : G)⁻¹)).comp l₀).continuous`. Conclude with `hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Set `a : Module.Dual ℂ W` to `{ toFun := fun w => ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η map_add' := fun v w => by`. Simplify using `only [map_add]`. Conclude with `integral_add (hint v) (hint w)`.

Use the proof step `map_smul' := fun c w => by`. Simplify using `only [map_smul, RingHom.id_apply]`. Conclude with `integral_smul c _ }`. Establish `ha : ∀ w, a w = ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η` using `fun _ => rfl`. Use `⟨((η.real Set.univ : ℝ) : ℂ)⁻¹ • a, fun h₀ hh₀ w => ?_, fun w hw => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, ha, ha, ← integral_mul_left_eq_self (μ := η) (fun h : H => l₀ (σ ((h : G)⁻¹) (σ h₀ w))) ⟨h₀, hh₀⟩]`. Use `congr 2`. Use function extensionality and compare the values at `h`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[LinearMap.smul_apply, ha]`. Establish `: (fun h : H => l₀ (σ ((h : G)⁻¹) w)) = fun _ => l₀ w`. Use function extensionality and compare the values at `fun h => by rw [hw _ (inv_mem h.2)]`. Rewrite using `[this, integral_const, Complex.real_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]`.
-/
theorem exists_invariant_form (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (H : Subgroup G) (hH : IsCompact (H : Set G)) (l₀ : Module.Dual ℂ W) :
    ∃ l : Module.Dual ℂ W, (∀ h ∈ H, ∀ w, l (σ h w) = l w) ∧
      ∀ w, (∀ h ∈ H, σ h w = w) → l w = l₀ w := by
  have : CompactSpace H := isCompact_iff_compactSpace.1 hH
  borelize ↥H
  let η : Measure H := Measure.haar
  have hne : ((η.real Set.univ : ℝ) : ℂ) ≠ 0 := by
    have : η.real Set.univ ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(isOpen_univ.measure_pos η Set.univ_nonempty).ne', measure_ne_top _ _⟩
    exact_mod_cast this
  have hint : ∀ w, Integrable (fun h : H => l₀ (σ ((h : G)⁻¹) w)) η := by
    intro w
    have hc : Continuous fun h : H => l₀ (σ ((h : G)⁻¹) w) :=
      (((isLocallyConstant_orbit hσ w).comp_continuous
        (continuous_subtype_val.inv : Continuous fun h : H => (h : G)⁻¹)).comp l₀).continuous
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let a : Module.Dual ℂ W :=
    { toFun := fun w => ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η
      map_add' := fun v w => by
        simp only [map_add]
        exact integral_add (hint v) (hint w)
      map_smul' := fun c w => by
        simp only [map_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have ha : ∀ w, a w = ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η := fun _ => rfl
  refine ⟨((η.real Set.univ : ℝ) : ℂ)⁻¹ • a, fun h₀ hh₀ w => ?_, fun w hw => ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, ha, ha,
      ← integral_mul_left_eq_self (μ := η) (fun h : H => l₀ (σ ((h : G)⁻¹) (σ h₀ w))) ⟨h₀, hh₀⟩]
    congr 2
    funext h
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  · rw [LinearMap.smul_apply, ha]
    have : (fun h : H => l₀ (σ ((h : G)⁻¹) w)) = fun _ => l₀ w :=
      funext fun h => by rw [hw _ (inv_mem h.2)]
    rw [this, integral_const, Complex.real_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end GlobalTheory.SmGL.DualAverage
