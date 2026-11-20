import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TraceUnique

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

/- English proof (translation)
Introduce `J M Y _ _ _ _ _ _ α a C hs hk hc p`. Establish `surj : Function.Surjective (FreeAlgebra.lift ℂ α)` using `DiscreteGroups.T1.Desc.Swap3.burnside (FreeAlgebra.lift ℂ α) fun W hW => hs W fun f x hx => by`. Simplify using `using hW (FreeAlgebra.ι ℂ f) x hx`. Set `lam : FreeAlgebra ℂ J →ₗ[ℂ] ℂ` to `LinearMap.trace ℂ Y ∘ₗ LinearMap.mulRight ℂ C ∘ₗ (FreeAlgebra.lift ℂ a).toLinearMap`. Establish `lam_apply : ∀ r, lam r = LinearMap.trace ℂ Y (FreeAlgebra.lift ℂ a r * C)` using `fun _ => rfl`.

Take `⟨s, hs'⟩` from `LinearMap.exists_rightInverse_of_surjective (FreeAlgebra.lift ℂ α).toLinearMap (LinearMap.range_eq_top.2 surj)`. Establish `sec : ∀ T, FreeAlgebra.lift ℂ α (s T) = T` using `fun T => LinearMap.congr_fun hs' T`. Establish `same : ∀ r r', FreeAlgebra.lift ℂ α r = FreeAlgebra.lift ℂ α r' → lam r = lam r'`. Introduce `r r' h`. Establish `h0 : FreeAlgebra.lift ℂ a (r - r') = 0` using `hk _ (by rw [map_sub, h, sub_self])`.

Establish `h1 : lam (r - r') = 0` using `by rw [lam_apply, h0, zero_mul, map_zero]`. Rewrite `h1` using `[map_sub]`. Conclude with `sub_eq_zero.1 h1`. Set `g : Module.End ℂ M →ₗ[ℂ] ℂ` to `lam ∘ₗ s`. Establish `g_apply : ∀ r, g (FreeAlgebra.lift ℂ α r) = lam r` using `fun r => same _ _ (sec _)`.

Take `⟨c, hc'⟩` from `DiscreteGroups.T1.Desc.Swap3.trace_unique g (by`. Introduce `x y`. Take `⟨r, rfl⟩` from `surj x`. Take `⟨r', rfl⟩` from `surj y`. Rewrite using `[← map_mul, ← map_mul, g_apply, g_apply, lam_apply, lam_apply, map_mul (FreeAlgebra.lift ℂ a), map_mul (FreeAlgebra.lift ℂ a)]`.

Conclude with `hc r r')`. Establish `hp : lam p = c * LinearMap.trace ℂ M (FreeAlgebra.lift ℂ α p)`. Rewrite using `[← g_apply, hc']`. Establish `h1 : LinearMap.trace ℂ Y C = c * (Module.finrank ℂ M : ℂ)`. Use `g_apply 1` as an intermediate fact.

Rewrite `this` using `[hc', map_one (FreeAlgebra.lift ℂ α), LinearMap.trace_one, lam_apply, map_one (FreeAlgebra.lift ℂ a), one_mul]`. Conclude with `this.symm`. Rewrite using `[← lam_apply, hp, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem traceForm_pf : TraceForm := by
  intro J M Y _ _ _ _ _ _ α a C hs hk hc p
  have surj : Function.Surjective (FreeAlgebra.lift ℂ α) :=
    DiscreteGroups.T1.Desc.Swap3.burnside (FreeAlgebra.lift ℂ α) fun W hW => hs W fun f x hx => by
      simpa using hW (FreeAlgebra.ι ℂ f) x hx

  let lam : FreeAlgebra ℂ J →ₗ[ℂ] ℂ :=
    LinearMap.trace ℂ Y ∘ₗ LinearMap.mulRight ℂ C ∘ₗ (FreeAlgebra.lift ℂ a).toLinearMap
  have lam_apply : ∀ r, lam r = LinearMap.trace ℂ Y (FreeAlgebra.lift ℂ a r * C) := fun _ => rfl
  obtain ⟨s, hs'⟩ := LinearMap.exists_rightInverse_of_surjective
    (FreeAlgebra.lift ℂ α).toLinearMap (LinearMap.range_eq_top.2 surj)
  have sec : ∀ T, FreeAlgebra.lift ℂ α (s T) = T := fun T => LinearMap.congr_fun hs' T

  have same : ∀ r r', FreeAlgebra.lift ℂ α r = FreeAlgebra.lift ℂ α r' → lam r = lam r' := by
    intro r r' h
    have h0 : FreeAlgebra.lift ℂ a (r - r') = 0 := hk _ (by rw [map_sub, h, sub_self])
    have h1 : lam (r - r') = 0 := by rw [lam_apply, h0, zero_mul, map_zero]
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1
  let g : Module.End ℂ M →ₗ[ℂ] ℂ := lam ∘ₗ s
  have g_apply : ∀ r, g (FreeAlgebra.lift ℂ α r) = lam r := fun r => same _ _ (sec _)
  obtain ⟨c, hc'⟩ := DiscreteGroups.T1.Desc.Swap3.trace_unique g (by
    intro x y
    obtain ⟨r, rfl⟩ := surj x
    obtain ⟨r', rfl⟩ := surj y
    rw [← map_mul, ← map_mul, g_apply, g_apply, lam_apply, lam_apply,
      map_mul (FreeAlgebra.lift ℂ a), map_mul (FreeAlgebra.lift ℂ a)]
    exact hc r r')
  have hp : lam p = c * LinearMap.trace ℂ M (FreeAlgebra.lift ℂ α p) := by
    rw [← g_apply, hc']
  have h1 : LinearMap.trace ℂ Y C = c * (Module.finrank ℂ M : ℂ) := by
    have := g_apply 1
    rw [hc', map_one (FreeAlgebra.lift ℂ α), LinearMap.trace_one, lam_apply, map_one (FreeAlgebra.lift ℂ a), one_mul] at this
    exact this.symm
  rw [← lam_apply, hp, h1]
  ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
