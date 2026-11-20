import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TraceUnique

namespace UpperTheory.V.Z.Mult.Pi

/- English proof (translation)
Introduce `J M Y _ _ _ _ _ _ α a hs hk`. Establish `surj : Function.Surjective (FreeAlgebra.lift ℂ α)` using `DiscreteGroups.T1.Desc.Swap3.burnside (FreeAlgebra.lift ℂ α) fun W hW => hs W fun f x hx => by`. Simplify using `using hW (FreeAlgebra.ι ℂ f) x hx`. Take `⟨v, hv⟩` from `exists_ne (0 : M)`. Take `⟨l, hl⟩` from `Module.Projective.exists_dual_eq_one ℂ hv`.

Take `⟨p, hp⟩` from `surj (LinearMap.smulRight l v)`. Establish `same : ∀ r r', FreeAlgebra.lift ℂ α r = FreeAlgebra.lift ℂ α r' → FreeAlgebra.lift ℂ a r = FreeAlgebra.lift ℂ a r'`. Introduce `r r' h`. Establish `h0 : FreeAlgebra.lift ℂ a (r - r') = 0` using `hk _ (by rw [map_sub, h, sub_self])`. Rewrite `h0` using `[map_sub]`.

Conclude with `sub_eq_zero.1 h0`. Establish `idem : LinearMap.smulRight l v * LinearMap.smulRight l v = LinearMap.smulRight l v`. Use extensionality with `x`. Simplify using `[hl]`. Use `⟨p, ?_, ?_, fun q => ⟨l (FreeAlgebra.lift ℂ α q v), ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hp, idem, LinearMap.trace_smulRight, hl]`. Rewrite using `[← map_mul]`. Conclude with `same _ _ (by rw [map_mul, hp, idem])`. Rewrite using `[← map_mul, ← map_mul, ← map_smul]`. Use `same _ _ ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, map_smul, hp]`. Use extensionality with `x`. Simplify using `[smul_smul, mul_comm]`.
-/
theorem minIdem_pf : MinIdem := by
  intro J M Y _ _ _ _ _ _ α a hs hk
  have surj : Function.Surjective (FreeAlgebra.lift ℂ α) :=
    DiscreteGroups.T1.Desc.Swap3.burnside (FreeAlgebra.lift ℂ α) fun W hW => hs W fun f x hx => by
      simpa using hW (FreeAlgebra.ι ℂ f) x hx
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  obtain ⟨p, hp⟩ := surj (LinearMap.smulRight l v)
  have same : ∀ r r', FreeAlgebra.lift ℂ α r = FreeAlgebra.lift ℂ α r' →
      FreeAlgebra.lift ℂ a r = FreeAlgebra.lift ℂ a r' := by
    intro r r' h
    have h0 : FreeAlgebra.lift ℂ a (r - r') = 0 := hk _ (by rw [map_sub, h, sub_self])
    rw [map_sub] at h0
    exact sub_eq_zero.1 h0
  have idem : LinearMap.smulRight l v * LinearMap.smulRight l v = LinearMap.smulRight l v := by
    ext x
    simp [hl]
  refine ⟨p, ?_, ?_, fun q => ⟨l (FreeAlgebra.lift ℂ α q v), ?_⟩⟩
  · rw [hp, idem, LinearMap.trace_smulRight, hl]
  · rw [← map_mul]
    exact same _ _ (by rw [map_mul, hp, idem])
  · rw [← map_mul, ← map_mul, ← map_smul]
    refine same _ _ ?_
    rw [map_mul, map_mul, map_smul, hp]
    ext x
    simp [smul_smul, mul_comm]

end UpperTheory.V.Z.Mult.Pi
