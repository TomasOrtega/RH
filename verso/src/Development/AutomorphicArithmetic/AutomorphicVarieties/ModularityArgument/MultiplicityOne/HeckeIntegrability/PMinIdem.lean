import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TraceUnique

namespace UpperTheory.V.Z.Mult.Pi

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
