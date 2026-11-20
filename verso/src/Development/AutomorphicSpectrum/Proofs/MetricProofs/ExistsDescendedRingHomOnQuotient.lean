import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.QuotUniv

/- English proof (translation)
Take `⟨s, hs⟩` from `q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)`. Establish `hqs : ∀ w, q (s w) = w` using `fun w => LinearMap.congr_fun hs w`. Choose the witnesses or unpack the hypotheses as in `⟨F, hF⟩ : ∃ F : O → Module.End ℂ (Fin g' → ℂ), ∀ a z, F a (q z) = q (B a z) := by`. Use `⟨fun a => q ∘ₗ (B a ∘ₗ s), fun a z => ?_⟩` and prove the remaining obligations. Establish `h0 : q (B a (s (q z) - z)) = 0` using `hk a _ (by rw [map_sub, hqs, sub_self])`.

Rewrite `h0` using `[map_sub, map_sub, sub_eq_zero]`. Conclude with `h0`. Establish `hext : ∀ L M : Module.End ℂ (Fin g' → ℂ), (∀ z, L (q z) = M (q z)) → L = M`. Introduce `L M h`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations.

Take `⟨z, rfl⟩` from `hq w`. Conclude with `h z`. Use `⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun a z => hF a z⟩` and prove the remaining obligations. Conclude with `hext _ _ fun z => by simp [hF]`. Introduce `a b`.

Conclude with `hext _ _ fun z => by simp [hF, Module.End.mul_apply]`. Conclude with `hext _ _ fun z => by simp [hF]`. Introduce `a b`. Conclude with `hext _ _ fun z => by simp [hF]`.
-/
theorem ringAction_descends_along_surjection
    (O : Type) [Ring O] (g g' : ℕ) (B : O →+* Module.End ℂ (Fin g → ℂ))
    (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hq : Function.Surjective q)
    (hk : ∀ (a : O) z, q z = 0 → q (B a z) = 0) :
    ∃ B' : O →+* Module.End ℂ (Fin g' → ℂ), ∀ a z, B' a (q z) = q (B a z) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqs : ∀ w, q (s w) = w := fun w => LinearMap.congr_fun hs w
  obtain ⟨F, hF⟩ : ∃ F : O → Module.End ℂ (Fin g' → ℂ), ∀ a z, F a (q z) = q (B a z) := by
    refine ⟨fun a => q ∘ₗ (B a ∘ₗ s), fun a z => ?_⟩
    have h0 : q (B a (s (q z) - z)) = 0 := hk a _ (by rw [map_sub, hqs, sub_self])
    rw [map_sub, map_sub, sub_eq_zero] at h0
    exact h0
  have hext : ∀ L M : Module.End ℂ (Fin g' → ℂ), (∀ z, L (q z) = M (q z)) → L = M := by
    intro L M h
    refine LinearMap.ext fun w => ?_
    obtain ⟨z, rfl⟩ := hq w
    exact h z
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun a z => hF a z⟩
  · exact hext _ _ fun z => by simp [hF]
  · intro a b
    exact hext _ _ fun z => by simp [hF, Module.End.mul_apply]
  · exact hext _ _ fun z => by simp [hF]
  · intro a b
    exact hext _ _ fun z => by simp [hF]

end GlobalTheory.CompanionTheory.Ar.QuotUniv
