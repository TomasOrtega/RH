import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelFibreFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

/- English proof (translation)
Introduce `K _ ι _ P e M Ψ hP hΨ y`. Take `⟨k0⟩` from `hP.1`. Establish `hH : IsMultiHomogIdeal P` using `hP.2.1.2.1`. Set `f : M.Xc → (((k : K) → ι k) → ℂ)` to `fun x => (Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)`. Use `Set.Finite.of_finite_image (f := f) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, ⟨hxy, hx0⟩, rfl⟩`. Establish `hq : modelQ M Ψ x = y` using `hxy`. Establish `hl` using `(modelLift_spec M x).1 x (mem_modelU M x)`. Establish `hlam : Ψ (segre (modelLift M x x)) 0 ≠ 0` using `fun h => hx0 (Or.inl h)`. Use `⟨fun p => Function.update (1 : K → ℂ) k0 (Ψ (segre (modelLift M x x)) 0)⁻¹ p.1 * modelLift M x x p, mcPts_smul hH _ ?_ hl.1, ?_, ?_⟩` and prove the remaining obligations.

Introduce `k`. Distinguish the cases in `hk : k = k0`. Substitute `hk` using the available equality. Simplify using `[hlam]`. Simplify using `[Function.update_of_ne hk]`.

Rewrite using `[segre_smul, Finset.prod_update_of_mem (Finset.mem_univ _)]`. Simplify using `[f]`. Use `show Ψ ((Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)) = Fin.cons 1 y`. Rewrite using `[map_smul]`. Use function extensionality and compare the values at `i`.

Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[hlam]`. Rewrite using `[← hq]`. Simplify using `[modelQ, div_eq_inv_mul]`. Introduce and unpack `x1 ⟨_, h1⟩ x2 ⟨_, h2⟩ heq`.

Establish `l1` using `(modelLift_spec M x1).1 x1 (mem_modelU M x1)`. Establish `l2` using `(modelLift_spec M x2).1 x2 (mem_modelU M x2)`. Establish `hlam1 : Ψ (segre (modelLift M x1 x1)) 0 ≠ 0` using `fun h => h1 (Or.inl h)`. Establish `hlam2 : Ψ (segre (modelLift M x2 x2)) 0 ≠ 0` using `fun h => h2 (Or.inl h)`. Establish `hseg : segre (modelLift M x1 x1) = (Ψ (segre (modelLift M x1 x1)) 0 / Ψ (segre (modelLift M x2 x2)) 0) • segre (modelLift M x2 x2)`.

Use `congrArg (fun w => Ψ (segre (modelLift M x1 x1)) 0 • w) heq` as an intermediate fact. Simplify using `only [f, smul_smul, mul_inv_cancel₀ hlam1, one_smul] at this`. Rewrite using `[div_eq_mul_inv]`. Conclude with `this`. Take `⟨c, hc, hcz⟩` from `sameOrbit_of_segre l2.1.1 _ (div_ne_zero hlam1 hlam2) hseg`.

Rewrite using `[← l1.2, ← l2.2]`. Conclude with `((M.fibre _ l2.1 _ l1.1).2 ⟨c, hc, hcz⟩).symm`.
-/
theorem ModelFibreFinite.proof : ModelFibreFinite.Statement := by
  intro K _ ι _ P e M Ψ hP hΨ y
  classical
  obtain ⟨k0⟩ := hP.1
  have hH : IsMultiHomogIdeal P := hP.2.1.2.1
  let f : M.Xc → (((k : K) → ι k) → ℂ) := fun x =>
    (Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)
  refine Set.Finite.of_finite_image (f := f) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ?_
  · rintro _ ⟨x, ⟨hxy, hx0⟩, rfl⟩
    have hq : modelQ M Ψ x = y := hxy
    have hl := (modelLift_spec M x).1 x (mem_modelU M x)
    have hlam : Ψ (segre (modelLift M x x)) 0 ≠ 0 := fun h => hx0 (Or.inl h)
    refine ⟨fun p => Function.update (1 : K → ℂ) k0 (Ψ (segre (modelLift M x x)) 0)⁻¹ p.1 *
      modelLift M x x p, mcPts_smul hH _ ?_ hl.1, ?_, ?_⟩
    · intro k
      by_cases hk : k = k0
      · subst hk
        simp [hlam]
      · simp [Function.update_of_ne hk]
    · rw [segre_smul, Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp [f]
    · show Ψ ((Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)) = Fin.cons 1 y
      rw [map_smul]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hlam]
      · rw [← hq]
        simp [modelQ, div_eq_inv_mul]
  · rintro x1 ⟨_, h1⟩ x2 ⟨_, h2⟩ heq
    have l1 := (modelLift_spec M x1).1 x1 (mem_modelU M x1)
    have l2 := (modelLift_spec M x2).1 x2 (mem_modelU M x2)
    have hlam1 : Ψ (segre (modelLift M x1 x1)) 0 ≠ 0 := fun h => h1 (Or.inl h)
    have hlam2 : Ψ (segre (modelLift M x2 x2)) 0 ≠ 0 := fun h => h2 (Or.inl h)
    have hseg : segre (modelLift M x1 x1) =
        (Ψ (segre (modelLift M x1 x1)) 0 / Ψ (segre (modelLift M x2 x2)) 0) •
          segre (modelLift M x2 x2) := by
      have := congrArg (fun w => Ψ (segre (modelLift M x1 x1)) 0 • w) heq
      simp only [f, smul_smul, mul_inv_cancel₀ hlam1, one_smul] at this
      rw [div_eq_mul_inv]
      exact this
    obtain ⟨c, hc, hcz⟩ := sameOrbit_of_segre l2.1.1 _ (div_ne_zero hlam1 hlam2) hseg
    rw [← l1.2, ← l2.2]
    exact ((M.fibre _ l2.1 _ l1.1).2 ⟨c, hc, hcz⟩).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
