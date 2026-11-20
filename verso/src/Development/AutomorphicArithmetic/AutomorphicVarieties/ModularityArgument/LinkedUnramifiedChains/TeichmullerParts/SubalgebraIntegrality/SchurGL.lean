import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc
import GroundTheory.AutomorphicForms.SmoothRepSchur
open UpperTheory.V.Z.J.D

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Equip the data with the indicated structure. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.J.D.schurGL :
    SchurGL := by
  intro L _ _ n w τ
  letI := τ.acg
  letI := τ.mod
  haveI : τ.ρ.IsIrreducible := τ.irred
  have hsm : GroundTheory.Automorphic.IsSmooth τ.ρ := τ.smooth
  refine ⟨τ.irred, fun f hf => ?_⟩
  let φ : Representation.IntertwiningMap τ.ρ τ.ρ :=
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext fun v => hf g v }
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hsm).2 φ
  exact ⟨c, LinearMap.ext fun v => (congrArg (fun h : Representation.IntertwiningMap τ.ρ τ.ρ => h v) hc).symm⟩
