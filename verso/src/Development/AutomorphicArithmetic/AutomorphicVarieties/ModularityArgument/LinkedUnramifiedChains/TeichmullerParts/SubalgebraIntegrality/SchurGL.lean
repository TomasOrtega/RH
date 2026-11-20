import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc
import GroundTheory.AutomorphicForms.SmoothRepSchur
open UpperTheory.V.Z.J.D

/- English proof (translation)
Introduce `L _ _ n w τ`. Use `letI := τ.acg`. Use `letI := τ.mod`. Use `haveI : τ.ρ.IsIrreducible := τ.irred`. Establish `hsm : GroundTheory.Automorphic.IsSmooth τ.ρ` using `τ.smooth`.

Use `⟨τ.irred, fun f hf => ?_⟩` and prove the remaining obligations. Set `φ : Representation.IntertwiningMap τ.ρ τ.ρ` to `{ toLinearMap := f, isIntertwining' := fun g => LinearMap.ext fun v => hf g v }`. Take `⟨c, hc⟩` from `(GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hsm).2 φ`. Conclude with `⟨c, LinearMap.ext fun v => (congrArg (fun h : Representation.IntertwiningMap τ.ρ τ.ρ => h v) hc).symm⟩`.
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
