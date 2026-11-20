import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSymmRelabel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RelabelTransport
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.IntNumCompPerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w v' w'

/- English proof (translation)
Introduce `F _ K _ ι _ K' _ ι' _ e h hS I hI V n L σ hV`. Establish `key` using `hS _ (Relabel.isFieldIntersection_pull e h hI) (V.map (Relabel.ringEquiv F e h)) n (fun j => L j ∘ e.symm) σ ((Relabel.isProjVarF_map_iff e h V n).2 hV)`. Establish `hL : ∀ L₀ : Fin n → K → ℤ, (fun j => (fun j => L₀ j ∘ e.symm) j ∘ e) = L₀` using `fun L₀ => by`. Use function extensionality and compare the values at `j k`. Simplify using the standard rewrite rules.

Simplify using `only [Relabel.pullFamily, Relabel.comap_map] at key`. Establish `h1` using `hL (L ∘ σ)`. Establish `h2` using `hL L`. Simplify using `only [Function.comp_apply] at h1 h2 key`. Rewrite `key` using `[h1, h2]`.

Conclude with `key`.
-/
theorem SymmRelabel.proof : SymmRelabel.Statement.{u, v, w, v', w'} := by
  intro F _ K _ ι _ K' _ ι' _ e h hS I hI V n L σ hV
  have key := hS _ (Relabel.isFieldIntersection_pull e h hI) (V.map (Relabel.ringEquiv F e h)) n
    (fun j => L j ∘ e.symm) σ ((Relabel.isProjVarF_map_iff e h V n).2 hV)
  have hL : ∀ L₀ : Fin n → K → ℤ, (fun j => (fun j => L₀ j ∘ e.symm) j ∘ e) = L₀ := fun L₀ => by
    funext j k
    simp
  simp only [Relabel.pullFamily, Relabel.comap_map] at key
  have h1 := hL (L ∘ σ)
  have h2 := hL L
  simp only [Function.comp_apply] at h1 h2 key
  rw [h1, h2] at key
  exact key

/- English proof (translation)
The claim follows from `SymmStatement.of_found SymmRelabel.proof F ι`.
-/
theorem SymmStatement.full {K : Type v} [Fintype K] (F : Type u) [Field F] (ι : K → Type w)
    [∀ k, Fintype (ι k)] : SymmStatement F ι :=
  SymmStatement.of_found SymmRelabel.proof F ι

end GroundTheory.Heights₂.Heights.Targets
