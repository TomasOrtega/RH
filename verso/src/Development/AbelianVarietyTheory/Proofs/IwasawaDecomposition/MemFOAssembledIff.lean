import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParPinsOfRec
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

/- English proof (translation)
Introduce `X z`. Establish `hphi : ∀ y : 𝓞 X.B.Ks, X.toD7.what₂.phiO y = X.B.embLL ((y : X.B.Ks) : X.B.LL)` using `fun _ => rfl`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `hle : FO X.toD7 ≤ X.B.Ks.map X.B.embLL.toRatAlgHom`.

Rewrite using `[FO, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `⟨((show 𝓞 X.B.Ks from y : X.B.Ks) : X.B.LL), SetLike.coe_mem _, (hphi y).symm⟩`. Take `⟨x, hx, rfl⟩` from `hle hz`. Conclude with `⟨x, hx, rfl⟩`.

Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨a, b, -, hab⟩` from `IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) (⟨x, hx⟩ : X.B.Ks)`. Establish `hx' : x = ((a : X.B.Ks) : X.B.LL) / ((b : X.B.Ks) : X.B.LL)`. Use `congrArg (fun t : X.B.Ks => (t : X.B.LL)) hab` as an intermediate fact. Conclude with `this.symm`.

Rewrite using `[hx', map_div₀, ← hphi a, ← hphi b]`. Conclude with `div_mem (phiO_mem_FO _ _) (phiO_mem_FO _ _)`.
-/
theorem mem_FO_assembled_iff :
    ∀ (X : Stages) (z : ℂ), z ∈ FO X.toD7 ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z := by
  intro X z
  have hphi : ∀ y : 𝓞 X.B.Ks, X.toD7.what₂.phiO y = X.B.embLL ((y : X.B.Ks) : X.B.LL) := fun _ => rfl
  constructor
  · intro hz
    have hle : FO X.toD7 ≤ X.B.Ks.map X.B.embLL.toRatAlgHom := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, rfl⟩
      exact ⟨((show 𝓞 X.B.Ks from y : X.B.Ks) : X.B.LL), SetLike.coe_mem _, (hphi y).symm⟩
    obtain ⟨x, hx, rfl⟩ := hle hz
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) (⟨x, hx⟩ : X.B.Ks)
    have hx' : x = ((a : X.B.Ks) : X.B.LL) / ((b : X.B.Ks) : X.B.LL) := by
      have := congrArg (fun t : X.B.Ks => (t : X.B.LL)) hab
      exact this.symm
    rw [hx', map_div₀, ← hphi a, ← hphi b]
    exact div_mem (phiO_mem_FO _ _) (phiO_mem_FO _ _)

end GlobalTheory.Mem
