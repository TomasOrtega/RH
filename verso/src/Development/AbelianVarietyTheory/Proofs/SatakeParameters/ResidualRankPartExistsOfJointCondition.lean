import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.StringRepresentationDecomposition

/- English proof (translation)
Introduce `D hrho i hHG`. Take `⟨x, hx⟩` from `hHG`. Establish `hx'` using `hx`. Take `⟨-, Sig, hSig, hgood⟩` from `hx'`. Take `⟨ρ₀, ξ, -, -, hρx⟩` from `hrho i x hx Sig hSig hgood`.

Conclude with `⟨_, isRhoBar_of_isRhoOf D i x _ hρx⟩`.
-/
theorem rbEx_of_jointCond_rho : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  intro D hrho i hHG
  obtain ⟨x, hx⟩ := hHG
  have hx' := hx
  obtain ⟨-, Sig, hSig, hgood⟩ := hx'
  obtain ⟨ρ₀, ξ, -, -, hρx⟩ := hrho i x hx Sig hSig hgood
  exact ⟨_, isRhoBar_of_isRhoOf D i x _ hρx⟩

end GlobalTheory.StringRepresentationDecomposition
