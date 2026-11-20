import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimitiveRootNotPrimePowMapNeOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.primitiveRoot_notPrimePow_map_ne_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FPrimitiveRootNotPrimePowMapNeOne.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.primitiveRoot_notPrimePow_map_ne_one' : ∀ (k : Type) [Field k] (O : Type) [CommRing O] [IsDomain O] (f : O →+* k) (ζ : O) (n : ℕ), 1 < n → IsPrimitiveRoot ζ n → (¬ IsPrimePow n) → f ζ ≠ 1 := by
  first | exact @GlobalTheory.primitiveRoot_notPrimePow_map_ne_one | exact GlobalTheory.primitiveRoot_notPrimePow_map_ne_one | (intros; apply GlobalTheory.primitiveRoot_notPrimePow_map_ne_one <;> assumption)
