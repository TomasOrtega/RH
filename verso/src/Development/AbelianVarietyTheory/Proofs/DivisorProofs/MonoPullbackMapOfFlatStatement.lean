import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackMapOfFlat
import Mathlib

open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMonoPullbackMapOfFlat.lean&line=206#L206)
-/
theorem _root_.GlobalTheory.T.mono_pullback_map_of_flat' : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [Flat f] (G G' : Y.Modules) (φ : G ⟶ G') [Mono φ], Mono ((Scheme.Modules.pullback f).map φ) := by
  first | exact @GlobalTheory.mono_pullback_map_of_flat | exact GlobalTheory.mono_pullback_map_of_flat | (intros; apply GlobalTheory.mono_pullback_map_of_flat <;> assumption)
