import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreAffine
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZariskiConn.isPreconnected_fibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FZariskiConnectednessIsPreconnectedFibreAffine.lean&line=132#L132)
-/
theorem _root_.GlobalTheory.T.zariskiConnectedness_isPreconnected_fibre_affine : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) [IsProper f] [IsAffine X] [IsLocallyNoetherian X], Function.Bijective f.appTop → ∀ x : X, _root_.IsPreconnected (f.base ⁻¹' {x}) := by
  first | exact @GlobalTheory.ZariskiConn.isPreconnected_fibre | exact GlobalTheory.ZariskiConn.isPreconnected_fibre | (intros; apply GlobalTheory.ZariskiConn.isPreconnected_fibre <;> assumption)
