import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open GroundTheory.Global.Elliptic
open scoped Real ModularForm UpperHalfPlane

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.
-/
theorem DeltaEta.proof : DeltaEta.Statement := by
  intro τ
  rw [latticeDiscr_lattice, discr_latticeOfTau]
  simp only [ModularForm.discriminant]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.ChowlaSelberg
