import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleUnionSections
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FVeryAmpleUnionSections.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.very_ample_union_sections : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X), H.IsLB → ∀ (m₁ m₂ m : ℕ) (x : Fin (m₁ + 1) → LB.Sec H) (y : Fin (m₂ + 1) → LB.Sec H) (e : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1)), VeryAmpleBy f H x → VeryAmpleBy f H y → VeryAmpleBy f H (fun j => Sum.elim x y (e j)) := by
  first | exact @GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union | exact GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union | (intros; apply GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union <;> assumption)
