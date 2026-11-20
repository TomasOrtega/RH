import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicPackage
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalRingCardinality.DataExtra
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.nonempty_provisionalPadPkg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsPadicPackage.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.exists_padic_package : ∀ D : D7, ∃ ng : NgPkg, ∀ (N j : ℕ) (Comp : Type) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)), j ≤ N → Nonempty (PadPkg D N j Comp jC ng) := by
  first | exact @GlobalTheory.nonempty_provisionalPadPkg | exact GlobalTheory.nonempty_provisionalPadPkg | (intros; apply GlobalTheory.nonempty_provisionalPadPkg <;> assumption)
