import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldFormallySmooth
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FResidueFieldFormallySmooth.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.residue_field_formally_smooth : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsClosed ({x} : Set X) → letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra; Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  first | exact @_root_.GlobalTheory.residueField_formallySmooth_of_isClosed | exact _root_.GlobalTheory.residueField_formallySmooth_of_isClosed | (intros; apply _root_.GlobalTheory.residueField_formallySmooth_of_isClosed <;> assumption)
