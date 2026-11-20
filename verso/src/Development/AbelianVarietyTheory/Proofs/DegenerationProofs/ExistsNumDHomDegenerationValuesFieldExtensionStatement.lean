import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsNumDHomDegenerationValuesFieldExtension.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.exists_numDHom_degenerationValues_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ (N : NumD F) (N' : NumD F') (ν : NumOf D F N) (ν' : NumOf D F' N'), ν'.th = ν.th → ∃ I : NumD.Hom f N N', I.lam = 1 ∧ (∀ y, ν'.eX (I.e y) = ν.eX y) ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (q : N.QT k) (q' : N'.QT k), QkExt f p p' → ν.QPt p q → ν'.QPt p' q' → q'.1.1.toAdd = I.e q.1.1.toAdd ∧ I.Rel q.1.2 q'.1.2 := by
  first | exact @GlobalTheory.GaugeHom.exists_hom | exact GlobalTheory.GaugeHom.exists_hom | (intros; apply GlobalTheory.GaugeHom.exists_hom <;> assumption)
