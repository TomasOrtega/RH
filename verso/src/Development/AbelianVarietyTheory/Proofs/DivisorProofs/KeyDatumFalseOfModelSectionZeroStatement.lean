import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFalseOfModelSectionZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KeyEven.not_keyOn_of_sec_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKeyDatumFalseOfModelSectionZero.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.keyDatum_false_of_modelSection_zero : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)), KeyOn (RingHom.id K) x G L σ y → (∀ i, σ.f i = 0) → False := by
  first | exact @GlobalTheory.KeyEven.not_keyOn_of_sec_zero | exact GlobalTheory.KeyEven.not_keyOn_of_sec_zero | (intros; apply GlobalTheory.KeyEven.not_keyOn_of_sec_zero <;> assumption)
