import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KeyEven.keyPB_of_keyOn_comp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKeyDatumFibreOfComposableBaseChange.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.keyDatum_fibre_of_composable_baseChange : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G)) (x : KeyIn B) (x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g), KeyOn f x G L σ (fun i => y (i.cast hg)) → KeyOn (h.comp f) x' G L σ (fun i => y (i.cast hg')) → KeyPB x' x h := by
  first | exact @GlobalTheory.KeyEven.keyPB_of_keyOn_comp | exact GlobalTheory.KeyEven.keyPB_of_keyOn_comp | (intros; apply GlobalTheory.KeyEven.keyPB_of_keyOn_comp <;> assumption)
