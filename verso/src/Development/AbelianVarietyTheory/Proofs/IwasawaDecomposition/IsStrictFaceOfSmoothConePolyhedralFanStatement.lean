import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictFaceOfSmoothConePolyhedralFan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolFan.FaceStrict.isStrict_face_of_isCone` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsStrictFaceOfSmoothConePolyhedralFan.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.isStrict_face_of_smoothCone_polyhedralFan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar φ X → Dominates bar X → ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m), IsCone bar φ γ → IsStrict bar φ fun i => γ (s i) := by
  first | exact @GlobalTheory.PolFan.FaceStrict.isStrict_face_of_isCone | exact GlobalTheory.PolFan.FaceStrict.isStrict_face_of_isCone | (intros; apply GlobalTheory.PolFan.FaceStrict.isStrict_face_of_isCone <;> assumption)
