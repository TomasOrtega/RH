import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalDescendedBundleNoetherian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FRelAmplePrincipalDescendedBundleNoetherian.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.relAmple_principal_descendedBundle_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R), Nat.card {x : Over.mk t ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) → LBIso (lbPow P.L n) (M.pull ψ.left) → Out.RelAmple B M ∧ Out.KTriv B M := by
  first | exact @GlobalTheory.relAmple_kTriv_of_descent_family | exact GlobalTheory.relAmple_kTriv_of_descent_family | (intros; apply GlobalTheory.relAmple_kTriv_of_descent_family <;> assumption)
