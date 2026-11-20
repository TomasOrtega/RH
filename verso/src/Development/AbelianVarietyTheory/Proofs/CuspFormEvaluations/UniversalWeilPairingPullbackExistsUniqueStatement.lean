import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalWeilPairingPullbackExistsUnique
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCuspFormEvaluations%2FUniversalWeilPairingPullbackExistsUnique.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.universal_weilPairing_pullback_exists_unique : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), 0 < N → (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (x y : T ⟶ Xo.univ.t.G) (e : Γ(T.left, ⊤)ˣ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom e)) ∧ (∀ (T : Over Xo.X) (x y : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → ∃ e : Γ(T.left, ⊤)ˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e ∧ e ^ (N ^ 2) = 1 ∧ ∀ e', WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e' → e' = e) ∧ ∀ (B : Type) [CommRing B] (u : B) (k : ℕ), IsUnit (k : B) → u ^ k = 1 → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ u = 1) → u = 1 := by
  first | exact @GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique | exact GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique | (intros; apply GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique <;> assumption)
