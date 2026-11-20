import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoSpreadGenericNoetherianDomain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LowDat.tateIso_spread` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTateIsoSpreadGenericNoetherianDomain.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.tateIso_spread_generic_noetherian_domain : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : Sp R ⟶ Sp o) (z : o) (k : ℕ), 0 < k →
  Module.finrank ℤ D.La = 2 * P.g → ∀ (pt : D.La → (𝟙_ (Over (Sp R)) ⟶ P.A))
  (F : Type) [Field F] [CharZero F] (x₀ : Sp F ⟶ Sp R) (β₀ : o →+* F), DenseRange x₀ → x₀ ≫ s = spMap β₀ →
  ∀ I₀ : TateIso D F (Over.mk x₀ ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
  (I₀.ζ k : F) = β₀ z → (∀ a, toUnit _ ≫ pt a = I₀.ev k a) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ Sp R) (β : o →+* K), x ≫ s = spMap β →
  ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
    (I.ζ k : K) = β z ∧ ∀ a, toUnit _ ≫ pt a = I.ev k a := by
  first | exact @GlobalTheory.LowDat.tateIso_spread | exact GlobalTheory.LowDat.tateIso_spread | (intros; apply GlobalTheory.LowDat.tateIso_spread <;> assumption)
