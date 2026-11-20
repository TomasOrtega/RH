import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonCharacterGroupOfGoodReductionTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSubsingletonCharacterGroupOfGoodReductionTrait.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.subsingleton_characterGroup_of_goodReduction_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), Set.range ξ ⊆ (U₀ : Set Y.Z) → (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → Subsingleton T.P.D.toPre.X := by
  first | exact @GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset | exact GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset | (intros; apply GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset <;> assumption)
