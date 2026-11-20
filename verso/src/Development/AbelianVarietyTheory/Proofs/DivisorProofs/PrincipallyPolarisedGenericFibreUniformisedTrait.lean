import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.UMin.UnifPolFib

/- English proof (translation)
Introduce `E _ _ _ H S t V _ _ _ _ χ t' ⟨hm⟩ ⟨P⟩`. Use `⟨P.A.g, fun R _ e => ?_⟩` and prove the remaining obligations. Establish `hL : t.PP.L.IsLB` using `RigLB.isLB _`. Establish `hL' : t'.PP.L.IsLB` using `RigLB.isLB _`. Establish `hF : LBIso t'.PP.L (t.PP.L.pull hm.cm.F)`.

Take `⟨w, hw, -, -⟩` from `hm.lin`. Conclude with `⟨w, hw⟩`. Establish `hα : IsGrpPullback P.A.A t'.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V))` using `GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK V) t'.G P.U.gen P.U.gen_hom`. Establish `hLα : LBIso P.A.L (t'.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V)))`. Take `⟨w, hw⟩` from `P.U.ext`.

Establish `hA` using `P.A.isLB`. Establish `hB : LBIso P.A.L ((P.A.L.pull P.U.gen.hom.left).pull P.U.gen.inv.left)`. Establish `e : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _`. Rewrite using `[← Over.comp_left, P.U.gen.inv_hom_id, Over.id_left]`. Establish `h1` using `GlobalTheory.UMin.FibMove.lbIso_pull_comp hA P.U.gen.hom.left P.U.gen.inv.left`.

Rewrite `h1` using `[e]`. Conclude with `LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _) (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) h1`. Establish `hLG : P.U.LG.L.IsLB` using `RigLB.isLB _`. Establish `h2` using `GlobalTheory.ThetaAffineGlue.lbIso_comp hA (pull_isLB hA _) hLG hB ⟨w, hw⟩`. Rewrite `h2` using `[P.bundle]`.

Conclude with `h2`. Establish `h0 : PolFib t'.G t'.PP.L P.A.g (jK V)` using `⟨P.A, _, rfl, hα, hLα⟩`. Establish `h1` using `(GlobalTheory.UMin.FibMove.polFib_move S (Sp V) t.G t.PP.L t'.G t'.PP.L χ hm.cm.F hL hL' hm.cart hF P.A.g (FractionRing V) (jK V)).2 R e h0`. Establish `h2` using `(GlobalTheory.UMin.FibMove.polFib_move S (Sp V) t.G t.PP.L t'.G t'.PP.L χ hm.cm.F hL hL' hm.cart hF P.A.g R (spMap e ≫ jK V)).1.mp h1`. Rewrite `h2` using `[Category.assoc]`. Then use the resulting hypothesis.
-/
theorem polFib_of_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∃ g : ℕ, ∀ (R : Type) [CommRing R] (e : FractionRing V →+* R), PolFib t.G t.PP.L g (spMap e ≫ jK V ≫ χ) := by
  intro E _ _ _ H S t V _ _ _ _ χ t' ⟨hm⟩ ⟨P⟩
  refine ⟨P.A.g, fun R _ e => ?_⟩
  have hL : t.PP.L.IsLB := RigLB.isLB _
  have hL' : t'.PP.L.IsLB := RigLB.isLB _
  have hF : LBIso t'.PP.L (t.PP.L.pull hm.cm.F) := by
    obtain ⟨w, hw, -, -⟩ := hm.lin
    exact ⟨w, hw⟩
  have hα : IsGrpPullback P.A.A t'.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V)) :=
    GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK V) t'.G P.U.gen P.U.gen_hom
  have hLα : LBIso P.A.L (t'.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V))) := by
    obtain ⟨w, hw⟩ := P.U.ext
    have hA := P.A.isLB
    have hB : LBIso P.A.L ((P.A.L.pull P.U.gen.hom.left).pull P.U.gen.inv.left) := by
      have e : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
        rw [← Over.comp_left, P.U.gen.inv_hom_id, Over.id_left]
      have h1 := GlobalTheory.UMin.FibMove.lbIso_pull_comp hA P.U.gen.hom.left P.U.gen.inv.left
      rw [e] at h1
      exact LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _)
        (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) h1
    have hLG : P.U.LG.L.IsLB := RigLB.isLB _
    have h2 := GlobalTheory.ThetaAffineGlue.lbIso_comp hA (pull_isLB hA _) hLG hB ⟨w, hw⟩
    rw [P.bundle] at h2
    exact h2
  have h0 : PolFib t'.G t'.PP.L P.A.g (jK V) := ⟨P.A, _, rfl, hα, hLα⟩
  have h1 := (GlobalTheory.UMin.FibMove.polFib_move S (Sp V) t.G t.PP.L t'.G t'.PP.L χ hm.cm.F hL hL' hm.cart hF P.A.g
    (FractionRing V) (jK V)).2 R e h0
  have h2 := (GlobalTheory.UMin.FibMove.polFib_move S (Sp V) t.G t.PP.L t'.G t'.PP.L χ hm.cm.F hL hL' hm.cart hF P.A.g
    R (spMap e ≫ jK V)).1.mp h1
  rwa [Category.assoc] at h2

end GlobalTheory.UMin.UnifPolFib
