import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem gm_absFrob (p f : ℕ) (hp : p.Prime) (X : Scheme.{0}) (h : (p : Γ(X, ⊤)) = 0) (y : X)
    (U : X.Opens) (hy : y ∈ U) (a : Γ(X, U)ˣ) :
    gm (GlobalTheory.SS.FrobField.absFrob X p f hp h) y U a = gm (𝟙 X) y U a ^ p ^ f := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, gm_val _ _ _ hy, gm_val _ _ _ hy, ← map_pow]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem picFrob_of : PicFrob := by
  unfold PicFrob
  intro p f hp X h c
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  set F := GlobalTheory.SS.FrobField.absFrob X p f hp h
  have hB : (lbPow L (p ^ f)).IsLB := by
    rw [lbPow]
    exact LB.isLB_linComb hL _ _
  have hmem : ∀ (J : PUnit.{1} → L.ι) (x : X), x ∈ L.U (J PUnit.unit) →
      x ∈ L.wchart (fun _ => 𝟙 X) J := by
    intro J x hx
    show x ∈ ⋂ k, (𝟙 X : X ⟶ X) ⁻¹' (L.U (J k) : Set X)
    rw [Set.mem_iInter]
    intro k
    exact hx
  rw [← GlobalTheory.CechPic.cls_pull hL F (pull_isLB hL F), ← GlobalTheory.CechPic.cls_lbPow hL (p ^ f) hB,
    GlobalTheory.CechPic.cls_eq_iff]
  refine GlobalTheory.CechPic.iso_of_chart hB ⟨fun J => J, ?_, ?_⟩
  · intro J x hx
    exact hmem J x (mem_pull.1 hx)
  · intro y i j hi hj
    have hi' : y ∈ L.U (i PUnit.unit) := mem_pull.1 hi
    have hj' : y ∈ L.U (j PUnit.unit) := mem_pull.1 hj
    rw [gm_pull_g L F (𝟙 X) y i j hi hj]
    erw [gm_linComb L (fun _ => 𝟙 X) (fun _ => ((p ^ f : ℕ) : ℤ)) (𝟙 X) y i j (hmem i y hi')
      (hmem j y hj')]
    rw [Category.id_comp, Category.comp_id, Fintype.prod_unique, zpow_natCast]
    exact gm_absFrob p f hp X h y (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ⟨hi', hj'⟩ _

end UpperTheory.Gal.crystallineComparison.Mod
