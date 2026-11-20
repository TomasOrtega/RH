import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, gm_val _ _ _ hy, gm_val _ _ _ hy, ← map_pow]`. Both sides reduce to the same expression.
-/
private theorem gm_absFrob (p f : ℕ) (hp : p.Prime) (X : Scheme.{0}) (h : (p : Γ(X, ⊤)) = 0) (y : X)
    (U : X.Opens) (hy : y ∈ U) (a : Γ(X, U)ˣ) :
    gm (GlobalTheory.SS.FrobField.absFrob X p f hp h) y U a = gm (𝟙 X) y U a ^ p ^ f := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, gm_val _ _ _ hy, gm_val _ _ _ hy, ← map_pow]
  rfl

/- English proof (translation)
Unfold `PicFrob`. Introduce `p f hp X h c`. Take `⟨L, hL, rfl⟩` from `GlobalTheory.CechPic.cls_surj c`. Use `set F := GlobalTheory.SS.FrobField.absFrob X p f hp h`. Establish `hB : (lbPow L (p ^ f)).IsLB`.

Rewrite using `[lbPow]`. Conclude with `LB.isLB_linComb hL _ _`. Establish `hmem : ∀ (J : PUnit.{1} → L.ι) (x : X), x ∈ L.U (J PUnit.unit) → x ∈ L.wchart (fun _ => 𝟙 X) J`. Introduce `J x hx`. Use `show x ∈ ⋂ k, (𝟙 X : X ⟶ X) ⁻¹' (L.U (J k) : Set X)`.

Rewrite using `[Set.mem_iInter]`. Introduce `k`. Conclude with `hx`. Rewrite using `[← GlobalTheory.CechPic.cls_pull hL F (pull_isLB hL F), ← GlobalTheory.CechPic.cls_lbPow hL (p ^ f) hB, GlobalTheory.CechPic.cls_eq_iff]`. Use `GlobalTheory.CechPic.iso_of_chart hB ⟨fun J => J, ?_, ?_⟩` and prove the remaining obligations.

Introduce `J x hx`. Conclude with `hmem J x (mem_pull.1 hx)`. Introduce `y i j hi hj`. Establish `hi' : y ∈ L.U (i PUnit.unit)` using `mem_pull.1 hi`. Establish `hj' : y ∈ L.U (j PUnit.unit)` using `mem_pull.1 hj`.

Rewrite using `[gm_pull_g L F (𝟙 X) y i j hi hj]`. Use `erw [gm_linComb L (fun _ => 𝟙 X) (fun _ => ((p ^ f : ℕ) : ℤ)) (𝟙 X) y i j (hmem i y hi') (hmem j y hj')]`. Rewrite using `[Category.id_comp, Category.comp_id, Fintype.prod_unique, zpow_natCast]`. Conclude with `gm_absFrob p f hp X h y (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ⟨hi', hj'⟩ _`.
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
