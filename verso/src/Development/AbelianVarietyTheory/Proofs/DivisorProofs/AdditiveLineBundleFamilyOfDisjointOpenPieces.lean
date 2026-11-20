import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvcCompOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTrivialOnDisjointCoverStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

/- English proof (translation)
Use `⟨hPt, (GlobalTheory.AbDual.isAdditive_iff hPt).mpr ?_⟩` and prove the remaining obligations. Introduce `Y a a' t`. Establish `hcovY : ⨆ i, (pullback.fst t.left (j i).left).opensRange = ⊤`. Simplify using `only [Scheme.Hom.opensRange_pullbackFst]`. Rewrite using `[← Scheme.Hom.preimage_iSup, hcov]`.

Apply the tactic sequence `try simp`. Establish `hdisjY : Pairwise fun i i' => Disjoint (pullback.fst t.left (j i).left).opensRange (pullback.fst t.left (j i').left).opensRange`. Introduce `i i' hii`. Establish `h : Disjoint (j i).left.opensRange (j i').left.opensRange` using `hdisj hii`. Rewrite using `[Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackFst]`.

Rewrite `h`, the goal using `[disjoint_iff]`. Use `le_antisymm (fun x hx => ?_) bot_le` and prove the remaining obligations. Establish `hx' : t.left x ∈ (j i).left.opensRange ⊓ (j i').left.opensRange` using `⟨hx.1, hx.2⟩`. Rewrite `hx'` using `[h]`. Simplify using `at hx'`.

Rewrite using `[← sub_eq_zero]`. Use `GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover (fun i => pullback.fst t.left (j i).left) hcovY hdisjY _ (fun i => ?_)` and prove the remaining obligations. Set `Zi : Over S` to `Over.mk (pullback.fst t.left (j i).left ≫ Y.hom)`. Set `u : Zi ⟶ Y` to `Over.homMk (pullback.fst t.left (j i).left) rfl`. Establish `hv : pullback.snd t.left (j i).left ≫ (B i).hom = Zi.hom` using `by show pullback.snd t.left (j i).left ≫ (B i).hom = pullback.fst t.left (j i).left ≫ Y.hom`.

Rewrite using `[← Over.w (j i), ← Over.w t, ← Category.assoc, ← Category.assoc, pullback.condition]`. Set `v : Zi ⟶ B i` to `Over.homMk (pullback.snd t.left (j i).left) hv`. Establish `huv : u ≫ t = v ≫ j i`. Use `ext`. Simplify using `[u, v, pullback.condition]`.

Express the relevant statement in the definitionally equal form `GlobalTheory.CechPic.pull u.left _ = 0`. Rewrite using `[map_sub, map_add, GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, huv, evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), MonObj.comp_mul, (Glob …`. Conclude with `sub_self _`.
-/
theorem fam_of_pieces {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left] (hcov : ⨆ i, (j i).left.opensRange = ⊤) (hdisj : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left) (hP : ∀ i, Fam A (P i)) (hPt : Pt.IsLB) (hiso : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) : Fam A Pt := by
  refine ⟨hPt, (GlobalTheory.AbDual.isAdditive_iff hPt).mpr ?_⟩
  intro Y a a' t

  have hcovY : ⨆ i, (pullback.fst t.left (j i).left).opensRange = ⊤ := by
    simp only [Scheme.Hom.opensRange_pullbackFst]
    rw [← Scheme.Hom.preimage_iSup, hcov]
    try simp
  have hdisjY : Pairwise fun i i' => Disjoint (pullback.fst t.left (j i).left).opensRange
      (pullback.fst t.left (j i').left).opensRange := by
    intro i i' hii
    have h : Disjoint (j i).left.opensRange (j i').left.opensRange := hdisj hii
    rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackFst]
    rw [disjoint_iff] at h ⊢
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : t.left x ∈ (j i).left.opensRange ⊓ (j i').left.opensRange := ⟨hx.1, hx.2⟩
    rw [h] at hx'
    simp at hx'

  rw [← sub_eq_zero]
  refine GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover (fun i => pullback.fst t.left (j i).left) hcovY hdisjY _ (fun i => ?_)
  let Zi : Over S := Over.mk (pullback.fst t.left (j i).left ≫ Y.hom)
  let u : Zi ⟶ Y := Over.homMk (pullback.fst t.left (j i).left) rfl
  have hv : pullback.snd t.left (j i).left ≫ (B i).hom = Zi.hom := by
    show pullback.snd t.left (j i).left ≫ (B i).hom = pullback.fst t.left (j i).left ≫ Y.hom
    rw [← Over.w (j i), ← Over.w t, ← Category.assoc, ← Category.assoc, pullback.condition]
  let v : Zi ⟶ B i := Over.homMk (pullback.snd t.left (j i).left) hv
  have huv : u ≫ t = v ≫ j i := by
    ext
    simp [u, v, pullback.condition]
  change GlobalTheory.CechPic.pull u.left _ = 0
  rw [map_sub, map_add, GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, huv,
    evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i),
    evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), MonObj.comp_mul,
    (GlobalTheory.AbDual.isAdditive_iff (hP i).isLB).mp (hP i).add]
  exact sub_self _

end GlobalTheory.DualCon.ProdGlue
