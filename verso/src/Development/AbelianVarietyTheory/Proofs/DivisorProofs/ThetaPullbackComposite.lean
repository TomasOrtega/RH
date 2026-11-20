import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open Limits (pullback)
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PPAS

/- English proof (translation)
Introduce and unpack `S T T' P f g ⟨Q, ψ, ⟨h, hc⟩, L, hL, hs, hcL⟩`. Take `⟨Q', ψ', -, h', hc'⟩` from `exists_pull T T' Q g`. Establish `hsq : sqMap (h'.comp h).1.w = sqMap h'.1.w ≫ sqMap h.1.w`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [sqMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]`.

Simplify using `only [sqMap, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]`. Use `⟨Q', ψ' ≫ ψ, ⟨h'.comp h, ?_⟩, L.pull ψ', pull_isLB hL ψ', PolBaseChange.sym_pull h' hs, ?_⟩` and prove the remaining obligations. Rewrite using `[hc', hc, ← CechPic.pull_comp, hsq]`. Rewrite using `[hc', hcL, pull_sqMap_lam h', CechPic.cls_pull hL]`.
-/
theorem isPull_hasTheta_pull : ∀ (S T T' : Scheme.{0}) (P : PPAS S) (f : T ⟶ S) (g : T' ⟶ T),
    (∃ (Q : PPAS T) (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P f ψ ∧ Q.HasTheta) →
      ∃ (Q : PPAS T') (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (g ≫ f) ψ ∧ Q.HasTheta := by
  rintro S T T' P f g ⟨Q, ψ, ⟨h, hc⟩, L, hL, hs, hcL⟩
  obtain ⟨Q', ψ', -, h', hc'⟩ := exists_pull T T' Q g
  have hsq : sqMap (h'.comp h).1.w = sqMap h'.1.w ≫ sqMap h.1.w := by
    apply pullback.hom_ext
    · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  refine ⟨Q', ψ' ≫ ψ, ⟨h'.comp h, ?_⟩, L.pull ψ', pull_isLB hL ψ', PolBaseChange.sym_pull h' hs, ?_⟩
  · rw [hc', hc, ← CechPic.pull_comp, hsq]
  · rw [hc', hcL, pull_sqMap_lam h', CechPic.cls_pull hL]

end GlobalTheory.PPAS
