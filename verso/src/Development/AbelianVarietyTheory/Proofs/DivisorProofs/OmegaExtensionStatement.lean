import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleMapDeterminedGeneric

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory.Twist (resM)

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.OmegaHT

/- English proof (translation)
Take `⟨c, rfl⟩` from `(hs V h).2 σ`. Rewrite using `[Fintype.linearCombination_apply, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]`. Use `congr 1`.

Establish `na` using `ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) (s i)`. Establish `nb` using `ConcreteCategory.congr_hom (ψ.mapPresheaf.naturality (homOfLE h).op) (s i)`. Conclude with `na.trans ((congrArg (fun t => G.presheaf.map (homOfLE h).op t) (e i)).trans nb.symm)`.
-/
theorem app_eq_of_frame {X : Scheme.{0}} {F G : X.Modules} {r : ℕ} {A : X.Opens} {s : Fin r → Γ(F, A)} (φ ψ : F ⟶ G)
    (hs : GlobalTheory.VB.IsFrame s) (e : ∀ i, φ.app A (s i) = ψ.app A (s i)) (V : X.Opens) (h : V ≤ A) (σ : Γ(F, V)) :
    φ.app V σ = ψ.app V σ := by
  obtain ⟨c, rfl⟩ := (hs V h).2 σ
  rw [Fintype.linearCombination_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  congr 1
  have na := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) (s i)
  have nb := ConcreteCategory.congr_hom (ψ.mapPresheaf.naturality (homOfLE h).op) (s i)
  exact na.trans ((congrArg (fun t => G.presheaf.map (homOfLE h).op t) (e i)).trans nb.symm)

/- English proof (translation)
Introduce `X _ F G r m A s a b hA hs hG e`. Establish `h` using `hG.isTorsionFree`. Use `Scheme.Modules.hom_ext _ _ fun W => ?_` and prove the remaining obligations. Use extensionality with `σ`. Distinguish the cases in `hη : genericPoint X ∈ W`.

Establish `hle : W ⊓ A ≤ W` using `inf_le_left`. Establish `hη' : genericPoint X ∈ W ⊓ A` using `⟨hη, hA⟩`. Use `sub_eq_zero.1 (h W hη _ ?_)` and prove the remaining obligations. Establish `na` using `ConcreteCategory.congr_hom (a.mapPresheaf.naturality (homOfLE hle).op) σ`. Establish `nb` using `ConcreteCategory.congr_hom (b.mapPresheaf.naturality (homOfLE hle).op) σ`.

Establish `e' : G.presheaf.map (homOfLE hle).op (a.app W σ) = G.presheaf.map (homOfLE hle).op (b.app W σ)` using `na.symm.trans ((app_eq_of_frame a b hs e (W ⊓ A) inf_le_right _).trans nb)`. Rewrite using `[map_sub, sub_eq_zero]`. Use `erw [← G.presheaf.germ_res_apply (homOfLE hle) _ hη' (a.app W σ), ← G.presheaf.germ_res_apply (homOfLE hle) _ hη' (b.app W σ), e']`. Establish `hW : W = ⊥`. Assume the negation of the conclusion as `hne`.

Take `⟨x, hx⟩` from `(TopologicalSpace.Opens.ne_bot_iff_nonempty W).1 hne`. Conclude with `hη (GlobalTheory.VB.genericPoint_mem hx)`. Substitute `hW` using the available equality. Conclude with `TopCat.Sheaf.eq_of_locally_eq' ⟨G.presheaf, G.isSheaf⟩ (fun _ : Empty => ⊥) ⊥ (fun i => i.elim) bot_le _ _ (fun i => i.elim)`.
-/
theorem extSt : ExtSt := by
  intro X _ F G r m A s a b hA hs hG e
  have h := hG.isTorsionFree
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext σ
  by_cases hη : genericPoint X ∈ W
  · have hle : W ⊓ A ≤ W := inf_le_left
    have hη' : genericPoint X ∈ W ⊓ A := ⟨hη, hA⟩
    refine sub_eq_zero.1 (h W hη _ ?_)
    have na := ConcreteCategory.congr_hom (a.mapPresheaf.naturality (homOfLE hle).op) σ
    have nb := ConcreteCategory.congr_hom (b.mapPresheaf.naturality (homOfLE hle).op) σ
    have e' : G.presheaf.map (homOfLE hle).op (a.app W σ)
        = G.presheaf.map (homOfLE hle).op (b.app W σ) :=
      na.symm.trans ((app_eq_of_frame a b hs e (W ⊓ A) inf_le_right _).trans nb)
    rw [map_sub, sub_eq_zero]
    erw [← G.presheaf.germ_res_apply (homOfLE hle) _ hη' (a.app W σ),
      ← G.presheaf.germ_res_apply (homOfLE hle) _ hη' (b.app W σ), e']
  · have hW : W = ⊥ := by
      by_contra hne
      obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty W).1 hne
      exact hη (GlobalTheory.VB.genericPoint_mem hx)
    subst hW
    exact TopCat.Sheaf.eq_of_locally_eq' ⟨G.presheaf, G.isSheaf⟩ (fun _ : Empty => ⊥) ⊥
      (fun i => i.elim) bot_le _ _ (fun i => i.elim)

end GlobalTheory.OmegaHT
