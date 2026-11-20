import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

/- English proof (translation)
Establish `hcl : ∀ w : Glob1 F, clAll F hc w = Hyp1.mk F (formZZ F ⟨w, hc ▸ Submodule.mem_top⟩)` using `fun w ↦ rfl`. Establish `hsum : ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) = Hyp2.mk F (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩) (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩))`. Simplify using `only [hcl, cupHyp_mk, map_sum]`. Establish `hval : ∀ T, (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩) (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.2.2 T = wsum F u v T`. Introduce `T`.

Simplify using `only [Submodule.coe_sum, Prod.snd_sum, Finset.sum_apply, coe_cupZZ, cupTot_η, wsum]`. Both sides reduce to the same expression. Establish `h1 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩) (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.1 T T' T'' φ ψ = 0`. Introduce `T T' T'' φ ψ`. Simplify using `only [Submodule.coe_sum, Prod.fst_sum, Finset.sum_apply, coe_cupZZ, cupTot_apply]`.

Use `Finset.sum_eq_zero fun k _ ↦ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mp F ψ 0 * 0 = 0`. Simplify using the standard rewrite rules. Establish `h2 : ∀ T T' (φ : T ⟶ T'), (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩) (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.2.1 T T' φ = 0`. Introduce `T T' φ`.

Simplify using `only [Submodule.coe_sum, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, coe_cupZZ, cupTot_a]`. Use `Finset.sum_eq_zero fun k _ ↦ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(0 : F.obj T') • _ - (0 : F.obj T') • _ = 0`. Simplify using the standard rewrite rules. Rewrite using `[hsum, Hyp2.mk_eq_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, he⟩`. Establish `hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), (dTot1 F e).1 T T' T'' φ ψ = 0` using `fun T T' T'' φ ψ ↦ by`. Rewrite using `[he]`. Conclude with `h1 T T' T'' φ ψ`.

Establish `ha : ∀ T T' (φ : T ⟶ T'), e.2 T' = p1 F φ (e.2 T) + D R _ (e.1 T T' φ)` using `fun T T' φ ↦ by`. Use `(congrArg (fun x : Tot2 F ↦ x.2.1 T T' φ) he).trans (h2 T T' φ)` as an intermediate fact. Rewrite `this` using `[dTot1_a]`. Rewrite `this` using `[sub_sub, sub_eq_zero]`. Conclude with `this`.

Establish `hη : ∀ T, dOne R _ (e.2 T) = wsum F u v T` using `fun T ↦ by`. Use `congrArg (fun x : Tot2 F ↦ x.2.2 T) he` as an intermediate fact. Rewrite `this` using `[dTot1_η]`. Rewrite using `[this, hval]`. Establish `hf : e.1 ∈ Z1 F`.

Rewrite using `[commAlgFunctorCocyclesOne_eq_ker]`. Use function extensionality and compare the values at `T T' T'' φ ψ`. Conclude with `hz T T' T'' φ ψ`. Take `⟨c, hcz⟩` from `hs (CatCoh.H1.mk F ⟨e.1, hf⟩)`. Take `⟨cz, rfl⟩` from `Hyp1.mk_surjective F c`.

Rewrite `hcz` using `[toO_mk, CatCoh.H1.mk_eq_mk]`. Take `⟨g, hg⟩` from `hcz`. Establish `hg' : ∀ T T' (φ : T ⟶ T'), g T' - mp F φ (g T) = cz.1.1 T T' φ - e.1 T T' φ` using `fun T T' φ ↦ congrFun (congrFun (congrFun hg T) T') φ`. Set `θ : A0 F` to `fun T ↦ e.2 T - (cz.1.2 T - D R _ (g T))`. Establish `hθ : θ ∈ Glob1 F`.

Introduce `T T' φ`. Simplify using `only [θ, map_sub, p1_D]`. Establish `hgT : g T' = mp F φ (g T) + (cz.1.1 T T' φ - e.1 T T' φ)` using `by rw [← hg' T T' φ]; abel`. Rewrite using `[ha T T' φ, cechDeRhamTotalCocyclesOne.conn cz φ, hgT]`. Simplify using `only [map_add, map_sub]`.

Normalize the expressions using the abelian group laws. Establish `hθc : (⟨θ, hθ⟩ : Glob1 F) ∈ Closed1 F` using `hc ▸ Submodule.mem_top`. Use function extensionality and compare the values at `T`. Establish `hθ0 : dOne R _ (e.2 T - (cz.1.2 T - D R _ (g T))) = 0` using `hθc T`. Rewrite `hθ0` using `[map_sub, map_sub, cechDeRhamTotalCocyclesOne.closed cz T, dOne_D, sub_zero, sub_zero]`.

Rewrite using `[← hη T, hθ0]`. Both sides reduce to the same expression. Introduce `hw`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero]`.

Use `Tot2.ext (fun T T' T'' φ ψ ↦ (h1 T T' T'' φ ψ).symm) (fun T T' φ ↦ (h2 T T' φ).symm) fun T ↦ ?_` and prove the remaining obligations. Rewrite using `[hval, hw]`. Both sides reduce to the same expression.
-/
theorem cupSum_eq_zero_iff_wsum_eq_zero (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hc : Closed1 F = ⊤) (hs : Function.Surjective (toO F)) (n : ℕ)
    (u v : Fin n → Glob1 F) :
    ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) = 0 ↔ wsum F u v = 0 := by
  have hcl : ∀ w : Glob1 F, clAll F hc w = Hyp1.mk F (formZZ F ⟨w, hc ▸ Submodule.mem_top⟩) :=
    fun w ↦ rfl
  have hsum : ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) =
      Hyp2.mk F (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)) := by
    simp only [hcl, cupHyp_mk, map_sum]
  have hval : ∀ T, (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.2.2 T = wsum F u v T := by
    intro T
    simp only [Submodule.coe_sum, Prod.snd_sum, Finset.sum_apply, coe_cupZZ, cupTot_η, wsum]
    rfl
  have h1 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    simp only [Submodule.coe_sum, Prod.fst_sum, Finset.sum_apply, coe_cupZZ, cupTot_apply]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    change mp F ψ 0 * 0 = 0
    simp
  have h2 : ∀ T T' (φ : T ⟶ T'), (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.2.1 T T' φ = 0 := by
    intro T T' φ
    simp only [Submodule.coe_sum, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, coe_cupZZ, cupTot_a]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    change (0 : F.obj T') • _ - (0 : F.obj T') • _ = 0
    simp
  rw [hsum, Hyp2.mk_eq_zero]
  constructor
  · rintro ⟨e, he⟩
    have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), (dTot1 F e).1 T T' T'' φ ψ = 0 := fun T T' T'' φ ψ ↦ by
      rw [he]; exact h1 T T' T'' φ ψ
    have ha : ∀ T T' (φ : T ⟶ T'), e.2 T' = p1 F φ (e.2 T) + D R _ (e.1 T T' φ) := fun T T' φ ↦ by
      have := (congrArg (fun x : Tot2 F ↦ x.2.1 T T' φ) he).trans (h2 T T' φ)
      rw [dTot1_a] at this
      rw [sub_sub, sub_eq_zero] at this
      exact this
    have hη : ∀ T, dOne R _ (e.2 T) = wsum F u v T := fun T ↦ by
      have := congrArg (fun x : Tot2 F ↦ x.2.2 T) he
      rw [dTot1_η] at this
      rw [this, hval]
    have hf : e.1 ∈ Z1 F := by
      rw [commAlgFunctorCocyclesOne_eq_ker]
      funext T T' T'' φ ψ
      exact hz T T' T'' φ ψ
    obtain ⟨c, hcz⟩ := hs (CatCoh.H1.mk F ⟨e.1, hf⟩)
    obtain ⟨cz, rfl⟩ := Hyp1.mk_surjective F c
    rw [toO_mk, CatCoh.H1.mk_eq_mk] at hcz
    obtain ⟨g, hg⟩ := hcz
    have hg' : ∀ T T' (φ : T ⟶ T'), g T' - mp F φ (g T) = cz.1.1 T T' φ - e.1 T T' φ := fun T T' φ ↦
      congrFun (congrFun (congrFun hg T) T') φ
    let θ : A0 F := fun T ↦ e.2 T - (cz.1.2 T - D R _ (g T))
    have hθ : θ ∈ Glob1 F := by
      intro T T' φ
      simp only [θ, map_sub, p1_D]
      have hgT : g T' = mp F φ (g T) + (cz.1.1 T T' φ - e.1 T T' φ) := by rw [← hg' T T' φ]; abel
      rw [ha T T' φ, cechDeRhamTotalCocyclesOne.conn cz φ, hgT]
      simp only [map_add, map_sub]
      abel
    have hθc : (⟨θ, hθ⟩ : Glob1 F) ∈ Closed1 F := hc ▸ Submodule.mem_top
    funext T
    have hθ0 : dOne R _ (e.2 T - (cz.1.2 T - D R _ (g T))) = 0 := hθc T
    rw [map_sub, map_sub, cechDeRhamTotalCocyclesOne.closed cz T, dOne_D, sub_zero, sub_zero] at hθ0
    rw [← hη T, hθ0]; rfl
  · intro hw
    refine ⟨0, ?_⟩
    rw [map_zero]
    refine Tot2.ext (fun T T' T'' φ ψ ↦ (h1 T T' T'' φ ψ).symm) (fun T T' φ ↦ (h2 T T' φ).symm)
      fun T ↦ ?_
    rw [hval, hw]; rfl

end GlobalTheory.AbCoh
