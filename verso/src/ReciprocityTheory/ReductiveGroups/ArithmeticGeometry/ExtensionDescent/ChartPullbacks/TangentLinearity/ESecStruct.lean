import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.CompBaseEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ResEqOfResEq

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

/- English proof (translation)
Establish `key : eSec H ≫ H.hom = 𝟙 _` using `by first`. Consider the case `simp [eSec]`. Consider the case `(have h := Over.w (η[H]); simpa [eSec] using h)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma eSec_struct {S : Scheme.{0}} (H : Over S) [GrpObj H] (κ : Γ((𝟙_ (Over S)).left, ⊤)) :
    (eSec H).appTop.hom (H.hom.appTop.hom κ) = κ := by

  have key : eSec H ≫ H.hom = 𝟙 _ := by
    first
    | simp [eSec]
    | (have h := Over.w (η[H]); simpa [eSec] using h)
  calc (eSec H).appTop.hom (H.hom.appTop.hom κ)
      = (eSec H ≫ H.hom).appTop.hom κ := by first | rfl | simp
    _ = κ := by rw [key]; simp

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `R _ _ I O _ _ D _ A G _ _ U ιD ιA ιG hlin e a u hu hu0 χ`. Establish `hO` using `hlin.q_lin e`. Establish `hi` using `hlin.i_lin e a`. Take `⟨ρ, hρ⟩` from `pair U ιD ιG e a χ hO u hu`. Establish `hinv` using `rho_inv U ιD ιG e a χ hO u hi ρ hρ`.

Take `⟨v, hv⟩` from `descend (U.gt e) ρ.val hinv`. Take `⟨κ, hκ⟩` from `const_pullback hGF (thick R I e) D.toPre.P.A D.toPre.P.isAb v`. Establish `hq : (U.gt e).q.left ≫ (thickObj R I e D.toPre.P.A).hom = (thickObj R I e G).hom` using `Over.w (U.gt e).q`. Establish `hρκ : ρ.val = (thickObj R I e G).hom.appTop.hom κ`. Rewrite using `[← hv, ← hκ]`.

Use `congrArg (fun φ : (thickObj R I e G).left ⟶ _ => φ.appTop.hom κ) hq` as an intermediate fact. Rewrite `this` using `[Scheme.Hom.comp_appTop]`. Conclude with `this`. Establish `he` using `rho_e U ιD ιG e a χ hO u hGF hu hu0 ρ hρ`. Establish `hκ1 : κ = 1`.

Rewrite `he` using `[hρκ, eSec_struct]`. Conclude with `he`. Establish `hρ1 : ρ = 1` using `Units.ext (by rw [hρκ, hκ1, map_one]; rfl)`. Introduce `j j' cj cj' cjj'`. Establish `h1` using `hρ j j' cj cj' (fun k k' h => (cjj' k' k h.symm).symm)`.

Rewrite `h1` using `[hρ1, map_one]`. Establish `h1'` using `h1.trans (_root_.one_mul _)`. Establish `h2` using `congrArg (res (le_of_eq (inf_comm _ _) : LB.wchart D.toPre.P.L (φA U ιD e a χ) j ⊓ LB.wchart D.toPre.P.L (φB U ιG e a χ) j' ≤ LB.wchart D.toPre.P.L (φB U ιG e a χ) j' ⊓ LB.wchart D.toPre.P.L (φA U ιD e a χ) j)) h1'`. Conclude with `(Canon.res_res' _ _ _).symm.trans (h2.trans (Canon.res_res' _ _ _))`.
-/
theorem tLin_of (hGF : GlobalFnsSt) : TLinSt := by
  intro R _ _ I O _ _ D _ A G _ _ U ιD ιA ιG hlin e a u hu hu0 χ
  have hO := hlin.q_lin e
  have hi := hlin.i_lin e a
  obtain ⟨ρ, hρ⟩ := pair U ιD ιG e a χ hO u hu
  have hinv := rho_inv U ιD ιG e a χ hO u hi ρ hρ
  obtain ⟨v, hv⟩ := descend (U.gt e) ρ.val hinv
  obtain ⟨κ, hκ⟩ := const_pullback hGF (thick R I e) D.toPre.P.A D.toPre.P.isAb v
  have hq : (U.gt e).q.left ≫ (thickObj R I e D.toPre.P.A).hom = (thickObj R I e G).hom :=
    Over.w (U.gt e).q
  have hρκ : ρ.val = (thickObj R I e G).hom.appTop.hom κ := by
    rw [← hv, ← hκ]
    have := congrArg (fun φ : (thickObj R I e G).left ⟶ _ => φ.appTop.hom κ) hq
    rw [Scheme.Hom.comp_appTop] at this
    exact this
  have he := rho_e U ιD ιG e a χ hO u hGF hu hu0 ρ hρ
  have hκ1 : κ = 1 := by
    rw [hρκ, eSec_struct] at he
    exact he
  have hρ1 : ρ = 1 := Units.ext (by rw [hρκ, hκ1, map_one]; rfl)
  intro j j' cj cj' cjj'
  have h1 := hρ j j' cj cj' (fun k k' h => (cjj' k' k h.symm).symm)
  rw [hρ1, map_one] at h1
  have h1' := h1.trans (_root_.one_mul _)
  have h2 := congrArg (res (le_of_eq (inf_comm _ _) : LB.wchart D.toPre.P.L (φA U ιD e a χ) j ⊓
      LB.wchart D.toPre.P.L (φB U ιG e a χ) j' ≤
      LB.wchart D.toPre.P.L (φB U ιG e a χ) j' ⊓ LB.wchart D.toPre.P.L (φA U ιD e a χ) j)) h1'
  exact (Canon.res_res' _ _ _).symm.trans (h2.trans (Canon.res_res' _ _ _))

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
