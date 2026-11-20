import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerOneFormEqZeroOfUniformisedValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegOfPeriodicOfIsRegSubStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedOfLocallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
open Opposite GlobalTheory.CatCoh

namespace GlobalTheory.CechPer

/- English proof (translation)
Introduce `A _ g L u hA x hx`. Take `⟨c, h, rfl, ⟨hd, hc, hω⟩, hp⟩` from `hx`. Take `⟨hopen, -, -, -, -, hmono, -, hloc, hres, halg, -, -⟩` from `GlobalTheory.CechPer.pre_val_rules A g L u`. Establish `vsub : ∀ (U : A.left.Opens) (a b : Sec (str A) U), ∀ z ∈ pre u.ex U, val u.ex U (a - b : Sec (str A) U) z = val u.ex U a z - val u.ex U b z`. Introduce `U a b z hz`.

Take `⟨e, he⟩` from `halg U z hz`. Conclude with `(he (a - b : Sec (str A) U)).trans ((map_sub e a b).trans (congrArg₂ (· - ·) (he a).symm (he b).symm))`. Establish `hreg : ∀ U V : A.left.affineOpens, IsReg u.ex (U.1 ⊓ V.1) (h U - h V)`. Introduce `U V`. Apply `GlobalTheory.T.isRegularOnOpenUniformised_of_locally A g L u hA` to reduce the goal to its premises.

Introduce `z hz`. Take `⟨W, hW, hzW⟩` from `hloc _ z hz`. Establish `hWU : W ≤ U` using `(le_inf_iff.1 hW).1`. Establish `hWV : W ≤ V` using `(le_inf_iff.1 hW).2`. Use `⟨W.1, hW, hzW, (c.1.1 (op V) (op W) (homOfLE hWV).op - c.1.1 (op U) (op W) (homOfLE hWU).op : Sec (str A) W.1), fun y hy ↦ ?_⟩` and prove the remaining obligations.

Establish `e0` using `vsub W.1 (c.1.1 (op V) (op W) (homOfLE hWV).op) (c.1.1 (op U) (op W) (homOfLE hWU).op) y hy`. Establish `e1` using `hc U W (homOfLE hWU).op y hy`. Establish `e2` using `hc V W (homOfLE hWV).op y hy`. Use `Eq.trans ?_ e0.symm` and prove the remaining obligations. Rewrite using `[Pi.sub_apply]`.

Take the linear combination `e2 - e1`. Establish `hb` using `GlobalTheory.T.isReg_of_periodic_of_isReg_sub' A g L u hA A.left.affineOpens (fun U ↦ U.1) h (iSup_affineOpens_eq_top A.left) hd (fun U l z hz ↦ by simpa using hp U l z hz) hreg`. Use `choose b hb using hb`. Set `b' : ∀ U : A.left.affineOpens, Sec (str A) U.1` to `b`. Use `(Hyp1.mk_eq_zero (F := OAff (str A))).2 ⟨fun T ↦ b' T.unop, Tot1.ext (fun T T' a ↦ ?_) (fun T ↦ ?_)⟩` and prove the remaining obligations.

Take `⟨U⟩` from `T`. Take `⟨V⟩` from `T'`. Establish `hVU : V.1 ≤ U.1` using `leOfHom a.unop`. Establish `hz0` using `GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA V.1 ((b' V - Sec.res (str A) hVU (b' U) - c.1.1 (op U) (op V) a : Sec (str A) V.1)) (fun z hz ↦ by`. Establish `e0` using `vsub V.1 (b' V - Sec.res (str A) hVU (b' U)) (c.1.1 (op U) (op V) a) z hz`.

Establish `e1` using `vsub V.1 (b' V) (Sec.res (str A) hVU (b' U)) z hz`. Establish `e2` using `hres U.1 V.1 hVU (b' U) z hz`. Establish `e3 : h V z = val u.ex V.1 (b' V) z` using `hb V z hz`. Establish `e4 : h U z = val u.ex U.1 (b' U) z` using `hb U z (hmono _ _ hVU hz)`. Establish `e5` using `hc U V a z hz`.

Use `e0.trans ?_` and prove the remaining obligations. Take the linear combination `e1 - e2 - e3 + e4 + e5)`. Conclude with `sub_eq_zero.1 (show (b' V - Sec.res (str A) hVU (b' U) - c.1.1 (op U) (op V) a : Sec (str A) V.1) = 0 from hz0)`. Take `⟨U⟩` from `T`. Express the relevant statement in the definitionally equal form `KaehlerDifferential.D ℂ (Sec (str A) U.1) (b' U) = c.1.2 (op U)`.

Apply `sub_eq_zero.1` to reduce the goal to its premises. Apply `GlobalTheory.T.kaehlerOneForm_eq_zero_of_uniformised_values A g L u hA U` to reduce the goal to its premises. Introduce `z hz`. Rewrite using `[map_sub, (GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hz).2.2 (b' U), ← hω U z hz, sub_eq_zero]`. Use `(Filter.EventuallyEq.fderiv_eq ?_).symm` and prove the remaining obligations.

Use `filter_upwards [(hopen U.1).mem_nhds hz] with y hy`. Conclude with `hb U y hy`.
-/
theorem eq_zero_of_isPer_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ x, IsPer u.ex u.Λ x 0 → x = 0 := by
  intro A _ g L u hA x hx
  obtain ⟨c, h, rfl, ⟨hd, hc, hω⟩, hp⟩ := hx
  obtain ⟨hopen, -, -, -, -, hmono, -, hloc, hres, halg, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  have vsub : ∀ (U : A.left.Opens) (a b : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (a - b : Sec (str A) U) z = val u.ex U a z - val u.ex U b z := by
    intro U a b z hz
    obtain ⟨e, he⟩ := halg U z hz
    exact (he (a - b : Sec (str A) U)).trans ((map_sub e a b).trans (congrArg₂ (· - ·) (he a).symm (he b).symm))
  have hreg : ∀ U V : A.left.affineOpens, IsReg u.ex (U.1 ⊓ V.1) (h U - h V) := by
    intro U V
    apply GlobalTheory.T.isRegularOnOpenUniformised_of_locally A g L u hA
    intro z hz
    obtain ⟨W, hW, hzW⟩ := hloc _ z hz
    have hWU : W ≤ U := (le_inf_iff.1 hW).1
    have hWV : W ≤ V := (le_inf_iff.1 hW).2
    refine ⟨W.1, hW, hzW, (c.1.1 (op V) (op W) (homOfLE hWV).op - c.1.1 (op U) (op W) (homOfLE hWU).op :
      Sec (str A) W.1), fun y hy ↦ ?_⟩
    have e0 := vsub W.1 (c.1.1 (op V) (op W) (homOfLE hWV).op) (c.1.1 (op U) (op W) (homOfLE hWU).op) y hy
    have e1 := hc U W (homOfLE hWU).op y hy
    have e2 := hc V W (homOfLE hWV).op y hy
    refine Eq.trans ?_ e0.symm
    rw [Pi.sub_apply]
    linear_combination e2 - e1
  have hb := GlobalTheory.T.isReg_of_periodic_of_isReg_sub' A g L u hA A.left.affineOpens (fun U ↦ U.1) h
    (iSup_affineOpens_eq_top A.left) hd (fun U l z hz ↦ by simpa using hp U l z hz) hreg
  choose b hb using hb
  let b' : ∀ U : A.left.affineOpens, Sec (str A) U.1 := b
  refine (Hyp1.mk_eq_zero (F := OAff (str A))).2 ⟨fun T ↦ b' T.unop, Tot1.ext (fun T T' a ↦ ?_) (fun T ↦ ?_)⟩
  · obtain ⟨U⟩ := T
    obtain ⟨V⟩ := T'
    have hVU : V.1 ≤ U.1 := leOfHom a.unop
    have hz0 := GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA V.1
      ((b' V - Sec.res (str A) hVU (b' U) - c.1.1 (op U) (op V) a : Sec (str A) V.1)) (fun z hz ↦ by
        have e0 := vsub V.1 (b' V - Sec.res (str A) hVU (b' U)) (c.1.1 (op U) (op V) a) z hz
        have e1 := vsub V.1 (b' V) (Sec.res (str A) hVU (b' U)) z hz
        have e2 := hres U.1 V.1 hVU (b' U) z hz
        have e3 : h V z = val u.ex V.1 (b' V) z := hb V z hz
        have e4 : h U z = val u.ex U.1 (b' U) z := hb U z (hmono _ _ hVU hz)
        have e5 := hc U V a z hz
        refine e0.trans ?_
        linear_combination e1 - e2 - e3 + e4 + e5)
    exact sub_eq_zero.1 (show (b' V - Sec.res (str A) hVU (b' U) - c.1.1 (op U) (op V) a : Sec (str A) V.1) = 0 from hz0)
  · obtain ⟨U⟩ := T
    change KaehlerDifferential.D ℂ (Sec (str A) U.1) (b' U) = c.1.2 (op U)
    apply sub_eq_zero.1
    apply GlobalTheory.T.kaehlerOneForm_eq_zero_of_uniformised_values A g L u hA U
    intro z hz
    rw [map_sub, (GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hz).2.2 (b' U), ← hω U z hz, sub_eq_zero]
    refine (Filter.EventuallyEq.fderiv_eq ?_).symm
    filter_upwards [(hopen U.1).mem_nhds hz] with y hy
    exact hb U y hy

end GlobalTheory.CechPer
