import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioMap

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

/- English proof (translation)
Introduce `i j` and use `⟨h.2.1 i j, fun e => e ▸ h.1 i⟩`.
-/
theorem loUni_of_int {l : MP p} (h : Formalism.MainNotions.S.TieN.IntLow (M p) l) : IsLoUni l :=
  fun i j => ⟨h.2.1 i j, fun e => e ▸ h.1 i⟩

/- English proof (translation)
Introduce `i j` and use `⟨h.2.1 i j, fun e => e ▸ h.1 i⟩`.
-/
theorem upUni_of_int {l : MP p} (h : Formalism.MainNotions.S.TieN.IntUp (M p) l) : IsUpUni l :=
  fun i j => ⟨h.2.1 i j, fun e => e ▸ h.1 i⟩

section
variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)

/- English proof (translation)
Simplify using `only [g0, Prod.fst_mul, Prod.fst_inv, Units.val_mul, Units.inv_mk]`.
-/
theorem conj_first_factor (x : GG p) :
    (((g0 M δ hA L U hL hU * x * (g0 M δ hA L U hL hU)⁻¹).1 : GLp p) : MP p) =
      lOf δ M p L U * ((x.1 : GLp p) : MP p) * lOf δ M p L⁻¹ U⁻¹ := by
  simp only [g0, Prod.fst_mul, Prod.fst_inv, Units.val_mul, Units.inv_mk]

/- English proof (translation)
Simplify using `only [g0, Prod.snd_mul, Prod.snd_inv, MulOpposite.unop_mul, MulOpposite.unop_inv, MulOpposite.unop_op, Units.val_mul, Units.inv_mk]`. Rewrite using `[Matrix.mul_assoc]`.
-/
theorem conj_second_factor (x : GG p) :
    ((((g0 M δ hA L U hL hU * x * (g0 M δ hA L U hL hU)⁻¹).2).unop : GLp p) : MP p) =
      ρOf δ M p L⁻¹ U⁻¹ * ((x.2.unop : GLp p) : MP p) * ρOf δ M p L U := by
  simp only [g0, Prod.snd_mul, Prod.snd_inv, MulOpposite.unop_mul, MulOpposite.unop_inv, MulOpposite.unop_op,
    Units.val_mul, Units.inv_mk]
  rw [Matrix.mul_assoc]

/- English proof (translation)
Establish `hLL : lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U = 1` using `lp_inv M δ hA L U hL hU`. Establish `hLL' : lOf δ M p L U * lOf δ M p L⁻¹ U⁻¹ = 1` using `(Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hLL`. Establish `hUU : ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹ = 1` using `up_inv M δ hA L U hL hU`. Establish `hUU' : ρOf δ M p L⁻¹ U⁻¹ * ρOf δ M p L U = 1` using `(Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hUU`. Use `set Lp := lOf δ M p L U`.

Use `set Lpi := lOf δ M p L⁻¹ U⁻¹`. Use `set Up := ρOf δ M p L U`. Use `set Upi := ρOf δ M p L⁻¹ U⁻¹`. Use `set Y := Y0 M δ u u' w p`. Establish `key : ∀ a b : MP p, (Lp * a * Lpi) * (Lp * Y * Up) * (Upi * b * Up) = Lp * (a * Y * b) * Up`.

Introduce `a b`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Lp * (a * Y * b) * Up := by rw [hLL, hUU]; simp only [Matrix.mul_one, Matrix.mul_assoc]`. Use extensionality with `x`.

Rewrite using `[mem_cj]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨hy1, hy2⟩` from `hy`. Take `⟨_, _, hy3⟩` from `y.2`.

Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show Formalism.MainNotions.S.TieN.IntLow (M p) _`. Rewrite using `[conj_first_factor]`. Conclude with `hy1`. Use `show Formalism.MainNotions.S.TieN.IntUp (M p) _`.

Rewrite using `[conj_second_factor]`. Conclude with `hy2`. Use `show _ * XP M δ u u' w L U * _ = XP M δ u u' w L U`. Rewrite using `[conj_first_factor, conj_second_factor]`. Use `show (Lp * _ * Lpi) * (Lp * Y * Up) * (Upi * _ * Up) = Lp * Y * Up`.

Rewrite using `[key]`. Conclude with `congrArg (fun z => Lp * z * Up) hy3`. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Establish `h1' : Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((x.1 : GLp p) : MP p) * Lpi)`. Use `h1` as an intermediate fact.

Rewrite `this` using `[show Formalism.MainNotions.S.TieN.IntLow (M p) _ = _ from rfl, conj_first_factor]`. Conclude with `this`. Establish `h2' : Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((x.2.unop : GLp p) : MP p) * Up)`. Use `h2` as an intermediate fact. Rewrite `this` using `[show Formalism.MainNotions.S.TieN.IntUp (M p) _ = _ from rfl, conj_second_factor]`.

Conclude with `this`. Establish `h3' : (Lp * ((x.1 : GLp p) : MP p) * Lpi) * (Lp * Y * Up) * (Upi * ((x.2.unop : GLp p) : MP p) * Up) = Lp * Y * Up`. Use `h3` as an intermediate fact. Express the relevant statement in the definitionally equal form `_ * XP M δ u u' w L U * _ = XP M δ u u' w L U at this`. Rewrite `this` using `[conj_first_factor, conj_second_factor]`.

Conclude with `this`. Rewrite `h3'` using `[key]`. Establish `hst : ((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p) = Y`. Use `congrArg (fun z => Lpi * z * Upi) h3'` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hLL, hUU, Matrix.one_mul, Matrix.mul_one]`. Use `_ = Lpi * (Lp * (((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)) * Up) * Upi := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Lpi * (Lp * Y * Up) * Upi := this`. Use `_ = Y := by`.

Combine the equalities or inequalities in the displayed calculation. Establish `hlo : IsLoUni ((x.1 : GLp p) : MP p)`. Establish `e : ((x.1 : GLp p) : MP p) = Lpi * (Lp * ((x.1 : GLp p) : MP p) * Lpi) * Lp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hLL, Matrix.one_mul, Matrix.mul_one]`.

Use `_ = Lpi * (Lp * ((x.1 : GLp p) : MP p) * Lpi) * Lp := by simp only [Matrix.mul_assoc]`. Rewrite using `[e]`. Conclude with `ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul (lOf_loUni M δ hA _ _ (ZsVolGrp.isLoUni_inv hL).1 (ZsVolGrp.isUpUni_inv hU).1) (loUni_of_int M h1')) (lOf_loUni M δ hA _ _ hL hU)`. Establish `hup : IsUpUni ((x.2.unop : GLp p) : MP p)`. Establish `e : ((x.2.unop : GLp p) : MP p) = Up * (Upi * ((x.2.unop : GLp p) : MP p) * Up) * Upi`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hUU, Matrix.one_mul, Matrix.mul_one]`. Use `_ = Up * (Upi * ((x.2.unop : GLp p) : MP p) * Up) * Upi := by simp only [Matrix.mul_assoc]`. Rewrite using `[e]`. Conclude with `ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul (ρOf_upUni M δ hA _ _ hL hU) (upUni_of_int M h2')) (ρOf_upUni M δ hA _ _ (ZsVolGrp.isLoUni_inv hL).1 (ZsVolGrp.isUpUni_inv hU).1)`.

Conclude with `⟨⟨x, hlo, hup, hst⟩, ⟨h1', h2'⟩, rfl⟩`.
-/
theorem cShape (w : Point D.host.E (D.R.rS + 1)) : CShapeAt M δ u u' w hA L U hL hU := by
  have hLL : lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U = 1 := lp_inv M δ hA L U hL hU
  have hLL' : lOf δ M p L U * lOf δ M p L⁻¹ U⁻¹ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hLL
  have hUU : ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹ = 1 := up_inv M δ hA L U hL hU
  have hUU' : ρOf δ M p L⁻¹ U⁻¹ * ρOf δ M p L U = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hUU
  set Lp := lOf δ M p L U
  set Lpi := lOf δ M p L⁻¹ U⁻¹
  set Up := ρOf δ M p L U
  set Upi := ρOf δ M p L⁻¹ U⁻¹
  set Y := Y0 M δ u u' w p
  have key : ∀ a b : MP p, (Lp * a * Lpi) * (Lp * Y * Up) * (Upi * b * Up) = Lp * (a * Y * b) * Up := by
    intro a b
    calc (Lp * a * Lpi) * (Lp * Y * Up) * (Upi * b * Up) = Lp * a * (Lpi * Lp) * Y * (Up * Upi) * b * Up := by
          simp only [Matrix.mul_assoc]
      _ = Lp * (a * Y * b) * Up := by rw [hLL, hUU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  ext x
  rw [mem_cj]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨_, _, hy3⟩ := y.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) _
      rw [conj_first_factor]; exact hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) _
      rw [conj_second_factor]; exact hy2
    · show _ * XP M δ u u' w L U * _ = XP M δ u u' w L U
      rw [conj_first_factor, conj_second_factor]
      show (Lp * _ * Lpi) * (Lp * Y * Up) * (Upi * _ * Up) = Lp * Y * Up
      rw [key]
      exact congrArg (fun z => Lp * z * Up) hy3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h1' : Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((x.1 : GLp p) : MP p) * Lpi) := by
      have := h1; rw [show Formalism.MainNotions.S.TieN.IntLow (M p) _ = _ from rfl, conj_first_factor] at this; exact this
    have h2' : Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((x.2.unop : GLp p) : MP p) * Up) := by
      have := h2; rw [show Formalism.MainNotions.S.TieN.IntUp (M p) _ = _ from rfl, conj_second_factor] at this; exact this
    have h3' : (Lp * ((x.1 : GLp p) : MP p) * Lpi) * (Lp * Y * Up) * (Upi * ((x.2.unop : GLp p) : MP p) * Up) =
        Lp * Y * Up := by
      have := h3
      change _ * XP M δ u u' w L U * _ = XP M δ u u' w L U at this
      rw [conj_first_factor, conj_second_factor] at this
      exact this
    rw [key] at h3'
    have hst : ((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p) = Y := by
      have := congrArg (fun z => Lpi * z * Upi) h3'
      calc ((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)
          = (Lpi * Lp) * (((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)) * (Up * Upi) := by
            rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
        _ = Lpi * (Lp * (((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)) * Up) * Upi := by
            simp only [Matrix.mul_assoc]
        _ = Lpi * (Lp * Y * Up) * Upi := this
        _ = Y := by
            calc Lpi * (Lp * Y * Up) * Upi = (Lpi * Lp) * Y * (Up * Upi) := by simp only [Matrix.mul_assoc]
              _ = Y := by rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
    have hlo : IsLoUni ((x.1 : GLp p) : MP p) := by
      have e : ((x.1 : GLp p) : MP p) = Lpi * (Lp * ((x.1 : GLp p) : MP p) * Lpi) * Lp := by
        calc ((x.1 : GLp p) : MP p) = (Lpi * Lp) * ((x.1 : GLp p) : MP p) * (Lpi * Lp) := by
              rw [hLL, Matrix.one_mul, Matrix.mul_one]
          _ = Lpi * (Lp * ((x.1 : GLp p) : MP p) * Lpi) * Lp := by simp only [Matrix.mul_assoc]
      rw [e]
      exact ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul
        (lOf_loUni M δ hA _ _ (ZsVolGrp.isLoUni_inv hL).1 (ZsVolGrp.isUpUni_inv hU).1) (loUni_of_int M h1'))
        (lOf_loUni M δ hA _ _ hL hU)
    have hup : IsUpUni ((x.2.unop : GLp p) : MP p) := by
      have e : ((x.2.unop : GLp p) : MP p) = Up * (Upi * ((x.2.unop : GLp p) : MP p) * Up) * Upi := by
        calc ((x.2.unop : GLp p) : MP p) = (Up * Upi) * ((x.2.unop : GLp p) : MP p) * (Up * Upi) := by
              rw [hUU, Matrix.one_mul, Matrix.mul_one]
          _ = Up * (Upi * ((x.2.unop : GLp p) : MP p) * Up) * Upi := by simp only [Matrix.mul_assoc]
      rw [e]
      exact ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul (ρOf_upUni M δ hA _ _ hL hU) (upUni_of_int M h2'))
        (ρOf_upUni M δ hA _ _ (ZsVolGrp.isLoUni_inv hL).1 (ZsVolGrp.isUpUni_inv hU).1)
    exact ⟨⟨x, hlo, hup, hst⟩, ⟨h1', h2'⟩, rfl⟩

end

end Formalism.L2.SG.Pf.ProdEP2Cut
