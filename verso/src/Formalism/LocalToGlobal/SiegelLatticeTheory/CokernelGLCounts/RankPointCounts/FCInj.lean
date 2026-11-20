import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SecondValueMul

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
  (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (g : UP p)

/- English proof (translation)
Introduce `X Y hXY`. Proceed by induction on `X using Quotient.inductionOn with`. Consider the case `h x`. Proceed by induction on `Y using Quotient.inductionOn with`. Consider the case `h y`.

Apply `Quotient.sound` to reduce the goal to its premises. Take `⟨⟨l, hl, e1⟩, ⟨ρ, hρ, e2⟩⟩` from `Quotient.exact hXY`. Establish `e1' : (((y : UP p) : GG p).1 : GLp p).val = l * (((x : UP p) : GG p).1 : GLp p).val` using `e1`. Establish `e2' : ((((y : UP p) : GG p).2.unop : GLp p)).val = ((((x : UP p) : GG p).2.unop : GLp p)).val * ρ` using `e2`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show Formalism.MainNotions.S.TieN.IntLow (M p) ((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).1 : GLp p).val`. Rewrite using `[first_value_mul]`. Establish `: (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val * (((x : UP p) : GG p).1 : GLp p).val = 1`. Rewrite using `[← first_value_mul, inv_mul_cancel]`. Both sides reduce to the same expression.

Rewrite using `[e1', Matrix.mul_assoc]`. Rewrite using `[show (((x : UP p) : GG p).1 : GLp p).val * (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val = 1 by`. Rewrite using `[← first_value_mul, mul_inv_cancel]`. Use the proof step `rfl, Matrix.mul_one]`. Conclude with `hl`.

Use `show Formalism.MainNotions.S.TieN.IntUp (M p) (((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p)).val`. Rewrite using `[second_value_mul, e2', ← Matrix.mul_assoc]`. Rewrite using `[show ((((((x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p))).val * ((((x : UP p) : GG p).2.unop : GLp p)).val = 1 by rw [← second_value_mul, mul_inv_cancel]; rfl, Matrix.one_mul]`. Conclude with `hρ`. Use `show (y : UP p) * (x : UP p)⁻¹ ∈ πa.ker`.

Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 x.2.1, MonoidHom.mem_ker.1 y.2.1, inv_one, mul_one]`.
-/
theorem fC_inj : Function.Injective (fC M a πa hker g) := by
  intro X Y hXY
  induction X using Quotient.inductionOn with
  | h x =>
    induction Y using Quotient.inductionOn with
    | h y =>
      apply Quotient.sound
      obtain ⟨⟨l, hl, e1⟩, ⟨ρ, hρ, e2⟩⟩ := Quotient.exact hXY
      have e1' : (((y : UP p) : GG p).1 : GLp p).val = l * (((x : UP p) : GG p).1 : GLp p).val := e1
      have e2' : ((((y : UP p) : GG p).2.unop : GLp p)).val = ((((x : UP p) : GG p).2.unop : GLp p)).val * ρ := e2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show Formalism.MainNotions.S.TieN.IntLow (M p) ((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).1 : GLp p).val
        rw [first_value_mul]
        have : (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val * (((x : UP p) : GG p).1 : GLp p).val = 1 := by
          rw [← first_value_mul, inv_mul_cancel]; rfl
        rw [e1', Matrix.mul_assoc]
        rw [show (((x : UP p) : GG p).1 : GLp p).val * (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val = 1 by
          rw [← first_value_mul, mul_inv_cancel]; rfl, Matrix.mul_one]
        exact hl
      · show Formalism.MainNotions.S.TieN.IntUp (M p) (((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p)).val
        rw [second_value_mul, e2', ← Matrix.mul_assoc]
        rw [show ((((((x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p))).val *
            ((((x : UP p) : GG p).2.unop : GLp p)).val = 1 by rw [← second_value_mul, mul_inv_cancel]; rfl, Matrix.one_mul]
        exact hρ
      · show (y : UP p) * (x : UP p)⁻¹ ∈ πa.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 x.2.1, MonoidHom.mem_ker.1 y.2.1, inv_one,
          mul_one]

end Formalism.L2.SG.Pf.CountAt
