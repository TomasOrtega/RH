import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClsCrdEqGlob
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassInjectiveOfSelfDual

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `c γ hγ v x hx`. Establish `hF` using `Tf.fv D.R.m le_rfl (Or.inr rfl)`. Establish `hγ'` using `((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI_range _ γ).1 hγ`. Take `⟨κ, hκ, hκe⟩` from `Subgroup.mem_map.mp hγ'`. Establish `hbc : bc (inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 * κ * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1⁻¹ := by`.

Rewrite using `[← hκe]`. Both sides reduce to the same expression. Establish `hκv` using `((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U_eq κ).1 hκ |>.2 (Tf.atT.eV v).1`. Rewrite `hκv` using `[(Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.UlocAlt (Tf.atT.eV v).1 (Tf.atT.eV v).2]`. Take `⟨_, hfix⟩` from `(Subgroup.mem_inf.mp hκv).2`.

Establish `hzx` using `dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) x.1 x.2`. Establish `hzg` using `dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) _ hx`. Establish `key` using `conj_stepA (Tf.atT.eV v).1 _ κ γ.1 hbc x.1`. Conclude with `(hF v ((D.fm u).til c) ⟨_, hx⟩ hzg).trans ((congrArg _ ((congrArg _ (Subtype.ext key)).trans (hfix ⟨_, hzx⟩))).trans (hF v ((D.fm u).til c) x hzx).symm)`.
-/
theorem fvStab_holds {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : FormsTiedSym D u Ch chOf) : FvStab Tf := by
  intro c γ hγ v x hx
  have hF := Tf.fv D.R.m le_rfl (Or.inr rfl)
  have hγ' := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI_range _ γ).1 hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ'
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 =
      ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 * κ *
        ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1⁻¹ := by
    rw [← hκe]; rfl
  have hκv := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U_eq κ).1 hκ |>.2 (Tf.atT.eV v).1
  rw [(Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.UlocAlt (Tf.atT.eV v).1 (Tf.atT.eV v).2] at hκv
  obtain ⟨_, hfix⟩ := (Subgroup.mem_inf.mp hκv).2
  have hzx := dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) x.1 x.2
  have hzg := dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) _ hx
  have key := conj_stepA (Tf.atT.eV v).1 _ κ γ.1 hbc x.1
  exact (hF v ((D.fm u).til c) ⟨_, hx⟩ hzg).trans ((congrArg _ ((congrArg _ (Subtype.ext key)).trans (hfix ⟨_, hzx⟩))).trans
    (hF v ((D.fm u).til c) x hzx).symm)

/- English proof (translation)
The claim follows from `class_injective_of_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf)`.
-/
theorem class_injective_holds : ClassMapInjective :=
  class_injective_of_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf)

/- English proof (translation)
The claim follows from `stabiliser_bijective_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf) (fun _ _ _ _ Tf => fvStab_holds Tf)`.
-/
theorem stabiliser_bijective_holds : StabiliserMapBijective :=
  stabiliser_bijective_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf) (fun _ _ _ _ Tf => fvStab_holds Tf)

end Formalism.L2.GlobalTheoryTheory.Br
