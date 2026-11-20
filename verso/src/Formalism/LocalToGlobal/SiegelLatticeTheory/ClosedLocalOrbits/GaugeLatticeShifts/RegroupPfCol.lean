import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RegroupPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ColUniqPf

/- English proof (translation)
Introduce `ρ ρ₁ ρ₂ γ₁ γ₂ h₁ h₂ hs`. Establish `hB : ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') ∈ X.K2`. Establish `e : ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') = (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ₁ : X.B.I.Gf) γ₁)⁻¹ * kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ₂ : X.B.I.Gf) γ₂`. Simplify using `only [kOf, Prod.snd_mul, Prod.snd_inv]`. Use `group`.

Rewrite using `[e]`. Conclude with `hK.2.1 _ (hK.2.2.1 _ h₁.2) _ h₂.2`. Take `⟨hsI, hsf⟩` from `Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' _ hs`. Take `⟨ν, η, hνη, -, -, hνf, hη⟩` from `Formalism.L2.SG.Pf.ratLevi_holds X u' _ (Subgroup.mem_inf.1 hs).1 hsI hsf`. Establish `hs2 : (γ₁⁻¹ * γ₂).2 = ν.2 * η.2` using `by rw [hνη, Prod.snd_mul]`.

Establish `hio : ((iotaF X u' ⟨η, hη⟩ : Hfin X u') : X.B.I.Gf) = η.2` using `rfl`. Establish `hn` using `((Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X u') (cs'.h ρ₁)⁻¹ ν.2 hνf).1`. Establish `hlev` using `Formalism.L2.SG.Pf.levelDec_holds X u' _ hn ((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂) (by`. Establish `e : (X.xu u')⁻¹ * ((((cs'.h ρ₁)⁻¹ : Hfin X u') : X.B.I.Gf) * ν.2 * (((cs'.h ρ₁)⁻¹ : Hfin X u') : X.B.I.Gf)⁻¹ * (((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂ : Hfin X u') : X.B.I.Gf)) * X.xu u' = ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu …`. Rewrite using `[hs2]`.

Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, hio]`. Use `group`. Rewrite using `[e]`. Conclude with `hB)`. Take `⟨ρ0, -, huniq⟩` from `hR (cs'.h ρ₂)`.

Establish `e1` using `huniq ρ₂ ⟨1, 1, by simp⟩`. Establish `e2` using `huniq ρ₁ ⟨(⟨η, hη⟩ : Gam X u')⁻¹, ⟨(cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂, hlev.1⟩, by show cs'.h ρ₂ = iotaF X u' (⟨η, hη⟩ : Gam X u')⁻¹ * cs'.h ρ₁ * ((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂)`. Rewrite using `[map_inv]`. Use the proof step `group⟩`. Conclude with `e2.trans e1.symm`.
-/
theorem colUniq_of {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')
    (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs') : ColUniq cs cs' := by
  intro ρ ρ₁ ρ₂ γ₁ γ₂ h₁ h₂ hs
  have hB : ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') ∈ X.K2 := by
    have e : ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') =
        (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ₁ : X.B.I.Gf) γ₁)⁻¹ *
          kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ₂ : X.B.I.Gf) γ₂ := by
      simp only [kOf, Prod.snd_mul, Prod.snd_inv]
      group
    rw [e]
    exact hK.2.1 _ (hK.2.2.1 _ h₁.2) _ h₂.2
  obtain ⟨hsI, hsf⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' _ hs
  obtain ⟨ν, η, hνη, -, -, hνf, hη⟩ :=
    Formalism.L2.SG.Pf.ratLevi_holds X u' _ (Subgroup.mem_inf.1 hs).1 hsI hsf
  have hs2 : (γ₁⁻¹ * γ₂).2 = ν.2 * η.2 := by rw [hνη, Prod.snd_mul]
  have hio : ((iotaF X u' ⟨η, hη⟩ : Hfin X u') : X.B.I.Gf) = η.2 := rfl
  have hn := ((Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X u') (cs'.h ρ₁)⁻¹ ν.2 hνf).1
  have hlev := Formalism.L2.SG.Pf.levelDec_holds X u' _ hn
    ((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂) (by
      have e : (X.xu u')⁻¹ * ((((cs'.h ρ₁)⁻¹ : Hfin X u') : X.B.I.Gf) * ν.2 *
          (((cs'.h ρ₁)⁻¹ : Hfin X u') : X.B.I.Gf)⁻¹ *
          (((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂ : Hfin X u') : X.B.I.Gf)) * X.xu u' =
          ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') := by
        rw [hs2]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hio]
        group
      rw [e]
      exact hB)
  obtain ⟨ρ0, -, huniq⟩ := hR (cs'.h ρ₂)
  have e1 := huniq ρ₂ ⟨1, 1, by simp⟩
  have e2 := huniq ρ₁ ⟨(⟨η, hη⟩ : Gam X u')⁻¹,
    ⟨(cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂, hlev.1⟩, by
      show cs'.h ρ₂ = iotaF X u' (⟨η, hη⟩ : Gam X u')⁻¹ * cs'.h ρ₁ *
        ((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂)
      rw [map_inv]
      group⟩
  exact e2.trans e1.symm

end ColUniqPf

/- English proof (translation)
Introduce `D X Y u u' _`. Conclude with `ColUniqPf.colUniq_of (Y.cs u) (Y.cs u') Y.hK (Y.colReps u')`.
-/
theorem column_uniqueness : ColUniqC := by
  intro D X Y u u' _
  exact ColUniqPf.colUniq_of (Y.cs u) (Y.cs u') Y.hK (Y.colReps u')

end Formalism.L2.SG.Pf.RegroupPf
