import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq

noncomputable section

namespace GlobalTheory.BeCoefficients

open Formalism.MainNotions.FormalGroupSystem
open Formalism.MainNotions.GL3Theta (G1 ModelOverW)
open Formalism.L2.G.Pend (k0ToC)

/- English proof (translation)
Introduce `l _ g hOk hM hph`. Take `⟨P0, hP0⟩` from `(Formalism.L2.G.Pend.coefWf_iff _).1 hph`. Take `⟨E0, hE0⟩` from `(Formalism.L2.G.Pend.coefWf_iff _).1 (Formalism.L2.G.Pend.exRat_of g hOk hM)`. Take `⟨L0, hL0⟩` from `Formalism.L2.G.Pend.l_mem_ratSub g hOk.2.1 hM`. Establish `hP0' : PowerSeries.map (k0ToC l) P0 = g.ph` using `hP0`.

Establish `hE0' : PowerSeries.map (k0ToC l) E0 = g.ex` using `hE0`. Establish `hL0' : PowerSeries.map (k0ToC l) L0 = g.l` using `hL0`. Establish `hE00 : PowerSeries.constantCoeff E0 = 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Apply `(map_eq_zero_iff _ (k0ToC l).injective).1` to reduce the goal to its premises.

Rewrite using `[← PowerSeries.coeff_map, hE0', PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `hOk.2.2.1`. Establish `hL00 : PowerSeries.constantCoeff L0 = 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Apply `(map_eq_zero_iff _ (k0ToC l).injective).1` to reduce the goal to its premises.

Rewrite using `[← PowerSeries.coeff_map, hL0', PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `Formalism.MainNotions.J.cc_l g`. Establish `hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) = 0` using `fun i => MvPowerSeries.constantCoeff_X i`. Establish `hs0 : MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 + PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) = 0`. Rewrite using `[map_add, PowerSeries.constantCoeff_subst_eq_zero (hX 0) _ hL00, PowerSeries.constantCoeff_subst_eq_zero (hX 1) _ hL00, add_zero]`.

Establish `hs1 : MvPowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 + PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) E0) = 0` using `PowerSeries.constantCoeff_subst_eq_zero hs0 _ hE00`. Use `(Formalism.L2.G.Pend.coefWf_iff _).2 ⟨PowerSeries.subst (PowerSeries.subst (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 + PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) E0) P0 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSe …` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs1), PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 0)), PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 1)), PowerSeries.map_subst (PowerSeries.HasS …`. Both sides reduce to the same expression.
-/
theorem beCoef : Formalism.L2.KerInert.BeCob.BeCoef := by
  intro l _ g hOk hM hph
  obtain ⟨P0, hP0⟩ := (Formalism.L2.G.Pend.coefWf_iff _).1 hph
  obtain ⟨E0, hE0⟩ := (Formalism.L2.G.Pend.coefWf_iff _).1 (Formalism.L2.G.Pend.exRat_of g hOk hM)
  obtain ⟨L0, hL0⟩ := Formalism.L2.G.Pend.l_mem_ratSub g hOk.2.1 hM
  have hP0' : PowerSeries.map (k0ToC l) P0 = g.ph := hP0
  have hE0' : PowerSeries.map (k0ToC l) E0 = g.ex := hE0
  have hL0' : PowerSeries.map (k0ToC l) L0 = g.l := hL0
  have hE00 : PowerSeries.constantCoeff E0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply (map_eq_zero_iff _ (k0ToC l).injective).1
    rw [← PowerSeries.coeff_map, hE0', PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hOk.2.2.1
  have hL00 : PowerSeries.constantCoeff L0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply (map_eq_zero_iff _ (k0ToC l).injective).1
    rw [← PowerSeries.coeff_map, hL0', PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Formalism.MainNotions.J.cc_l g
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hs0 : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) = 0 := by
    rw [map_add, PowerSeries.constantCoeff_subst_eq_zero (hX 0) _ hL00,
      PowerSeries.constantCoeff_subst_eq_zero (hX 1) _ hL00, add_zero]
  have hs1 : MvPowerSeries.constantCoeff (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) E0) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hs0 _ hE00
  refine (Formalism.L2.G.Pend.coefWf_iff _).2 ⟨PowerSeries.subst (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) E0) P0 -
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) P0 -
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) P0, ?_⟩
  rw [map_sub, map_sub, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs1),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 0)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 1)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs0), map_add,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 0)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 1)),
    MvPowerSeries.map_X, MvPowerSeries.map_X, hP0', hE0', hL0']
  rfl

end GlobalTheory.BeCoefficients
