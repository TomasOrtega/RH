import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExistsSqEqIntCast
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.AlgebraMapFinite

noncomputable section

namespace Formalism.L2.G

open QuadraticAlgebra Formalism.BasicNotions.Examples₂ Formalism.MainNotions.G

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

abbrev QQ : Type := FractionRing (WQ p n)

abbrev OO : Type := QuadraticAlgebra (W2 p n) (p : W2 p n) 0

instance instDomOO : IsDomain (OO p n) := GatR.isDomain (WittVector.irreducible p)

instance instDvrOO : IsDiscreteValuationRing (OO p n) := GatR.isDVR (WittVector.irreducible p)

abbrev KO : Type := FractionRing (OO p n)

def wU : OO p n := ω

def jO : WQ p n →+* OO p n := (algebraMap (W2 p n) (OO p n)).comp (jW p n)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jO_injective : Function.Injective (jO p n) :=
  (Quad.algebraMap_injective _).comp (jW_injective p n)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inj_WK : Function.Injective ((algebraMap (OO p n) (KO p n)).comp (jO p n)) :=
  (IsFractionRing.injective (OO p n) (KO p n)).comp (jO_injective p n)

def iota : QQ p n →+* KO p n := IsFractionRing.lift (inj_WK p n)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem wU_sq : wU p n ^ 2 = (p : OO p n) := by
  unfold wU
  rw [GatR.om_sq, map_natCast]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem sq_OO [NeZero n] (hp2 : p ≠ 2) (z : ℤ) : ∃ y : OO p n, y ^ 2 = (z : OO p n) := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hfin : FiniteMultiplicity (p : ℤ) z :=
    Int.finiteMultiplicity_iff.2 ⟨by simpa using hp.out.one_lt.ne', hz⟩
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨y, hy⟩ := exists_sq_eq_intCast_of_not_dvd_of_ne_two p n hp2 c hpc
  refine ⟨wU p n ^ multiplicity (p : ℤ) z * algebraMap (W2 p n) (OO p n) y, ?_⟩
  rw [mul_pow, ← pow_mul, mul_comm _ 2, pow_mul, wU_sq, ← map_pow, hy, map_intCast]
  conv_rhs => rw [hc]
  push_cast
  rfl

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem settingStd (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    UnramifiedQuadraticSetting p n (WQ p n) (QQ p n) (OO p n) (KO p n) (iota p n) (sig p n) (jO p n) (wU p n) := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨?_, GatR.om_irreducible (WittVector.irreducible p), ?_, sq_OO p n (by omega)⟩
  · exact
    { prime := hp.out
      five_le := h5
      two_le := h2
      even := he
      frac_alt := inferInstance
      frac_O := inferInstance
      p_unif := WittVector.irreducible p
      res_card := card_quot_WQ p n
      eq_sum_herm_smul_frame_of_inW := inferInstance
      frob := fun x => by
        obtain ⟨y, hy⟩ := frob_WQ p n x
        exact ⟨y, by rw [sig_alg, hy]⟩
      period := sig_period p n
      ι_comp := fun x => IsFractionRing.lift_algebraMap (inj_WK p n) x
      finite := (Quad.algebraMap_finite _).comp (jW_finite p n)
      complete_O := GatR.isAdicComplete (WittVector.irreducible p) inferInstance
      w_sq := wU_sq p n }
  · exact (Quad.card_res _).trans (card_quotient_extRing p n)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem setting (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    HidaSetting p n (WQ p n) (QQ p n) (OO p n) (KO p n) (iota p n) (sig p n) (jO p n) (wU p n) :=
  (settingStd p n h5 h2 he).1

end Formalism.L2.G
