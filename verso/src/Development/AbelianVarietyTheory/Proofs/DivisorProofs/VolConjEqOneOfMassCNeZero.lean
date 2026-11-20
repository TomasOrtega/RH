import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassMapConjStatement

open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

/- English proof (translation)
Establish `hC' : C.map (MulAut.conj t).toMonoidHom ≤ T`. Introduce and unpack `x ⟨c, hc, rfl⟩`. Establish `hcT` using `hC hc`. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Conclude with `T.mul_mem (T.mul_mem ht hcT) (T.inv_mem ht)`.

Establish `hchange` using `GlobalTheory.T.mass_mul_volume_commensurable Γ' T C (C.map (MulAut.conj t).toMonoidHom) hC hC' h1 h2 hf hf'`. Rewrite `hchange` using `[GlobalTheory.T.twistedCentralizerMass_map_conj Γ' T C t ht hC]`. Use `mul_left_cancel₀ hm (hchange.trans (mul_one _).symm)` as an intermediate fact. Conclude with `this`.
-/
theorem vol_conj_eq_one_of_massC_ne_zero {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G) (ht : t ∈ T)
    (hC : C ≤ T) (h1 : C.relIndex (C.map (MulAut.conj t).toMonoidHom) ≠ 0)
    (h2 : (C.map (MulAut.conj t).toMonoidHom).relIndex C ≠ 0)
    (hf : ∀ s ∈ T, ((Γ' ⊓ C.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G).Finite)
    (hf' : ∀ s ∈ T, ((Γ' ⊓ (C.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom :
      Subgroup G) : Set G).Finite)
    (hm : massC Γ' T C ≠ 0) :
    vol C (C.map (MulAut.conj t).toMonoidHom) = 1 := by
  have hC' : C.map (MulAut.conj t).toMonoidHom ≤ T := by
    rintro x ⟨c, hc, rfl⟩
    have hcT := hC hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact T.mul_mem (T.mul_mem ht hcT) (T.inv_mem ht)
  have hchange := GlobalTheory.T.mass_mul_volume_commensurable Γ' T C (C.map (MulAut.conj t).toMonoidHom) hC hC' h1 h2 hf hf'
  rw [GlobalTheory.T.twistedCentralizerMass_map_conj Γ' T C t ht hC] at hchange
  have := mul_left_cancel₀ hm (hchange.trans (mul_one _).symm)
  exact this

end GlobalTheory.LKCount
