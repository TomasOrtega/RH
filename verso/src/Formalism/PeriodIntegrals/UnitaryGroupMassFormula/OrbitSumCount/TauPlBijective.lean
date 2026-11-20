import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow

noncomputable section

open scoped BigOperators
open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace SumOrbCW

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem iotaH_bijective (e : ℕ) : Function.Bijective (iotaH e) := by
  obtain ⟨-, hcard, hord, -⟩ := Formalism.TwoAdicCyclotomicDecomposition.quotCyclic e
  have : NeZero (2 ^ e) := ⟨by positivity⟩
  have hinj : Function.Injective (iotaH e) := by
    intro a b hab
    have ha : a.val < orderOf (hcl e (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2))) := by
      rw [show hcl e (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2)) = QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
        (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2)) from rfl, hord]; exact ZMod.val_lt a
    have hb : b.val < orderOf (hcl e (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2))) := by
      rw [show hcl e (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2)) = QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
        (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2)) from rfl, hord]; exact ZMod.val_lt b
    exact ZMod.val_injective _ (pow_injOn_Iio_orderOf ha hb hab)
  refine hinj.bijective_of_nat_card_le ?_
  rw [hcard, Nat.card_zmod]

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Substitute using the available equality. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis.

Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem plGG_bijective (D : D7) :
    Function.Bijective (fun z : Bool × HH D => (⟨plGG D z, plGG_mem_Psi D z⟩ : D.R.Psi)) := by
  have hi := D.R.toFrame.iota_bijective
  constructor
  · rintro ⟨b, t⟩ ⟨b', t'⟩ h
    have h' := congrArg Subtype.val h
    cases b <;> cases b' <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h' <;> simp [hi.1 h']
  · rintro ⟨⟨⟨s, c⟩, h⟩, hg⟩
    have hc : c = 1 := hg
    subst hc
    obtain ⟨t, ht⟩ := hi.2 h
    rcases Int.units_eq_one_or s with hs | hs
    · exact ⟨(false, t), by subst hs; simp [plGG, Formalism.HC.Frame.tau1, ht]⟩
    · exact ⟨(true, t), by subst hs; simp [plGG, Formalism.HC.Frame.tau2, ht]⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tauPl_bijective (D : D7) : Function.Bijective (tauPl D) :=
  D.eTau.symm.bijective.comp (plGG_bijective D)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sum_wPl (D : D7) (j : ℕ) : (∑ z : Bool × HH D, wPl D j z) = ∑ τ : D.what₂.Tau, wj D j τ :=
  (tauPl_bijective D).sum_comp (wj D j)

end SumOrbCW

end
