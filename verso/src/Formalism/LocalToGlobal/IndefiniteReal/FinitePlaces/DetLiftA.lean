import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ContinuousCoB

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Filter

namespace Formalism.IndefR.Fin.DL

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem pi_sign_unit {ι : Type*} {K : ι → Type*} [∀ i, Field (K i)] (h2 : ∀ i, (2 : K i) ≠ 0)
    (a : ∀ i, K i) : ∃ s : ∀ i, K i, s * s = 1 ∧ IsUnit (a + s) := by
  classical
  refine ⟨fun i => if a i + 1 = 0 then -1 else 1, ?_, ?_⟩
  · funext i
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp
  · refine Pi.isUnit_iff.2 fun i => isUnit_iff_ne_zero.2 ?_
    simp only [Pi.add_apply]
    split_ifs with h
    · intro h'
      apply h2 i
      linear_combination h - h'
    · simpa using h

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ainf_sign_unit (F : Type) [Field F] [NumberField F] (a : InfiniteAdeleRing F) :
    ∃ s : InfiniteAdeleRing F, s * s = 1 ∧ IsUnit (a + s) := by
  have h2 : ∀ w : InfinitePlace F, (2 : w.Completion) ≠ 0 := by
    intro w h
    have : algebraMap F w.Completion 2 = 0 := by rw [map_ofNat]; exact h
    exact two_ne_zero ((map_eq_zero_iff _ (algebraMap F w.Completion).injective).1 this)
  exact pi_sign_unit (K := fun w : InfinitePlace F => w.Completion) h2 a

end Formalism.IndefR.Fin.DL

end
