import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_dual_zmod_le_card :
    ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A],
      Nat.card (Module.Dual (ZMod n) A) ≤ Nat.card A := by
  intro n _ A _ _ _
  classical
  haveI : Fintype A := Fintype.ofFinite A
  let Φ : Module.Dual (ZMod n) A → AddChar A ℂ := fun f =>
    (ZMod.stdAddChar (N := n)).compAddMonoidHom f.toAddMonoidHom
  have hinj : Function.Injective Φ := by
    intro f g h
    ext a
    have h1 := congrArg (fun χ : AddChar A ℂ => χ a) h
    simp only [Φ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at h1
    exact ZMod.injective_stdAddChar h1
  calc Nat.card (Module.Dual (ZMod n) A) ≤ Nat.card (AddChar A ℂ) :=
        Nat.card_le_card_of_injective Φ hinj
    _ = Nat.card A := by
        rw [Nat.card_eq_fintype_card, AddChar.card_eq, Nat.card_eq_fintype_card]

end GlobalTheory
