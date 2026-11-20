import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

/- English proof (translation)
Replace the relevant objects with their definitions. Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem delAt_unitary_triv {D : D7} (C : CharFrame D) (l : ℕ) : (C.delAt l).IsUnitary ∧ (C.delAt l).TrivOn D.host.F := by
  unfold CharFrame.delAt
  split_ifs
  · exact ⟨C.isDel'.unitary, C.isDel'.triv⟩
  · exact ⟨C.isDel.unitary, C.isDel.triv⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem toricLam0_unitary_trivOnMaxRealSubfield : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m),
    (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  intro D Z h l j a
  have hd := delAt_unitary_triv Z.C l
  exact ⟨((Z.C.isMu0 j).unitary.mul hd.1).mul (h.aux a).unitary.inv,
    ((Z.C.isMu0 j).triv.mul hd.2).mul (h.aux a).triv.inv⟩

end GlobalTheory.LamTie
