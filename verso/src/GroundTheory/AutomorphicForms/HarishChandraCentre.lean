import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection
import GroundTheory.AutomorphicForms.HarishChandraCentre.Injective
import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
import GroundTheory.AutomorphicForms.HarishChandraCentre.LeadingTerm
import GroundTheory.AutomorphicForms.HarishChandraCentre.Symmetric
import GroundTheory.AutomorphicForms.HarishChandraCentre.Capelli
import GroundTheory.AutomorphicForms.HarishChandraCentre.Consequences

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

/- English proof (translation)
The claim follows from `harishChandraHom_isSymmetric z`.
-/
theorem harishChandraHom_mem_symmetricSubalgebra (z : Subalgebra.center ℂ (U n)) :
    harishChandraHom z ∈ symmetricSubalgebra (Fin n) ℂ :=
  harishChandraHom_isSymmetric z

noncomputable def capelliCenter (k : ℕ) : Subalgebra.center ℂ (U n) :=
  ⟨capelli (k + 1), capelli_mem_center _⟩

/- English proof (translation)
The claim follows from `adjoin_eq_symmetricSubalgebra _ (fun _ => harishChandraHom_isSymmetric _) (fun k => totalDegree_harishChandraHom_capelli_sub k)`.
-/
theorem adjoin_harishChandraHom_capelli :
    Algebra.adjoin ℂ (Set.range fun k : Fin n => harishChandraHom (capelliCenter (n := n) k)) =
      symmetricSubalgebra (Fin n) ℂ :=
  adjoin_eq_symmetricSubalgebra _ (fun _ => harishChandraHom_isSymmetric _)
    (fun k => totalDegree_harishChandraHom_capelli_sub k)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `harishChandraHom_isSymmetric z`. Rewrite using `[← adjoin_harishChandraHom_capelli, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `⟨_, rfl⟩`.
-/
theorem range_harishChandraHom :
    (harishChandraHom (n := n)).range = symmetricSubalgebra (Fin n) ℂ := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact harishChandraHom_isSymmetric z
  · rw [← adjoin_harishChandraHom_capelli, Algebra.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩

noncomputable def harishChandraEquiv :
    Subalgebra.center ℂ (U n) ≃ₐ[ℂ] symmetricSubalgebra (Fin n) ℂ :=
  (AlgEquiv.ofInjective harishChandraHom harishChandraHom_injective).trans
    (Subalgebra.equivOfEq _ _ range_harishChandraHom)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem harishChandraEquiv_apply (z : Subalgebra.center ℂ (U n)) :
    (harishChandraEquiv z : MvPolynomial (Fin n) ℂ) = harishChandraHom z := rfl

end GroundTheory.Automorphic.HarishChandra
