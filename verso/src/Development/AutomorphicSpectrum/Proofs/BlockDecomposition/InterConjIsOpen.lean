import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.TopGroup

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem inter_conj_isOpen :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G),
      IsOpen (J : Set G) → ∀ g : G,
        IsOpen ((J ⊓ J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro G _ _ _ J hJ g
  have hpre : ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
      = (fun x : G => g⁻¹ * x * g) ⁻¹' (J : Set G) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩
  have hcont : Continuous (fun x : G => g⁻¹ * x * g) := by fun_prop
  have h2 : IsOpen ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [hpre]; exact hJ.preimage hcont
  rw [Subgroup.coe_inf]
  exact hJ.inter h2

end GlobalTheory.CompanionTheory.TopGroup
