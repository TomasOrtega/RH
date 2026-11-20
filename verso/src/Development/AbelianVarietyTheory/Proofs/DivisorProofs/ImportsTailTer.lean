import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSpecialUnitarySupportedAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalPointsUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryFixingPlaneComplementMemClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncationSpecialUnitaryMemClosureStrongApproxStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.StrongApproxSUProof

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc g hg`. Establish `h3` using `GlobalTheory.T.truncation_specialUnitary_mem_closure_strongApprox GlobalTheory.T.specialUnitary_fixing_plane_complement_mem_closure GlobalTheory.T.exists_isotropic_places_alt F E σ hcm M J hM hJ S₁ S₂ ε hε hnc`. Use `closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_specialUnitarySupportedAtPlaces F E σ hcm M J hJ g hg)` and prove the remaining obligations. Introduce and unpack `x ⟨T₁, T₂, η, hη, hx⟩`. Use `closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_rational_points_unitary_group F E σ hcm M J hJ T₁ T₂ η hη x hx)` and prove the remaining obligations.

Introduce and unpack `y ⟨γ, hγ, hy⟩`. Conclude with `h3 T₁ T₂ η hη γ hγ y hy`.
-/
theorem strongApproxSU : StrongApproxSU := by
  intro F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc g hg
  have h3 := GlobalTheory.T.truncation_specialUnitary_mem_closure_strongApprox GlobalTheory.T.specialUnitary_fixing_plane_complement_mem_closure GlobalTheory.T.exists_isotropic_places_alt F E σ hcm M J hM hJ S₁ S₂ ε hε hnc
  refine closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_specialUnitarySupportedAtPlaces F E σ hcm M J hJ g hg)
  rintro x ⟨T₁, T₂, η, hη, hx⟩
  refine closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_rational_points_unitary_group F E σ hcm M J hJ T₁ T₂ η hη x hx)
  rintro y ⟨γ, hγ, hy⟩
  exact h3 T₁ T₂ η hη γ hγ y hy

end GlobalTheory.StrongApproxSUProof
