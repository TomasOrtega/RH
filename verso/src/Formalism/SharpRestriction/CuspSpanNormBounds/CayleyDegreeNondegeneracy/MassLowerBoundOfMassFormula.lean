import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeStructureOfDet
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatDetSqOfCyclicDualQuotient
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `hTp h3 hsp F0 he hz Λ hrow`. Take `⟨hΛ, hu, hlift, hconv⟩` from `hrow.2.1`. Take `⟨w₁, hw₁, hgen, hann⟩` from `dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero`. Use `latDet_of_cyclic_dual_quotient D _ (orthLattice_isLattice F0 he hz Λ hΛ hu) ?_ hTp hsp w₁ hw₁ hgen hann` and prove the remaining obligations. Introduce `x hx`.

Conclude with `(i_mem_dual _ _).2 fun y hy => orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu y hy x hx`.
-/
theorem det_orthLattice_eq_pow (D : D7) (u : D.what₂.Word) :
    ForPrimeFlagLattice D u fun F0 Λ => latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ) := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  refine latDet_of_cyclic_dual_quotient D _ (orthLattice_isLattice F0 he hz Λ hΛ hu) ?_ hTp hsp w₁ hw₁ hgen hann
  intro x hx
  exact (i_mem_dual _ _).2 fun y hy => orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu y hy x hx

/- English proof (translation)
The claim follows from `orthLattice_structure_of_det D u (det_orthLattice_eq_pow D u)`.
-/
theorem orthLattice_structure (D : D7) (u : D.what₂.Word) : BaseLatticeStructure D u := orthLattice_structure_of_det D u (det_orthLattice_eq_pow D u)

/- English proof (translation)
The claim follows from `orth_space_posDef_every_place (Formalism.MainNotions.S.Inh.tie_flag0 D u) rfl rfl hT`.
-/
theorem orth_space_posDef (D : D7) (u : D.what₂.Word) (hT : 0 < Tu D u) : IsPosDef (D.sp.X 0).hT :=
  orth_space_posDef_every_place (Formalism.MainNotions.S.Inh.tie_flag0 D u) rfl rfl hT

end Formalism.MainNotions.BridgeLemma₂

end
