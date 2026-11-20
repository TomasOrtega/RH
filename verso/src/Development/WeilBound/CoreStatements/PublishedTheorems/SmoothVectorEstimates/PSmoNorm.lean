import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Substitute using the available equality.

A detailed English derivation is pending.
-/
theorem smonorm_of : Meet → CuspidalIrreducibleSubrep → SmoNorm := by
  intro hM hG E _ _ _ a π π' hπ hπ' hS
  let μ : Measure (GA E a) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨H, hH, hf⟩ := hG E a μ π hπ
  obtain ⟨H', hH', hf'⟩ := hG E a μ π' hπ'
  have hne : H ⊓ H' ≠ ⊥ := hM E a μ π π' H H' hπ hπ' hH.1 hH'.1
    (fun φ hφ => ⟨hf.finitePartMemL2 φ hφ, hf.classes_le (toL2_mem_classes hφ (hf.finitePartMemL2 φ hφ))⟩)
    (fun φ hφ => ⟨hf'.finitePartMemL2 φ hφ, hf'.classes_le (toL2_mem_classes hφ (hf'.finitePartMemL2 φ hφ))⟩) hS
  have h1 : H ⊓ H' = H := (hH.2.2 _ inf_le_left (hH.1.inf hH'.1)).resolve_left hne
  have h2 : H ⊓ H' = H' := (hH'.2.2 _ inf_le_right (hH.1.inf hH'.1)).resolve_left hne
  have e : H = H' := h1.symm.trans h2
  subst e
  exact hf.unique hf'

end PositivityTheory.jumpWindows

end
