import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoUnitaryOffDiagNormSqZeroIffMemMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevelStatement

namespace GlobalTheory.PsCo.Pc3

/- English proof (translation)
Introduce `n ε`. Take `⟨hcont, hinv⟩` from `GlobalTheory.T.offDiagBlockNorm_mul_invariant n ε`. Conclude with `⟨hcont, hinv, GlobalTheory.T.pseudoUnitary_offDiag_norm_sq_zero_iff_mem_maxCompact n ε, GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε⟩`.
-/
theorem stR : StR := by
  intro n ε
  obtain ⟨hcont, hinv⟩ := GlobalTheory.T.offDiagBlockNorm_mul_invariant n ε
  exact ⟨hcont, hinv, GlobalTheory.T.pseudoUnitary_offDiag_norm_sq_zero_iff_mem_maxCompact n ε, GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε⟩

end GlobalTheory.PsCo.Pc3
