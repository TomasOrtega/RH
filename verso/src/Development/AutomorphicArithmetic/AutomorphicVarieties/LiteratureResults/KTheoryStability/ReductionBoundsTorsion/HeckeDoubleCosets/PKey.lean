import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.KeyGenAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PermMatrixMulApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.Affine

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem pKey (hT : PTransfer) : PKey := by
  intro hCh hEv hAff L _ _ hC k hk π hπ n r hn1 hr1 F hFinv hFcoc z hz
  haveI := (pIndex L (n + r) π hπ).1
  haveI := (pIndex L n π hπ).1
  have hSK := pStabK L π hπ.ne_zero n r hn1
  refine keyGen hT hSK.1 hSK.2 (fun c => pGqStab L π hπ n r hn1 c) k F hFinv hFcoc ?_ z hz
  intro c hc H hH w hw
  have hlow : ∃ i : Fin r, ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))
      (Fin.natAdd n i) ⟨0, by omega⟩ ∉ Ideal.span {π} := by
    by_contra hne
    push_neg at hne
    obtain ⟨c', hc'⟩ := pLow L π hπ n r hn1 c hne
    exact hc c' hc'
  have h := pStabVan hCh hEv hAff L hC k hk π hπ n r hn1 hr1 c hlow F hFinv hFcoc H hH w hw
  simpa only [map_mul, mul_assoc] using h

end PositivityTheory.KB.AffineStabilizerVanishing

end
