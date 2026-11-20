import Formalism.WachLatticeTwists.RamifiedBlockRings.DeltaRingProp
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem deltaRing : DeltaRingProp := by
  intro O _ _ _ X d G _ _ _ t bl T r₀ π χ₁ ε g₀ eB e₁ s D hD ℓ hℓ hu s₀ hs hs2 y hy
  obtain ⟨-, -, -, -, -, hrr, -⟩ := hD
  have h1 : D.δO = ∏ i ∈ Finset.Ioo 0 t,
      ((χ₁ g₀ : O) - (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)) := by
    have h2 : D.δO = ∏ i ∈ Finset.Ioo 0 t,
        ((D.rr 0 : D.X' → O) D.π' - (D.rr i : D.X' → O) D.π') := by
      show ((Pi.evalRingHom (fun _ : D.X' => O) D.π').comp D.T'.val.toRingHom) D.δ = _
      unfold RingData.δ
      rw [map_prod]; rfl
    rw [h2]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_Ioo] at hi
    rw [hrr 0 (by omega), hrr i hi.2]
    simp
  rw [h1]
  exact Formalism.RepresentationBoundsCohomology.BR.theorem_n_five_delta_clause O ℓ hℓ hu s₀ hs hs2 (ε g₀) y (χ₁ g₀) hy t

end Formalism.RepresentationBoundsCohomology.ringDataObjects
