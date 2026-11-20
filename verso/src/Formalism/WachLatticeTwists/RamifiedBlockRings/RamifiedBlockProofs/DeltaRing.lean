import Formalism.WachLatticeTwists.RamifiedBlockRings.DeltaRingProp
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

/- English proof (translation)
Introduce `O _ _ _ X d G _ _ _ t bl T r₀ π χ₁ ε g₀ eB e₁ s D hD ℓ hℓ hu s₀ hs hs2 y hy`. Take `⟨-, -, -, -, -, hrr, -⟩` from `hD`. Establish `h1 : D.δO = ∏ i ∈ Finset.Ioo 0 t, ((χ₁ g₀ : O) - (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O))`. Establish `h2 : D.δO = ∏ i ∈ Finset.Ioo 0 t, ((D.rr 0 : D.X' → O) D.π' - (D.rr i : D.X' → O) D.π')` using `by show ((Pi.evalRingHom (fun _ : D.X' => O) D.π').comp D.T'.val.toRingHom) D.δ = _`. Unfold `RingData.δ`.

Rewrite using `[map_prod]`. Both sides reduce to the same expression. Rewrite using `[h2]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_Ioo]`.

Rewrite using `[hrr 0 (by omega), hrr i hi.2]`. Simplify using the standard rewrite rules. Rewrite using `[h1]`. Conclude with `Formalism.RepresentationBoundsCohomology.BR.theorem_n_five_delta_clause O ℓ hℓ hu s₀ hs hs2 (ε g₀) y (χ₁ g₀) hy t`.
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
