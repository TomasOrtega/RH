import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ker_map_residue_eq_span {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {σ : Type*} :
    RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MvPolynomial σ O →+* _) =
      Ideal.span {C ϖ} := by
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
    Set.image_singleton]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem SpecialIdealCorresp.proof : SpecialIdealCorresp.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P W hW hϖW
  obtain ⟨π, hπ⟩ : ∃ π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O),
      π = MvPolynomial.map (IsLocalRing.residue O) := ⟨_, rfl⟩
  have hsp : ∀ V : Ideal (MRing ι O), specialIdeal V = V.map π := fun V => by rw [hπ]; rfl
  have hsurj : Function.Surjective π := hπ ▸ MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := hπ ▸ ker_map_residue_eq_span hϖ
  have hle : ∀ {V : Ideal (MRing ι O)}, (C ϖ : MRing ι O) ∈ V → RingHom.ker π ≤ V := fun h => by
    rw [hker, Ideal.span_le, Set.singleton_subset_iff]; exact h
  have hcm : ∀ {V : Ideal (MRing ι O)}, (C ϖ : MRing ι O) ∈ V → (V.map π).comap π = V := fun h => by
    rw [Ideal.comap_map_of_surjective' π hsurj, sup_eq_left.mpr (hle h)]
  simp only [hsp]
  refine ⟨Ideal.map_isPrime_of_surjective hsurj (hle hϖW), ?_, ?_, ?_⟩
  · have hJ : P ⊔ Ideal.span {C ϖ} = (P.map π).comap π := by
      rw [Ideal.comap_map_of_surjective' π hsurj, hker]
    rw [hJ, Ideal.comap_minimalPrimes_eq_of_surjective hsurj]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      rwa [Ideal.map_comap_of_surjective π hsurj]
    · intro h
      exact ⟨_, h, hcm hϖW⟩
  · have hX : ∀ v, (X v : MRing ι O) ∈ W ↔ (X v : MRing ι (IsLocalRing.ResidueField O)) ∈ W.map π :=
      fun v => by
        conv_lhs => rw [← hcm hϖW]
        rw [Ideal.mem_comap, hπ, MvPolynomial.map_X]
    simp only [IsRelevant, hX]
  · intro W' _ hϖW' h
    rw [← hcm hϖW', ← hcm hϖW, h]

end GroundTheory.Heights₂.Heights.NumbersDVR
