import Development.EtaleCohomology.EtaleSheaves.FMrangePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.FMrangePfQc

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem finset_idem {W : Type} [CommRing W] (hW : ProdACF W) (t : Finset W) :
    ∃ e : W, IsIdempotentElem e ∧ ∀ p : PrimeSpectrum W, p ∈ (PrimeSpectrum.zeroLocus (t : Set W))ᶜ ↔ e ∉ p.asIdeal := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp⟩
  | insert a t _ ih =>
    obtain ⟨e, he, hpe⟩ := ih
    obtain ⟨f, u, hf, hu, rfl⟩ := hW.2 a
    refine ⟨f + e - f * e, ?_, fun p => ?_⟩
    · unfold IsIdempotentElem at *
      linear_combination (1 - e + (e * e - e)) * hf + (1 - f) * he
    · have hfe : f * (f + e - f * e) = f := by
        have := hf.eq; linear_combination (1 - e) * this
      have hef : e * (f + e - f * e) = e := by
        have := he.eq; linear_combination (1 - f) * this
      have key : f + e - f * e ∈ p.asIdeal ↔ f ∈ p.asIdeal ∧ e ∈ p.asIdeal := by
        constructor
        · intro h
          exact ⟨hfe ▸ p.asIdeal.mul_mem_left f h, hef ▸ p.asIdeal.mul_mem_left e h⟩
        · rintro ⟨h1, h2⟩
          exact p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right e h1)
      have hfu : f * u ∈ p.asIdeal ↔ f ∈ p.asIdeal := by
        constructor
        · intro h
          obtain ⟨v, hv⟩ := hu.exists_right_inv
          have := p.asIdeal.mul_mem_right v h
          rwa [mul_assoc, hv, mul_one] at this
        · exact fun h => p.asIdeal.mul_mem_right u h
      have h1 := hpe p
      simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Finset.coe_insert, Set.insert_subset_iff] at h1 ⊢
      rw [key]
      simp only [SetLike.mem_coe, hfu, not_iff_not.mp h1]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem QcIdem_pf : QcIdem := by
  intro W _ hW U hU
  obtain ⟨t, ht⟩ := (@PrimeSpectrum.isCompact_isOpen_iff W _ (U : Set (Spec (CommRingCat.of W)))).1 ⟨hU, U.isOpen⟩
  obtain ⟨e, he, hpe⟩ := finset_idem hW t
  refine ⟨e, he, fun p => ?_⟩
  rw [← hpe p, ht]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FMrange_of (hI : IdemLift) : FMrange :=
  FMrange_of_leaves hI QcIdem_pf

end LateralTheory.E.FMrangePfQc
