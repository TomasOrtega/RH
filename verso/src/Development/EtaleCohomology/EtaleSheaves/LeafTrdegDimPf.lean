import Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

namespace LateralTheory.E.LeafTrdegDimPf

open Algebra

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.
-/
theorem trdeg_le_card (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (h : Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F) :
    Algebra.trdeg k F ≤ (s.card : Cardinal) := by
  have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set F)) F :=
    ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.1 (h.isAlgebraic x)⟩
  obtain ⟨t, hts, hb⟩ := exists_isTranscendenceBasis_subset (R := k) (A := F) (s : Set F)
  rw [← hb.cardinalMk_eq_trdeg]
  calc Cardinal.mk t ≤ Cardinal.mk (s : Set F) := Cardinal.mk_le_mk_of_subset hts
    _ = (s.card : Cardinal) := by simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem LeafTrdegDim_of : LateralTheory.E.LeafCurveVCut.LeafTrdegDim := by
  intro k F Ω _ _ _ _ _ _ _ _ n s hs hF R hR
  have hFT : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨d, hd1, hd2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k R
  have h1 : Algebra.trdeg k R ≤ Algebra.trdeg k Ω :=
    trdeg_le_of_injective R.val Subtype.val_injective
  have h2 : Algebra.trdeg k Ω = Algebra.trdeg k F := GlobalTheory.trdeg_eq_of_isAlgebraic_top k F Ω
  have h3 := trdeg_le_card k F s hF
  have hdn : (d : Cardinal) ≤ (n : Cardinal) := by
    rw [← hd2]
    exact h1.trans (h2 ▸ h3.trans (by exact_mod_cast hs))
  have : d ≤ n := by exact_mod_cast hdn
  rw [hd1]
  exact_mod_cast this

end LateralTheory.E.LeafTrdegDimPf
