import Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

namespace LateralTheory.E.LeafTrdegDimPf

open Algebra

/- English proof (translation)
Establish `: Algebra.IsAlgebraic (Algebra.adjoin k (s : Set F)) F` using `⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.1 (h.isAlgebraic x)⟩`. Take `⟨t, hts, hb⟩` from `exists_isTranscendenceBasis_subset (R := k) (A := F) (s : Set F)`. Rewrite using `[← hb.cardinalMk_eq_trdeg]`. Combine the equalities or inequalities in the displayed calculation.
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
Introduce `k F Ω _ _ _ _ _ _ _ _ n s hs hF R hR`. Establish `hFT : Algebra.FiniteType k R` using `(Subalgebra.fg_iff_finiteType R).1 hR`. Take `⟨d, hd1, hd2⟩` from `GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k R`. Establish `h1 : Algebra.trdeg k R ≤ Algebra.trdeg k Ω` using `trdeg_le_of_injective R.val Subtype.val_injective`. Establish `h2 : Algebra.trdeg k Ω = Algebra.trdeg k F` using `GlobalTheory.trdeg_eq_of_isAlgebraic_top k F Ω`.

Establish `h3` using `trdeg_le_card k F s hF`. Establish `hdn : (d : Cardinal) ≤ (n : Cardinal)`. Rewrite using `[← hd2]`. Conclude with `h1.trans (h2 ▸ h3.trans (by exact_mod_cast hs))`. Establish `: d ≤ n` using `by exact_mod_cast hdn`.

Rewrite using `[hd1]`. Conclude with `this` after adjusting the coercions.
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
