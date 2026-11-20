import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagRatioTrdeg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PGenLeadMinorNeZero
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace FlagArithVar

variable (Ψ : Type) (N : ℕ)

/- English proof (translation)
Rewrite using `[yFl, RingHom.map_det]`. Use `congr 1`.
-/
theorem yFl_eq (q : FlBlock Ψ N) (A : FlIdx Ψ N q) :
    yFl Ψ N ⟨q, A⟩ = ((genMatFr ℚ Ψ N q.1).submatrix (Fin.castLE (step_le q.2)) A.1).det := by
  rw [yFl, RingHom.map_det]
  congr 1

def leadIdx (q : FlBlock Ψ N) : FlIdx Ψ N q := ⟨Fin.castLE (step_le q.2), Fin.strictMono_castLE _⟩

/- English proof (translation)
Rewrite using `[yFl_eq, leadMinor, pivotMinor]`. Use `congr 2`. Use function extensionality and compare the values at `c`. Apply `Fin.ext` to reduce the goal to its premises. Use `c.isLt` as an intermediate fact.

Simplify using `only [leadIdx, Fin.val_castLE, pivotCols]`. Use `split_ifs with h`. Both sides reduce to the same expression. Simplify using `only [Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers.
-/
theorem yFl_lead (q : FlBlock Ψ N) : yFl Ψ N ⟨q, leadIdx Ψ N q⟩ = leadMinor (genMatFr ℚ Ψ N q.1) q.2 := by
  rw [yFl_eq, leadMinor, pivotMinor]
  congr 2
  funext c
  apply Fin.ext
  have := c.isLt
  simp only [leadIdx, Fin.val_castLE, pivotCols]
  split_ifs with h
  · rfl
  · simp only [Fin.val_castLE]; omega

/- English proof (translation)
Rewrite using `[yFl_eq, flagMinor]`. Use `congr 2`. Conclude with `Finset.orderEmbOfFin_unique _ (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) A.2`.
-/
theorem yFl_eq_flagMinor (q : FlBlock Ψ N) (A : FlIdx Ψ N q) :
    yFl Ψ N ⟨q, A⟩ = flagMinor (genMatFr ℚ Ψ N q.1) q.2
      ⟨Finset.univ.image A.1, by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩ := by
  rw [yFl_eq, flagMinor]
  congr 2
  exact Finset.orderEmbOfFin_unique _ (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) A.2

/- English proof (translation)
Rewrite using `[yFl_eq, flagMinor]`.
-/
theorem flagMinor_eq_yFl (τ : Ψ) (i : Fin (N - 1)) (S : PluckerBlocks N N i) :
    flagMinor (genMatFr ℚ Ψ N τ) i S = yFl Ψ N ⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ := by
  rw [yFl_eq, flagMinor]

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨q, A⟩, rfl⟩`. Use `⟨(q.1, ⟨q.2, ⟨Finset.univ.image A.1, by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩⟩), ?_⟩` and prove the remaining obligations. Use `show flagMinor _ _ _ / leadMinor _ _ = yFl Ψ N ⟨q, A⟩ / yFl Ψ N ⟨q, leadIdx Ψ N q⟩`.

Rewrite using `[yFl_lead, yFl_eq_flagMinor]`. Introduce and unpack `⟨⟨τ, i, S⟩, rfl⟩`. Use `⟨⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩` and prove the remaining obligations. Use `show yFl Ψ N _ / yFl Ψ N ⟨(τ, i), leadIdx Ψ N (τ, i)⟩ = flagMinor _ _ _ / leadMinor _ _`. Rewrite using `[yFl_lead, flagMinor_eq_yFl]`.
-/
theorem coneRatios_eq : coneRatios (yFl Ψ N) (leadIdx Ψ N) = Set.range (flagMinorRatio ℚ Ψ N) := by
  ext x
  constructor
  · rintro ⟨⟨q, A⟩, rfl⟩
    refine ⟨(q.1, ⟨q.2, ⟨Finset.univ.image A.1,
      by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩⟩), ?_⟩
    show flagMinor _ _ _ / leadMinor _ _ = yFl Ψ N ⟨q, A⟩ / yFl Ψ N ⟨q, leadIdx Ψ N q⟩
    rw [yFl_lead, yFl_eq_flagMinor]
  · rintro ⟨⟨τ, i, S⟩, rfl⟩
    refine ⟨⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩
    show yFl Ψ N _ / yFl Ψ N ⟨(τ, i), leadIdx Ψ N (τ, i)⟩ = flagMinor _ _ _ / leadMinor _ _
    rw [yFl_lead, flagMinor_eq_yFl]

/- English proof (translation)
Rewrite using `[IntermediateField.adjoin_toSubfield]`. Use `le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure)) (Subfield.closure_mono Set.subset_union_right)` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[eq_ratCast]`. Conclude with `SubfieldClass.ratCast_mem _ q`.
-/
theorem toSubfield_adjoin_rat {E : Type} [Field E] [Algebra ℚ E] (s : Set E) :
    (IntermediateField.adjoin ℚ s).toSubfield = Subfield.closure s := by
  rw [IntermediateField.adjoin_toSubfield]
  refine le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure))
    (Subfield.closure_mono Set.subset_union_right)
  rintro _ ⟨q, rfl⟩
  rw [eq_ratCast]
  exact SubfieldClass.ratCast_mem _ q

/- English proof (translation)
Rewrite using `[← (RingEquiv.subfieldCongr (toSubfield_adjoin_rat s)).toIntAlgEquiv.trdeg_eq]`. Conclude with `AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv`.
-/
theorem trdeg_int_adjoin {E : Type} [Field E] [Algebra ℚ E] (s : Set E) :
    Algebra.trdeg ℤ (IntermediateField.adjoin ℚ s) = Algebra.trdeg ℤ (Subfield.closure s) := by
  rw [← (RingEquiv.subfieldCongr (toSubfield_adjoin_rat s)).toIntAlgEquiv.trdeg_eq]
  exact AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv

/- English proof (translation)
Establish `: Algebra.IsAlgebraic ℤ ℚ` using `IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)`. Establish `: FaithfulSMul ℤ ℚ` using `(faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective`. Establish `: FaithfulSMul ℚ L` using `(faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective`. Rewrite using `[← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]`.
-/
theorem trdeg_int_eq_rat {L : Type} [Field L] (I : Algebra ℚ L) :
    Algebra.trdeg ℤ L = @Algebra.trdeg ℚ L _ _ I := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have : FaithfulSMul ℤ ℚ := (faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective
  have : FaithfulSMul ℚ L := (faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective
  rw [← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]

/- English proof (translation)
Rewrite using `[← trdeg_int_adjoin, trdeg_int_eq_rat (IntermediateField.adjoin ℚ s).algebra']`. Conclude with `h`.
-/
theorem trdeg_closure_of_rat {E : Type} [Field E] {iQ : Algebra ℚ E} (s : Set E) {c : Cardinal}
    (h : @Algebra.trdeg ℚ (IntermediateField.adjoin ℚ s) _ _ (IntermediateField.adjoin ℚ s).algebra' = c) :
    Algebra.trdeg ℤ (Subfield.closure s) = c := by
  rw [← trdeg_int_adjoin, trdeg_int_eq_rat (IntermediateField.adjoin ℚ s).algebra']
  exact h

end FlagArithVar

open FlagArithVar in

/- English proof (translation)
Introduce `Ψ _ _ _ N hN`. Establish `hc : ∀ q, yFl Ψ N ⟨q, leadIdx Ψ N q⟩ ≠ 0` using `fun q => by`. Rewrite using `[yFl_lead]`. Conclude with `GenLeadMinorNeZero.full ℚ Ψ N q.1 q.2`. Establish `hK : Nonempty (FlBlock Ψ N)` using `⟨(Classical.arbitrary Ψ, ⟨0, by omega⟩)⟩`.

Establish `hhor : IsHorizontal (PFl Ψ N)` using `horizontal (yFl Ψ N)`. Use `⟨hK, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (yFl Ψ N), relevant (yFl Ψ N) _ hc⟩, hhor, ?_⟩` and prove the remaining obligations. Establish `htr` using `ConeTrdeg.full _ (FlIdx Ψ N) (ratioField (yFl Ψ N) (leadIdx Ψ N)) (ratioPtL (yFl Ψ N) (leadIdx Ψ N)) (birational (yFl Ψ N) _ hc) (fun k ↦ ⟨leadIdx Ψ N k, fun h0 ↦ by`. Establish `h1` using `congrArg Subtype.val h0`. Simplify using `[ratioPtL, ratioPt, hc] at h1⟩)`.

Use the proof step `(by rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc]; exact hhor)`. Establish `hL : Algebra.trdeg ℤ (ratioField (yFl Ψ N) (leadIdx Ψ N)) = ((dimFl Ψ N : ℕ) : Cardinal)`. Establish `h` using `trdeg_closure_of_rat _ (FlagRatioTrdeg.full ℚ Ψ N)`. Rewrite using `[ratioField, coneRatios_eq, trdeg_int_adjoin]`. Conclude with `h`.

Rewrite `htr` using `[mCoordIdeal_ratioPtL (yFl Ψ N) _ hc, hL]`. Establish `: (PFl Ψ N).IsPrime` using `RingHom.ker_isPrime _`. Establish `hA` using `IntDomainDim.full (MRing (FlIdx Ψ N) ⧸ PFl Ψ N) (algebraMap_injective _ hhor)`. Rewrite using `[hA]`. Unfold `PFl`.

Rewrite using `[htr, ← Nat.cast_add, Cardinal.toENat_nat]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FlagArithVar.proof : FlagArithVar.Statement := by
  intro Ψ _ _ _ N hN
  have hc : ∀ q, yFl Ψ N ⟨q, leadIdx Ψ N q⟩ ≠ 0 := fun q => by
    rw [yFl_lead]; exact GenLeadMinorNeZero.full ℚ Ψ N q.1 q.2
  have hK : Nonempty (FlBlock Ψ N) := ⟨(Classical.arbitrary Ψ, ⟨0, by omega⟩)⟩
  have hhor : IsHorizontal (PFl Ψ N) := horizontal (yFl Ψ N)
  refine ⟨hK, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (yFl Ψ N), relevant (yFl Ψ N) _ hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ (FlIdx Ψ N) (ratioField (yFl Ψ N) (leadIdx Ψ N))
    (ratioPtL (yFl Ψ N) (leadIdx Ψ N)) (birational (yFl Ψ N) _ hc)
    (fun k ↦ ⟨leadIdx Ψ N k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (ratioField (yFl Ψ N) (leadIdx Ψ N)) = ((dimFl Ψ N : ℕ) : Cardinal) := by
    have h := trdeg_closure_of_rat _ (FlagRatioTrdeg.full ℚ Ψ N)
    rw [ratioField, coneRatios_eq, trdeg_int_adjoin]
    exact h
  rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc, hL] at htr
  have : (PFl Ψ N).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing (FlIdx Ψ N) ⧸ PFl Ψ N) (algebraMap_injective _ hhor)
  rw [hA]
  unfold PFl
  rw [htr, ← Nat.cast_add, Cardinal.toENat_nat]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
