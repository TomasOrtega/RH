import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagNeZero
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioTrdeg
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.CoordinateConeArithVar

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B`. Use `choose cX hcX using D.arith.2.1.2.2`. Use `choose cP hcP using hNe II Ψ K ι Ω E D Pl H B`. Set `c : ∀ k, Pl.ιY k` to `fun`. Consider the case `Sum.inl k => cX k`.

Consider the case `Sum.inr q => cP q.1 q.2`. Establish `hc : ∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0`. Introduce and unpack `(k | q)`. Introduce `h`. Establish `h0 : D.y ⟨k, cX k⟩ = 0`.

Establish `h' : Pl.ofΩ (D.y ⟨k, cX k⟩) = 0` using `h`. Establish `h2 : (C (D.y ⟨k, cX k⟩) : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) = 0` using `IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (by rw [map_zero]; exact h')`. Conclude with `C_injective _ _ (h2.trans C_0.symm)`. Apply `hcX k` to reduce the goal to its premises. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]`.

Conclude with `hcP q.1 q.2`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `: CharZero Pl.ΩY` using `charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY)`. Establish `hhor : IsHorizontal (Pl.flagPrime B)` using `horizontal (Pl.flagGenericPoint B)`. Use `⟨⟨Sum.inl D.arith.1.some⟩, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (Pl.flagGenericPoint B), relevant (Pl.flagGenericPoint B) c hc⟩, hhor, ?_⟩` and prove the remaining obligations.

Establish `htr` using `ConeTrdeg.full _ Pl.ιY (ratioField (Pl.flagGenericPoint B) c) (ratioPtL (Pl.flagGenericPoint B) c) (birational (Pl.flagGenericPoint B) c hc) (fun k ↦ ⟨c k, fun h0 ↦ by`. Establish `h1` using `congrArg Subtype.val h0`. Simplify using `[ratioPtL, ratioPt, hc] at h1⟩)`. Use the proof step `(by rw [mCoordIdeal_ratioPtL (Pl.flagGenericPoint B) c hc]; exact hhor)`. Establish `hL : Algebra.trdeg ℤ (ratioField (Pl.flagGenericPoint B) c) = ((D.n + D.flagDim0 : ℕ) : Cardinal)`.

Rewrite using `[← hTr II Ψ K ι Ω E D Pl H B c hc]`. Establish `hsub : (ratioField (Pl.flagGenericPoint B) c).toSubfield = Subfield.closure (coneRatios (Pl.flagGenericPoint B) c)`. Simplify using `only [IntermediateField.adjoin_toSubfield]`. Use `le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure)) (Subfield.closure_mono Set.subset_union_right)` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`.

Rewrite using `[eq_ratCast]`. Conclude with `SubfieldClass.ratCast_mem _ q`. Rewrite using `[← (RingEquiv.subfieldCongr hsub).toIntAlgEquiv.trdeg_eq]`. Conclude with `AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv`. Rewrite `htr` using `[mCoordIdeal_ratioPtL (Pl.flagGenericPoint B) c hc, hL]`.

Establish `: (mCoordIdeal (Pl.flagGenericPoint B)).IsPrime` using `RingHom.ker_isPrime _`. Establish `hA` using `IntDomainDim.full (MRing Pl.ιY ⧸ mCoordIdeal (Pl.flagGenericPoint B)) (algebraMap_injective _ hhor)`. Use `show ringKrullDim (MRing Pl.ιY ⧸ mCoordIdeal (Pl.flagGenericPoint B)) = _`. Rewrite using `[hA, htr]`. Rewrite using `[← Nat.cast_add, Cardinal.toENat_nat, show D.n + 1 + D.flagDim0 + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) = D.n + D.flagDim0 + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) + 1 by omega]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem HodgeFlagArith.proof (hNe : HodgeFlagNeZero.Statement) (hTr : HodgeFlagRatioTrdeg.Statement) :
    HodgeFlagArith.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B
  choose cX hcX using D.arith.2.1.2.2
  choose cP hcP using hNe II Ψ K ι Ω E D Pl H B
  let c : ∀ k, Pl.ιY k := fun
    | Sum.inl k => cX k
    | Sum.inr q => cP q.1 q.2
  have hc : ∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0 := by
    rintro (k | q)
    · intro h
      have h0 : D.y ⟨k, cX k⟩ = 0 := by
        have h' : Pl.ofΩ (D.y ⟨k, cX k⟩) = 0 := h
        have h2 : (C (D.y ⟨k, cX k⟩) : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) = 0 :=
          IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (by rw [map_zero]; exact h')
        exact C_injective _ _ (h2.trans C_0.symm)
      apply hcX k
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
    · exact hcP q.1 q.2
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : CharZero Pl.ΩY :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY)
  have hhor : IsHorizontal (Pl.flagPrime B) := horizontal (Pl.flagGenericPoint B)
  refine ⟨⟨Sum.inl D.arith.1.some⟩, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (Pl.flagGenericPoint B),
    relevant (Pl.flagGenericPoint B) c hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ Pl.ιY (ratioField (Pl.flagGenericPoint B) c) (ratioPtL (Pl.flagGenericPoint B) c)
    (birational (Pl.flagGenericPoint B) c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL (Pl.flagGenericPoint B) c hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (ratioField (Pl.flagGenericPoint B) c) = ((D.n + D.flagDim0 : ℕ) : Cardinal) := by
    rw [← hTr II Ψ K ι Ω E D Pl H B c hc]
    have hsub : (ratioField (Pl.flagGenericPoint B) c).toSubfield = Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
      simp only [IntermediateField.adjoin_toSubfield]
      refine le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure))
        (Subfield.closure_mono Set.subset_union_right)
      rintro _ ⟨q, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem _ q
    rw [← (RingEquiv.subfieldCongr hsub).toIntAlgEquiv.trdeg_eq]
    exact AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv
  rw [mCoordIdeal_ratioPtL (Pl.flagGenericPoint B) c hc, hL] at htr
  have : (mCoordIdeal (Pl.flagGenericPoint B)).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing Pl.ιY ⧸ mCoordIdeal (Pl.flagGenericPoint B)) (algebraMap_injective _ hhor)
  show ringKrullDim (MRing Pl.ιY ⧸ mCoordIdeal (Pl.flagGenericPoint B)) = _
  rw [hA, htr]
  rw [← Nat.cast_add, Cardinal.toENat_nat,
    show D.n + 1 + D.flagDim0 + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) =
      D.n + D.flagDim0 + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) + 1 by omega]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
