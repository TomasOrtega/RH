import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumAlternatingCardElementarySublatticesAboveStatement

open GlobalTheory.LatHecke

namespace GlobalTheory.HeckeSeries

open Classical

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ}

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_subIdx_sub_iff {n k : ℕ} (hk : k ≤ n) {L M' M : Lat O K r}
    (hM' : M' ∈ subElem k L) :
    M ∈ subIdx (n - k) M' ↔ M ∈ subIdx n L ∧ M.1 ≤ M'.1 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := hM'
  have hq : 0 < qRes O := lt_of_lt_of_le two_pos two_le_qRes
  have hpow : qRes O ^ n = qRes O ^ (n - k) * qRes O ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  constructor
  · rintro ⟨h3, h4⟩
    refine ⟨⟨h3.trans h1, ?_⟩, h3⟩
    rw [← AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup M'.1.toAddSubgroup
      L.1.toAddSubgroup h3 h1, h4, h2, hpow]
  · rintro ⟨⟨-, h4⟩, h5⟩
    refine ⟨h5, ?_⟩
    have h := AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup M'.1.toAddSubgroup
      L.1.toAddSubgroup h5 h1
    rw [h4, h2, hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq k) h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem heckeElem_heckeAll_eq {E : Type} [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E)
    {n k : ℕ} (hk : k ≤ n) (L : Lat O K r) :
    heckeElem k (heckeAll (n - k) φ) L = ∑ M ∈ (subIdx_finite n L).toFinset,
      ((((subElem_finite k L).toFinset.filter (fun M' => M.1 ≤ M'.1)).card : ℂ)) • φ M := by
  rw [heckeElem_eq_sum]
  have h : ∀ M' ∈ (subElem_finite k L).toFinset, heckeAll (n - k) φ M' =
      ∑ M ∈ (subIdx_finite n L).toFinset, if M.1 ≤ M'.1 then φ M else 0 := by
    intro M' hM'
    rw [heckeAll_eq_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext M
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact mem_subIdx_sub_iff hk ((Set.Finite.mem_toFinset _).1 hM')
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem heckeSeries_identity : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (E : Type) [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E) (n : ℕ) (L : Lat O K r),
    1 ≤ n → ∑ k ∈ Finset.range (n + 1), ((-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2)) •
      heckeElem k (heckeAll (n - k) φ) L = 0 := by
  intro O K _ _ _ _ _ _ _ r E _ _ φ n L hn
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [heckeElem_heckeAll_eq φ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) L])]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun M hM => ?_
  rw [← Finset.sum_smul]
  have hM' : M ∈ subIdx n L := (Set.Finite.mem_toFinset _).1 hM
  have h := GlobalTheory.T.sum_alternating_card_elementarySublattices_above O K r n L M hn hM'
  convert zero_smul ℂ (φ M) using 2
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  rw [← Set.ncard_coe_finset]
  congr 1
  ext M'
  simp

end GlobalTheory.HeckeSeries
