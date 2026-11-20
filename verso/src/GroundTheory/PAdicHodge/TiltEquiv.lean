import Mathlib
import GroundTheory.PAdicHodge.UntiltPerfectoid
import GroundTheory.PAdicHodge.UntiltApprox
import GroundTheory.PAdicHodge.UntiltGalois
import GroundTheory.PAdicHodge.UntiltGaloisCorr
import GroundTheory.PAdicHodge.CompletedAlgClosure
import GroundTheory.PAdicHodge.PerfectoidCharP
import GroundTheory.PAdicHodge.PerfectoidCriterion
import GroundTheory.PAdicHodge.TiltAlgClosed
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_isGalois_le {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L]
    [PerfectField F] (N : IntermediateField F L) [FiniteDimensional F N] :
    ∃ N' : IntermediateField F L, N ≤ N' ∧ FiniteDimensional F N' ∧ IsGalois F N' := by
  classical
  set B := Module.finBasis F N
  set f : Polynomial F := ∏ i, minpoly F (B i : L)
  have hint : ∀ i, IsIntegral F (B i : L) := fun i =>
    (IsIntegral.of_finite F (B i)).map (IntermediateField.val N)
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => minpoly.ne_zero (hint i)
  set N' := IntermediateField.adjoin F (f.rootSet L)
  have hsplit : (f.map (algebraMap F L)).Splits := IsAlgClosed.splits _
  have : Polynomial.IsSplittingField F N' f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hfin : FiniteDimensional F N' := Polynomial.IsSplittingField.finiteDimensional N' f
  have : Normal F N' := Normal.of_isSplittingField f
  have : IsGalois F N' := IsGalois.mk
  refine ⟨N', ?_, hfin, this⟩
  have hB : ∀ i, (B i : L) ∈ N' := fun i => by
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hf0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_finsetProd]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval F (B i : L))
  intro x hx
  have := congrArg (fun u : N => (u : L)) (B.sum_repr ⟨x, hx⟩)
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
  rw [← this]
  exact N'.sum_mem fun i _ => N'.smul_mem (hB i)

section InC

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p

variable (K C p) in
include K in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isPerfectoidField_of_isAlgClosed_of_normedAlgebra [CompleteSpace C] :
    IsPerfectoidField C p :=
  IsPerfectoidField.of_isAlgClosed p (by
    rw [← map_natCast (algebraMap K C), norm_algebraMap']
    exact IsPerfectoidField.norm_natCast_lt_one)

variable [IsPerfectoidField C p]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_eq_untiltField (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ M : IntermediateField K♭ C♭, FiniteDimensional K♭ M ∧ untiltField K C p M = L := by
  obtain ⟨N, hN, hLN⟩ := exists_le_untiltField (p := p) L
  have : PerfectField K♭ := PerfectRing.toPerfectField K♭ p
  obtain ⟨N', hNN', hN', hgal⟩ := exists_isGalois_le N
  obtain ⟨M, -, hM, hML⟩ :=
    exists_untiltField_eq_of_le N' L (hLN.trans (untiltField_mono hNN'))
  exact ⟨M, hM, hML⟩

instance isPerfectoidField_of_finiteDimensional (L : IntermediateField K C) [FiniteDimensional K L] :
    IsPerfectoidField L p := by
  obtain ⟨M, hM, hML⟩ := exists_eq_untiltField (p := p) L
  exact IsPerfectoidField.of_ringEquiv p (IntermediateField.equivOfEq hML).toRingEquiv
    fun _ => rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem untiltField_tiltIntermediateField (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ _ : FiniteDimensional K♭ (tiltIntermediateField p L),
      untiltField K C p (tiltIntermediateField p L) = L := by
  obtain ⟨M, hM, rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M) = M :=
    tiltIntermediateField_untiltField M
  rw [h]
  exact ⟨hM, rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem finrank_tiltIntermediateField (L : IntermediateField K C) [FiniteDimensional K L] :
    Module.finrank K♭ (tiltIntermediateField p L) = Module.finrank K L := by
  obtain ⟨M, hM, rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M) = M :=
    tiltIntermediateField_untiltField M
  rw [h, finrank_untiltField]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem existsUnique_tiltIntermediateField_eq (M : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ M] :
    ∃! L : IntermediateField K C, ∃ _ : FiniteDimensional K L, tiltIntermediateField p L = M := by
  refine ⟨untiltField K C p M, ⟨inferInstance, tiltIntermediateField_untiltField M⟩, ?_⟩
  rintro L ⟨hL, hLM⟩
  obtain ⟨M', hM', rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M') = M' :=
    tiltIntermediateField_untiltField M'
  rw [h] at hLM
  rw [hLM]

end InC

section Abstract

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem IsPerfectoidField.of_finiteDimensional (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
    (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] : IsPerfectoidField L p := by
  rcases IsPerfectoidField.charZero_or_charP (K := K) p with h0 | hp
  · have := IsPerfectoidField.completeSpace (K := K) p
    have : IsPerfectoidField (CompletedAlgClosure K) p :=
      isPerfectoidField_of_isAlgClosed_of_normedAlgebra K (CompletedAlgClosure K) p
    set j := CompletedAlgClosure.embedding K L
    let e : L ≃ₐ[K] j.fieldRange := AlgEquiv.ofInjectiveField j
    have : FiniteDimensional K j.fieldRange := LinearEquiv.finiteDimensional e.toLinearEquiv
    refine IsPerfectoidField.of_ringEquiv p e.symm.toRingEquiv fun y => ?_
    have h1 : ((e (e.symm y) : j.fieldRange) : CompletedAlgClosure K) = j (e.symm y) := rfl
    rw [AlgEquiv.apply_symm_apply] at h1
    change ‖e.symm y‖ = ‖(y : CompletedAlgClosure K)‖
    rw [h1, CompletedAlgClosure.norm_embedding]
  · exact IsPerfectoidField.of_finiteDimensional_of_charP (K := K) p L

end Abstract

end GroundTheory.PAdicHodge
