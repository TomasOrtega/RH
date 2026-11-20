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
Use `set B := Module.finBasis F N`. Use `set f : Polynomial F := ∏ i, minpoly F (B i : L)`. Establish `hint : ∀ i, IsIntegral F (B i : L)` using `fun i => (IsIntegral.of_finite F (B i)).map (IntermediateField.val N)`. Establish `hf0 : f ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => minpoly.ne_zero (hint i)`. Use `set N' := IntermediateField.adjoin F (f.rootSet L)`.

Establish `hsplit : (f.map (algebraMap F L)).Splits` using `IsAlgClosed.splits _`. Establish `: Polynomial.IsSplittingField F N' f` using `IntermediateField.adjoin_rootSet_isSplittingField hsplit`. Establish `hfin : FiniteDimensional F N'` using `Polynomial.IsSplittingField.finiteDimensional N' f`. Establish `: Normal F N'` using `Normal.of_isSplittingField f`. Establish `: IsGalois F N'` using `IsGalois.mk`.

Use `⟨N', ?_, hfin, this⟩` and prove the remaining obligations. Establish `hB : ∀ i, (B i : L) ∈ N'` using `fun i => by`. Apply `IntermediateField.subset_adjoin` to reduce the goal to its premises. Rewrite using `[Polynomial.mem_rootSet]`. Use `⟨hf0, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_finsetProd]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval F (B i : L))`. Introduce `x hx`. Use `congrArg (fun u : N => (u : L)) (B.sum_repr ⟨x, hx⟩)` as an intermediate fact. Simplify using `only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this`.

Rewrite using `[← this]`. Conclude with `N'.sum_mem fun i _ => N'.smul_mem (hB i)`.
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
The claim follows from `IsPerfectoidField.of_isAlgClosed p (by rw [← map_natCast (algebraMap K C), norm_algebraMap'] exact IsPerfectoidField.norm_natCast_lt_one)`.
-/
theorem isPerfectoidField_of_isAlgClosed_of_normedAlgebra [CompleteSpace C] :
    IsPerfectoidField C p :=
  IsPerfectoidField.of_isAlgClosed p (by
    rw [← map_natCast (algebraMap K C), norm_algebraMap']
    exact IsPerfectoidField.norm_natCast_lt_one)

variable [IsPerfectoidField C p]

/- English proof (translation)
Take `⟨N, hN, hLN⟩` from `exists_le_untiltField (p := p) L`. Establish `: PerfectField K♭` using `PerfectRing.toPerfectField K♭ p`. Take `⟨N', hNN', hN', hgal⟩` from `exists_isGalois_le N`. Take `⟨M, -, hM, hML⟩` from `exists_untiltField_eq_of_le N' L (hLN.trans (untiltField_mono hNN'))`. Conclude with `⟨M, hM, hML⟩`.
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
Take `⟨M, hM, rfl⟩` from `exists_eq_untiltField (p := p) L`. Establish `h : tiltIntermediateField p (untiltField K C p M) = M` using `tiltIntermediateField_untiltField M`. Rewrite using `[h]`. Conclude with `⟨hM, rfl⟩`.
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
Take `⟨M, hM, rfl⟩` from `exists_eq_untiltField (p := p) L`. Establish `h : tiltIntermediateField p (untiltField K C p M) = M` using `tiltIntermediateField_untiltField M`. Rewrite using `[h, finrank_untiltField]`.
-/
theorem finrank_tiltIntermediateField (L : IntermediateField K C) [FiniteDimensional K L] :
    Module.finrank K♭ (tiltIntermediateField p L) = Module.finrank K L := by
  obtain ⟨M, hM, rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M) = M :=
    tiltIntermediateField_untiltField M
  rw [h, finrank_untiltField]

/- English proof (translation)
Use `⟨untiltField K C p M, ⟨inferInstance, tiltIntermediateField_untiltField M⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `L ⟨hL, hLM⟩`. Take `⟨M', hM', rfl⟩` from `exists_eq_untiltField (p := p) L`. Establish `h : tiltIntermediateField p (untiltField K C p M') = M'` using `tiltIntermediateField_untiltField M'`. Rewrite `hLM` using `[h]`.

Rewrite using `[hLM]`.
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
Break down `IsPerfectoidField.charZero_or_charP (K := K) p with h0 | hp` into its components or cases. Use `IsPerfectoidField.completeSpace (K := K) p` as an intermediate fact. Establish `: IsPerfectoidField (CompletedAlgClosure K) p` using `isPerfectoidField_of_isAlgClosed_of_normedAlgebra K (CompletedAlgClosure K) p`. Use `set j := CompletedAlgClosure.embedding K L`. Set `e : L ≃ₐ[K] j.fieldRange` to `AlgEquiv.ofInjectiveField j`.

Establish `: FiniteDimensional K j.fieldRange` using `LinearEquiv.finiteDimensional e.toLinearEquiv`. Use `IsPerfectoidField.of_ringEquiv p e.symm.toRingEquiv fun y => ?_` and prove the remaining obligations. Establish `h1 : ((e (e.symm y) : j.fieldRange) : CompletedAlgClosure K) = j (e.symm y)` using `rfl`. Rewrite `h1` using `[AlgEquiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `‖e.symm y‖ = ‖(y : CompletedAlgClosure K)‖`.

Rewrite using `[h1, CompletedAlgClosure.norm_embedding]`. Conclude with `IsPerfectoidField.of_finiteDimensional_of_charP (K := K) p L`.
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
