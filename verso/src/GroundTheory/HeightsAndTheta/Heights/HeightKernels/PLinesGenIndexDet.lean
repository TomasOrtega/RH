import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexDet

/- English proof (translation)
The claim follows from `Submodule.fg_span (Set.finite_range b) span_eq_top := by rw [Submodule.span_span_of_tower, b.span_eq]`.
-/
theorem span_basis_isLattice {V : Type} [AddCommGroup V] [Module ℚ V] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ V) : Submodule.IsLattice ℚ (Submodule.span ℤ (Set.range b)) where
  fg := Submodule.fg_span (Set.finite_range b)
  span_eq_top := by rw [Submodule.span_span_of_tower, b.span_eq]

end KLinesGenIndexDet

open KLinesGenIndexDet in

/- English proof (translation)
Introduce `V _ _ _ ι _ _ bA bB A B hA hB`. Use `set MA := Submodule.span ℤ (Set.range bA)`. Use `set MB := Submodule.span ℤ (Set.range bB)`. Use `span_basis_isLattice bA` as an intermediate fact. Use `span_basis_isLattice bB` as an intermediate fact.

Take `⟨bE, hE⟩` from `h1 V ι (Module.finrank_eq_card_basis bA).symm (MA ⊓ MB) inferInstance`. Establish `hAB : A ⊓ B = AddSubgroup.closure (Set.range bE)`. Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure, ← hE, hA, hB, ← Submodule.span_int_eq_addSubgroupClosure, ← Submodule.span_int_eq_addSubgroupClosure]`. Both sides reduce to the same expression. Establish `hBA : B ⊓ A = AddSubgroup.closure (Set.range bE)` using `by rw [inf_comm, hAB]`.

Establish `e1 : ((B.relIndex A : ℕ) : ℚ) = |bA.det bE|`. Rewrite using `[← AddSubgroup.inf_relIndex_right]`. Conclude with `AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bA hBA hA`. Establish `e2 : ((A.relIndex B : ℕ) : ℚ) = |bB.det bE|`. Rewrite using `[← AddSubgroup.inf_relIndex_right]`.

Conclude with `AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bB hAB hB`. Establish `hne : bB.det bE ≠ 0` using `(bB.isUnit_det bE).ne_zero`. Establish `key : (B.relIndex A : ℚ) / (A.relIndex B : ℚ) = |bA.det bB|`. Rewrite using `[e1, e2, ← bA.det_mul_det bB bE, abs_mul, mul_div_assoc, div_self (abs_ne_zero.mpr hne), mul_one]`. Unfold `genIndex`.

Use `congrArg (fun q : ℚ => (q : ℝ)) key` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.
-/
theorem LinesGenIndexDet.proof (h1 : LinesLatticeBasis.Statement) : LinesGenIndexDet.Statement := by
  intro V _ _ _ ι _ _ bA bB A B hA hB
  set MA := Submodule.span ℤ (Set.range bA)
  set MB := Submodule.span ℤ (Set.range bB)
  have := span_basis_isLattice bA
  have := span_basis_isLattice bB
  obtain ⟨bE, hE⟩ := h1 V ι (Module.finrank_eq_card_basis bA).symm (MA ⊓ MB) inferInstance
  have hAB : A ⊓ B = AddSubgroup.closure (Set.range bE) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, ← hE, hA, hB,
      ← Submodule.span_int_eq_addSubgroupClosure, ← Submodule.span_int_eq_addSubgroupClosure]
    rfl
  have hBA : B ⊓ A = AddSubgroup.closure (Set.range bE) := by rw [inf_comm, hAB]
  have e1 : ((B.relIndex A : ℕ) : ℚ) = |bA.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bA hBA hA
  have e2 : ((A.relIndex B : ℕ) : ℚ) = |bB.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bB hAB hB
  have hne : bB.det bE ≠ 0 := (bB.isUnit_det bE).ne_zero
  have key : (B.relIndex A : ℚ) / (A.relIndex B : ℚ) = |bA.det bB| := by
    rw [e1, e2, ← bA.det_mul_det bB bE, abs_mul, mul_div_assoc, div_self (abs_ne_zero.mpr hne),
      mul_one]
  unfold genIndex
  have := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at this
  exact this

end GroundTheory.Heights₂.Heights
