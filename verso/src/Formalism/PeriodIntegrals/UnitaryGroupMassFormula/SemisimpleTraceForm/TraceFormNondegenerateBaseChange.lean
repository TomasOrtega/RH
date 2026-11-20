import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep

namespace PI.SSAscent.UnitaryGroupMassFormula

open Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem traceFormNondegenerate_baseChange : AscendStep := by
  intro K L _ _ _ a S hK
  classical
  set f : Matrix (Fin a) (Fin a) K →+* Matrix (Fin a) (Fin a) L :=
    (algebraMap K L).mapMatrix with hf
  set P : Submodule K (Matrix (Fin a) (Fin a) K) :=
    Subalgebra.toSubmodule (Algebra.adjoin K S) with hP
  let b := Module.finBasis K P
  set m := Module.finrank K P
  let β : Fin m → Matrix (Fin a) (Fin a) K := fun i => (b i : Matrix (Fin a) (Fin a) K)
  have hβA : ∀ i, β i ∈ Algebra.adjoin K S := fun i => (b i).2
  have hspanA : ∀ x ∈ Algebra.adjoin K S, ∃ d : Fin m → K, ∑ i, d i • β i = x := by
    intro x hx
    refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 := congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : P))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1
  have hli : LinearIndependent K β :=
    b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  let G : Matrix (Fin m) (Fin m) K := Matrix.of fun i j => Matrix.trace (β i * β j)
  have hG : G.det ≠ 0 := by
    intro h0
    obtain ⟨d, hd0, hd⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hd0
    have hz : ∑ i, d i • β i = 0 := by
      apply hK
      · exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hβA i) _
      · intro y hy
        obtain ⟨e, rfl⟩ := hspanA y hy
        rw [Finset.mul_sum, trace_sum]
        apply Finset.sum_eq_zero
        intro j _
        have hj : (d ᵥ* G) j = 0 := by rw [hd]; rfl
        rw [mul_smul_comm, trace_smul, Finset.sum_mul, trace_sum]
        simp only [smul_mul_assoc, trace_smul, smul_eq_mul]
        simp only [vecMul, dotProduct, G, Matrix.of_apply] at hj
        rw [hj, mul_zero]
    funext i
    exact (Fintype.linearIndependent_iff.mp hli) d hz i

  have hfA : ∀ y ∈ Algebra.adjoin K S, f y ∈ Algebra.adjoin L (f '' S) := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap r =>
        have : f (algebraMap K _ r) = algebraMap L (Matrix (Fin a) (Fin a) L) (algebraMap K L r) := by
          ext i j
          rw [hf, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply,
            Matrix.algebraMap_matrix_apply]
          split_ifs <;> simp
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hfsmul : ∀ (c : K) (M : Matrix (Fin a) (Fin a) K), f (c • M) = algebraMap K L c • f M := by
    intro c M
    ext i j
    simp [hf]

  have hBspan : ∀ x ∈ Algebra.adjoin L (f '' S),
      x ∈ Submodule.span L (Set.range fun i => f (β i)) := by
    intro x hx
    have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin L (f '' S)) := hx
    rw [Algebra.adjoin_eq_span] at hx'
    refine (Submodule.span_le.mpr ?_) hx'
    have hcl : (Submonoid.closure (f '' S) : Set (Matrix (Fin a) (Fin a) L)) ⊆
        (Submonoid.map (f : Matrix (Fin a) (Fin a) K →* Matrix (Fin a) (Fin a) L)
          (Algebra.adjoin K S).toSubmonoid : Set _) := by
      have : Submonoid.closure (f '' S) ≤
          Submonoid.map (f : Matrix (Fin a) (Fin a) K →* Matrix (Fin a) (Fin a) L)
            (Algebra.adjoin K S).toSubmonoid := by
        rw [Submonoid.closure_le]
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨s, Algebra.subset_adjoin hs, rfl⟩
      exact this
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hcl hz
    obtain ⟨d, rfl⟩ := hspanA y hy
    show f (∑ i, d i • β i) ∈ _
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hfsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro x hx hxy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp (hBspan x hx)
  have hG' : (G.map (algebraMap K L)).det ≠ 0 := by
    have := RingHom.map_det (algebraMap K L) G
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero _).mpr hG
  have hc : c ᵥ* G.map (algebraMap K L) = 0 := by
    funext j
    have h1 := hxy (f (β j)) (hfA _ (hβA j))
    rw [Finset.sum_mul, trace_sum] at h1
    simp only [vecMul, dotProduct, Matrix.map_apply, G, Matrix.of_apply, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, trace_smul, smul_eq_mul, ← map_mul, AddMonoidHom.map_trace]
    rfl
  by_contra hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by simp)
  exact hG' (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc0, hc⟩)

end PI.SSAscent.UnitaryGroupMassFormula
