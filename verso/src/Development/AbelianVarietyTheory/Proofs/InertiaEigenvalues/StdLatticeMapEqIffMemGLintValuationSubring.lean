import Mathlib
import Formalism.SatakeDualWeyl.Statement

open Matrix

namespace GlobalTheory.GLintLattice

variable {K : Type} [Field K] (A : ValuationSubring K) {r : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem mem_span_basisFun_iff (y : Fin r → K) :
    y ∈ Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ ∀ i, y i ∈ A := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    refine ⟨fun i => ⟨y i, h i⟩, ?_⟩
    ext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem mulVec_maps_iff (M : Matrix (Fin r) (Fin r) K) :
    (∀ y : Fin r → K, (∀ i, y i ∈ A) → ∀ i, (M *ᵥ y) i ∈ A) ↔ ∀ i j, M i j ∈ A := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]) i
    simpa [Matrix.mulVec_single_one] using this
  · intro h y hy i
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem (fun j _ => mul_mem (h i j) (hy j))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem mem_GLint_iff (x : GL (Fin r) K) :
    x ∈ Formalism.UG.GLint (Fin r) A.toSubring ↔
      (∀ i j, (x : Matrix (Fin r) (Fin r) K) i j ∈ A) ∧
        (∀ i j, ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ∈ A) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show ((u : Matrix (Fin r) (Fin r) A.toSubring) i j : K) ∈ A
      exact (u : Matrix (Fin r) (Fin r) A.toSubring) i j |>.2
    · rw [← map_inv]
      show (((u⁻¹ : GL (Fin r) A.toSubring) : Matrix (Fin r) (Fin r) A.toSubring) i j : K) ∈ A
      exact ((u⁻¹ : GL (Fin r) A.toSubring) : Matrix (Fin r) (Fin r) A.toSubring) i j |>.2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin r) (Fin r) A.toSubring := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix (Fin r) (Fin r) A.toSubring := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map A.toSubring.subtype = (x : Matrix (Fin r) (Fin r) K) := by ext; rfl
    have hM' : M'.map A.toSubring.subtype = ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) := by
      ext; rfl
    have inj : Function.Injective fun N : Matrix (Fin r) (Fin r) A.toSubring => N.map A.toSubring.subtype :=
      Matrix.map_injective Subtype.val_injective
    have e1 : M * M' = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact x.mul_inv)
    have e2 : M' * M = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact x.inv_mul)
    refine ⟨⟨M, M', e1, e2⟩, ?_⟩
    ext i j
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem stdLattice_map_eq_iff_mem_GLint : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ)
    (x : GL (Fin r) K),
    (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
        ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) =
      Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔
    x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  intro K _ A r x
  have hf : ∀ z, ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) z =
      (x : Matrix (Fin r) (Fin r) K) *ᵥ z := fun z => rfl
  have inv_x : ∀ z : Fin r → K, ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ
      ((x : Matrix (Fin r) (Fin r) K) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have x_inv : ∀ z : Fin r → K, (x : Matrix (Fin r) (Fin r) K) *ᵥ
      (((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [mem_GLint_iff, ← mulVec_maps_iff, ← mulVec_maps_iff]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hm : (x : Matrix (Fin r) (Fin r) K) *ᵥ y ∈
          (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
            ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) :=
        ⟨y, (mem_span_basisFun_iff A y).2 hy, hf y⟩
      rw [h] at hm
      exact (mem_span_basisFun_iff A _).1 hm
    · have hm : y ∈ (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
            ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) := by
        rw [h]; exact (mem_span_basisFun_iff A y).2 hy
      obtain ⟨z, hz, hzy⟩ := hm
      rw [hf] at hzy
      rw [← hzy, inv_x]
      exact (mem_span_basisFun_iff A z).1 hz
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hf, mem_span_basisFun_iff]
      exact h1 z ((mem_span_basisFun_iff A z).1 hz)
    · intro y hy
      refine ⟨((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ y,
        (mem_span_basisFun_iff A _).2 (h2 y ((mem_span_basisFun_iff A y).1 hy)), ?_⟩
      rw [hf, x_inv]

end GlobalTheory.GLintLattice
