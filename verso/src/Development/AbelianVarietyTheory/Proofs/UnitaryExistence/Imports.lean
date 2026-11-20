import Mathlib
namespace GlobalTheory.LatticeBoundedAction

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem main {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (Λ : Submodule R V) :
    ∀ v ∈ Submodule.span K (↑Λ : Set V), ∃ (d : R), d ≠ (0 : R) ∧ d • v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h₁
    · rw [mul_smul]; exact Λ.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
    have hb : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have key : (b : R) • (c • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, ← hab, mul_comm, IsLocalization.mk'_spec, algebraMap_smul]
    refine ⟨d * b, mul_ne_zero hd hb, ?_⟩
    rw [mul_smul, key, smul_comm]
    exact Λ.smul_mem a h

end GlobalTheory.LatticeBoundedAction
