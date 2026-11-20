import Mathlib

/- English proof (translation)
Introduce `R W T _ _ _ _ j`. Rewrite using `[Submodule.eq_top_iff']`. Introduce `t`. Take `⟨x, rfl⟩` from `j.surjective t`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r w`. Establish `h : r ⊗ₜ[ℤ] w = r • ((1 : R) ⊗ₜ[ℤ] w)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[h, map_smul]`.

Conclude with `Submodule.smul_mem _ r (Submodule.subset_span ⟨w, rfl⟩)`. Consider the case `add x y hx hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem UpperTheory.Reformulated.B.DYlb6.main :
    ∀ {R W T : Type} [inst : CommRing R] [inst_1 : AddCommGroup W] [inst_2 : AddCommGroup T] [inst_3 : _root_.Module R T]
      (j : TensorProduct ℤ R W ≃ₗ[R] T),
      Submodule.span R (Set.range fun (a : W) ↦ (j : TensorProduct ℤ R W → T) ((1 : R) ⊗ₜ[ℤ] a)) = ⊤ := by
  intro R W T _ _ _ _ j
  rw [Submodule.eq_top_iff']
  intro t
  obtain ⟨x, rfl⟩ := j.surjective t
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r w =>
    have h : r ⊗ₜ[ℤ] w = r • ((1 : R) ⊗ₜ[ℤ] w) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨w, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
