import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `c y`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
private theorem semi_symm {σ : ℂ ≃+* ℂ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {e : V ≃+ V'} (h : IsSemi σ e) : IsSemi σ.symm e.symm := by
  intro c y
  apply e.injective
  rw [h]
  simp

/- English proof (translation)
Use `⟨Module.Basis.ofRepr { toFun := fun y => Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y)) invFun := fun f => e (b.repr.symm (Finsupp.mapRange σ.symm (map_zero _) f)) map_add' := fun x y => by` and prove the remaining obligations. Use extensionality with `i`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := fun c y => by`. Use extensionality with `i`.

Establish `hs` using `semi_symm h c y`. Simplify using `[hs]`. Use `left_inv := fun y => by`. Establish `hr : Finsupp.mapRange σ.symm (map_zero _) (Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))) = b.repr (e.symm y)`. Use extensionality with `i`.

Simplify using the standard rewrite rules. Simplify using `only [hr, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]`. Use `right_inv := fun f => by`. Use extensionality with `i`. Simplify using `}, ?_⟩`.

Introduce `y i`. Both sides reduce to the same expression.
-/
private theorem exists_basis {σ : ℂ ≃+* ℂ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {e : V ≃+ V'} (h : IsSemi σ e) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) :
    ∃ b' : Module.Basis ι ℂ V', ∀ y i, b'.repr y i = σ (b.repr (e.symm y) i) := by
  refine ⟨Module.Basis.ofRepr
    { toFun := fun y => Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))
      invFun := fun f => e (b.repr.symm (Finsupp.mapRange σ.symm (map_zero _) f))
      map_add' := fun x y => by
        ext i
        simp
      map_smul' := fun c y => by
        ext i
        have hs := semi_symm h c y
        simp [hs]
      left_inv := fun y => by
        have hr : Finsupp.mapRange σ.symm (map_zero _)
            (Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))) = b.repr (e.symm y) := by
          ext i
          simp
        simp only [hr, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun f => by
        ext i
        simp }, ?_⟩
  intro y i
  rfl

/- English proof (translation)
Introduce `σ V V' _ _ _ _ e h T T' hT`. Distinguish the cases in `H : ∃ s : Finset V, Nonempty (Module.Basis s ℂ V)`. Take `⟨s, ⟨b⟩⟩` from `H`. Take `⟨b', hb'⟩` from `exists_basis h b`. Establish `hbj : ∀ j, b' j = e (b j)`.

Introduce `j`. Apply `b'.repr.injective` to reduce the goal to its premises. Rewrite using `[b'.repr_self]`. Use extensionality with `k`. Rewrite using `[hb', AddEquiv.symm_apply_apply, b.repr_self]`.

Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, hjk]`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b', Matrix.trace, Matrix.trace, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.diag_apply, LinearMap.toMatrix_apply, hbj, hb', ← hT, AddEquiv.symm_apply_apply]`. Establish `H' : ¬ ∃ t : Finset V', Nonempty (Module.Basis t ℂ V')`. Introduce and unpack `⟨t, ⟨c⟩⟩`. Take `⟨c', -⟩` from `exists_basis (semi_symm h) c`.

Conclude with `H ⟨_, ⟨c'.reindexFinsetRange⟩⟩`. Simplify using `only [LinearMap.trace, dif_neg H, dif_neg H', LinearMap.zero_apply, map_zero]`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.traceSemi_of :
    TraceSemi := by
  intro σ V V' _ _ _ _ e h T T' hT
  classical
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s ℂ V)
  · obtain ⟨s, ⟨b⟩⟩ := H
    obtain ⟨b', hb'⟩ := exists_basis h b
    have hbj : ∀ j, b' j = e (b j) := by
      intro j
      apply b'.repr.injective
      rw [b'.repr_self]
      ext k
      rw [hb', AddEquiv.symm_apply_apply, b.repr_self]
      by_cases hjk : j = k
      · subst hjk
        simp
      · simp [Finsupp.single_apply, hjk]
    rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b', Matrix.trace,
      Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, hbj, hb', ← hT,
      AddEquiv.symm_apply_apply]
  · have H' : ¬ ∃ t : Finset V', Nonempty (Module.Basis t ℂ V') := by
      rintro ⟨t, ⟨c⟩⟩
      obtain ⟨c', -⟩ := exists_basis (semi_symm h) c
      exact H ⟨_, ⟨c'.reindexFinsetRange⟩⟩
    simp only [LinearMap.trace, dif_neg H, dif_neg H', LinearMap.zero_apply, map_zero]
