import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R K _ _ _ _ hinj k n ν ι b μ hb g hg`. Establish `hid : ∀ x : MvPolynomial (Fin k × Fin n) K, rowAct K (1 : Matrix (Fin k) (Fin k) K) x = x`. Introduce `x`. Establish `e1 : rowAct K (n` using `n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `v`. Simplify using `only [rowAct, aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single v.1]`. Simplify using the standard rewrite rules. Introduce `c _ hc`.

Simplify using `[Ne.symm hc]`. Simplify using the standard rewrite rules. Rewrite using `[e1]`. Both sides reduce to the same expression. Establish `hinvA : ∀ A : Matrix (Fin k) (Fin k) K, IsUnit A.det → ∀ x : MvPolynomial (Fin k × Fin n) K, rowAct K A (rowAct K A⁻¹ x) = x ∧ rowAct K A⁻¹ (rowAct K A x) = x`.

Introduce `A hA x`. Establish `e1` using `congrArg (fun F => F x) (h K k n A A⁻¹)`. Establish `e2` using `congrArg (fun F => F x) (h K k n A⁻¹ A)`. Simplify using `only [AlgHom.comp_apply] at e1 e2`. Rewrite `e1` using `[Matrix.nonsing_inv_mul A hA]`.

Rewrite `e2` using `[Matrix.mul_nonsing_inv A hA]`. Conclude with `⟨e1.trans (hid x), e2.trans (hid x)⟩`. Establish `hφinj : Function.Injective (map (algebraMap R K) : MvPolynomial (Fin k × Fin n) R → _)` using `MvPolynomial.map_injective _ hinj`. Set `L : MvPolynomial (Fin k × Fin n) R →ₗ[R] MvPolynomial (Fin k × Fin n) K` to `((rowAct K g⁻¹).toLinearMap.restrictScalars R).comp (mapAlgHom (Algebra.ofId R K)).toLinearMap`. Establish `hL : ∀ p, L p = rowAct K g⁻¹ (map (algebraMap R K) p)` using `fun p => rfl`.

Establish `hLinj : Function.Injective L`. Introduce `p q hpq`. Rewrite `hpq` using `[hL, hL]`. Establish `e` using `congrArg (rowAct K g) hpq`. Rewrite `e` using `[(hinvA g hg _).1, (hinvA g hg _).1]`.

Conclude with `hφinj e`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `hb.1.map' L (LinearMap.ker_eq_bot.mpr hLinj)`. Establish `e1 : Set.range (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) = L '' Set.range b`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[e1, ← Submodule.map_span, hb.2.1]`. Use extensionality with `F`. Unfold `nablaL`. Rewrite using `[Submodule.mem_map, Submodule.mem_comap, Submodule.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, rfl⟩`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Use `show map (algebraMap R K) p = rowAct K g (L p)`. Rewrite using `[hL, (hinvA g hg _).1]`.

Introduce and unpack `⟨p, hp, hpF⟩`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Establish `e : map (algebraMap R K) p = rowAct K g F` using `hpF`. Rewrite using `[hL, e, (hinvA g hg _).2]`.
-/
theorem nablaLBasis_of (h : RowActMul) : NablaLBasis := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g hg
  have hid : ∀ x : MvPolynomial (Fin k × Fin n) K, rowAct K (1 : Matrix (Fin k) (Fin k) K) x = x := by
    intro x
    have e1 : rowAct K (n := n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [rowAct, aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single v.1]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    rw [e1]
    rfl
  have hinvA : ∀ A : Matrix (Fin k) (Fin k) K, IsUnit A.det → ∀ x : MvPolynomial (Fin k × Fin n) K,
      rowAct K A (rowAct K A⁻¹ x) = x ∧ rowAct K A⁻¹ (rowAct K A x) = x := by
    intro A hA x
    have e1 := congrArg (fun F => F x) (h K k n A A⁻¹)
    have e2 := congrArg (fun F => F x) (h K k n A⁻¹ A)
    simp only [AlgHom.comp_apply] at e1 e2
    rw [Matrix.nonsing_inv_mul A hA] at e1
    rw [Matrix.mul_nonsing_inv A hA] at e2
    exact ⟨e1.trans (hid x), e2.trans (hid x)⟩
  have hφinj : Function.Injective (map (algebraMap R K) : MvPolynomial (Fin k × Fin n) R → _) :=
    MvPolynomial.map_injective _ hinj
  let L : MvPolynomial (Fin k × Fin n) R →ₗ[R] MvPolynomial (Fin k × Fin n) K :=
    ((rowAct K g⁻¹).toLinearMap.restrictScalars R).comp (mapAlgHom (Algebra.ofId R K)).toLinearMap
  have hL : ∀ p, L p = rowAct K g⁻¹ (map (algebraMap R K) p) := fun p => rfl
  have hLinj : Function.Injective L := by
    intro p q hpq
    rw [hL, hL] at hpq
    have e := congrArg (rowAct K g) hpq
    rw [(hinvA g hg _).1, (hinvA g hg _).1] at e
    exact hφinj e
  refine ⟨?_, ?_⟩
  · exact hb.1.map' L (LinearMap.ker_eq_bot.mpr hLinj)
  · have e1 : Set.range (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) = L '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, hb.2.1]
    ext F
    unfold nablaL
    rw [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      show map (algebraMap R K) p = rowAct K g (L p)
      rw [hL, (hinvA g hg _).1]
    · rintro ⟨p, hp, hpF⟩
      refine ⟨p, hp, ?_⟩
      have e : map (algebraMap R K) p = rowAct K g F := hpF
      rw [hL, e, (hinvA g hg _).2]

end Formalism.GradedWeylDivisibility
