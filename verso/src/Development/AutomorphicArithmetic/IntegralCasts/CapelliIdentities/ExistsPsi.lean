import Mathlib

/- English proof (translation)
Introduce `L T _ _ _ _ _ m hm`. Use `letI : Field (T ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Module.Finite L (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing L (T ⧸ m)`. Establish `hb : Function.Bijective (Algebra.ofId L (T ⧸ m))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e : L ≃ₐ[L] (T ⧸ m)` to `AlgEquiv.ofBijective (Algebra.ofId L (T ⧸ m)) hb`.

Use `⟨(e.symm : (T ⧸ m) →ₐ[L] L).comp (Ideal.Quotient.mkₐ L m), fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e.symm (Ideal.Quotient.mk m x) = 0 ↔ x ∈ m`. Rewrite using `[map_eq_zero_iff e.symm e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem UpperTheory.Reformulated.B.Qi48.exists_psi :
    ∀ (L T : Type) [inst : Field L] [IsAlgClosed L] [inst_2 : CommRing T]
    [inst_3 : Algebra L T] [Algebra.FiniteType L T] (m : Ideal T),
    m.IsMaximal → ∃ (ψ : T →ₐ[L] L), ∀ (x : T), (ψ : T → L) x = (0 : L) ↔ x ∈ m := by
  intro L T _ _ _ _ _ m hm
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite L (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing L (T ⧸ m)
  have hb : Function.Bijective (Algebra.ofId L (T ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : L ≃ₐ[L] (T ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId L (T ⧸ m)) hb
  refine ⟨(e.symm : (T ⧸ m) →ₐ[L] L).comp (Ideal.Quotient.mkₐ L m), fun x => ?_⟩
  change e.symm (Ideal.Quotient.mk m x) = 0 ↔ x ∈ m
  rw [map_eq_zero_iff e.symm e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
