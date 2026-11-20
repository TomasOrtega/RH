import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

/- English proof (translation)
Introduce `R M W _ _ _ _ _ q n act1 actw tr hsurj hker hu`. Establish `hy : ∀ p : Fin q × Fin n, ∀ m, tr (act1 (yV R p.1 p.2) m) = 0`. Introduce `p m`. Rewrite using `[← LinearMap.mem_ker, hker]`. Conclude with `Submodule.mem_iSup_of_mem p (LinearMap.mem_range_self _ m)`.

Use `⟨fun τ => ?_, fun I m hm => ?_⟩` and prove the remaining obligations. Proceed by induction on `τ using MvPolynomial.induction_on with`. Consider the case `C a`. Introduce `m`. Rewrite using `[MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]`.

Simplify using the standard rewrite rules. Consider the case `add p r hp hr`. Introduce `m`. Simplify using `[map_add, hp, hr]`. Consider the case `mul_X p s hp`.

Introduce `m`. Break down `s with ⟨j, i⟩ | ⟨j, i⟩` into its components or cases. Rewrite using `[map_mul, Module.End.mul_apply, hp, map_mul, map_mul, Module.End.mul_apply, MvPolynomial.aeval_X, Sum.elim_inl]`. Conclude with `congrArg _ (hu j i m)`. Rewrite using `[map_mul, Module.End.mul_apply, hp, map_mul, MvPolynomial.aeval_X, Sum.elim_inr, show tr (act1 (MvPolynomial.X (Sum.inr (j, i))) m) = 0 from hy (j, i) m]`.

Simplify using the standard rewrite rules. Establish `htop : (I • ⊤ : Submodule R W) = (I • ⊤ : Submodule R M).map tr`. Rewrite using `[Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]`. Rewrite `hm` using `[htop]`. Take `⟨m', hm', he⟩` from `hm`.

Establish `hk : m - m' ∈ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2))`. Rewrite using `[← hker, LinearMap.mem_ker, map_sub, he, sub_self]`. Establish `hmm : m = m' + (m - m')` using `by abel`. Rewrite using `[hmm]`. Conclude with `Submodule.add_mem_sup hm' hk`.
-/
theorem UpperTheory.V.Th.Sp.trans :
    ∀ (R M W : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W] (q n : ℕ) (act1 : PUY R q n →ₐ[R] Module.End R M) (actw : PU R q n →ₐ[R] Module.End R W) (tr : M →ₗ[R] W), Function.Surjective tr → LinearMap.ker tr = ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) → (∀ j i m, tr (act1 (uV R j i) m) = actw (MvPolynomial.X (j, i)) (tr m)) → (∀ τ m, tr (act1 τ m) = actw (MvPolynomial.aeval (Sum.elim MvPolynomial.X 0) τ) (tr m)) ∧ ∀ (I : Ideal R) m, tr m ∈ (I • ⊤ : Submodule R W) → m ∈ (I • ⊤ : Submodule R M) ⊔ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
  intro R M W _ _ _ _ _ q n act1 actw tr hsurj hker hu
  have hy : ∀ p : Fin q × Fin n, ∀ m, tr (act1 (yV R p.1 p.2) m) = 0 := by
    intro p m
    rw [← LinearMap.mem_ker, hker]
    exact Submodule.mem_iSup_of_mem p (LinearMap.mem_range_self _ m)
  refine ⟨fun τ => ?_, fun I m hm => ?_⟩
  · induction τ using MvPolynomial.induction_on with
    | C a =>
        intro m
        rw [MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
        simp
    | add p r hp hr =>
        intro m
        simp [map_add, hp, hr]
    | mul_X p s hp =>
        intro m
        rcases s with ⟨j, i⟩ | ⟨j, i⟩
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, map_mul, Module.End.mul_apply,
            MvPolynomial.aeval_X, Sum.elim_inl]
          exact congrArg _ (hu j i m)
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, MvPolynomial.aeval_X, Sum.elim_inr,
            show tr (act1 (MvPolynomial.X (Sum.inr (j, i))) m) = 0 from hy (j, i) m]
          simp
  · have htop : (I • ⊤ : Submodule R W) = (I • ⊤ : Submodule R M).map tr := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
    rw [htop] at hm
    obtain ⟨m', hm', he⟩ := hm
    have hk : m - m' ∈ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
      rw [← hker, LinearMap.mem_ker, map_sub, he, sub_self]
    have hmm : m = m' + (m - m') := by abel
    rw [hmm]
    exact Submodule.add_mem_sup hm' hk
