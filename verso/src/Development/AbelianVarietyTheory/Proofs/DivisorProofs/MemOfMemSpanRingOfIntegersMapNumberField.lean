import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory.FlatDescent

/- English proof (translation)
Set `g : B ⊗[A] N →ₗ[B] M'` to `hf.equiv.toLinearMap ∘ₗ N.subtype.baseChange B`. Establish `hspan : Submodule.span B (f '' (N : Set M)) ≤ LinearMap.range g`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Conclude with `⟨(1 : B) ⊗ₜ[A] (⟨c, hc⟩ : N), by simp [g, IsBaseChange.equiv_tmul]⟩`.

Take `⟨x, hx⟩` from `hspan hw`. Establish `h1 : (1 : B) ⊗ₜ[A] w = N.subtype.baseChange B x`. Apply `hf.equiv.injective` to reduce the goal to its premises. Establish `: hf.equiv (N.subtype.baseChange B x) = f w` using `hx`. Rewrite using `[this, IsBaseChange.equiv_tmul, one_smul]`.

Establish `hq : N.mkQ ∘ₗ N.subtype = 0`. Use extensionality with `c`. Simplify using the standard rewrite rules. Establish `h2 : (1 : B) ⊗ₜ[A] (N.mkQ w) = 0`. Use `congrArg (N.mkQ.baseChange B) h1` as an intermediate fact.

Rewrite `this` using `[LinearMap.baseChange_tmul]`. Rewrite using `[this, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hq, LinearMap.baseChange_zero, LinearMap.zero_apply]`. Establish `h3 : N.mkQ w = 0`. Apply `Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) (M ⧸ N)` to reduce the goal to its premises. Simplify using `using h2`.

Simplify using `using h3`.
-/
theorem mem_of_mem_span_of_isBaseChange {A B M M' : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [Module B M'] [IsScalarTower A B M'] {f : M →ₗ[A] M'} (hf : IsBaseChange B f)
    (N : Submodule A M) (w : M) (hw : f w ∈ Submodule.span B (f '' (N : Set M))) : w ∈ N := by
  let g : B ⊗[A] N →ₗ[B] M' := hf.equiv.toLinearMap ∘ₗ N.subtype.baseChange B
  have hspan : Submodule.span B (f '' (N : Set M)) ≤ LinearMap.range g := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨(1 : B) ⊗ₜ[A] (⟨c, hc⟩ : N), by simp [g, IsBaseChange.equiv_tmul]⟩
  obtain ⟨x, hx⟩ := hspan hw
  have h1 : (1 : B) ⊗ₜ[A] w = N.subtype.baseChange B x := by
    apply hf.equiv.injective
    have : hf.equiv (N.subtype.baseChange B x) = f w := hx
    rw [this, IsBaseChange.equiv_tmul, one_smul]
  have hq : N.mkQ ∘ₗ N.subtype = 0 := by
    ext c
    simp
  have h2 : (1 : B) ⊗ₜ[A] (N.mkQ w) = 0 := by
    have := congrArg (N.mkQ.baseChange B) h1
    rw [LinearMap.baseChange_tmul] at this
    rw [this, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hq, LinearMap.baseChange_zero,
      LinearMap.zero_apply]
  have h3 : N.mkQ w = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) (M ⧸ N)
    simpa using h2
  simpa using h3

/- English proof (translation)
Introduce `K K' _ _ _ _ j n N w hw`. Use `letI := j.toAlgebra`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K') (nonZeroDivisors (𝓞 K))) K' := IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')`. Establish `hP : Algebra.IsPushout (𝓞 K) (𝓞 K') K K'` using `Algebra.isPushout_of_isLocalization (nonZeroDivisors (𝓞 K)) K (𝓞 K') K'`. Establish `hb : IsBaseChange (𝓞 K') ((IsScalarTower.toAlgHom (𝓞 K) K K').toLinearMap.compLeft (Fin n))` using `hP.out.finitePow (Fin n)`.

Conclude with `mem_of_mem_span_of_isBaseChange hb N w hw`.
-/
theorem mem_of_mem_span_map :
    ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (N : Submodule (𝓞 K) (Fin n → K)) (w : Fin n → K),
    (fun i => j (w i)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin n → K) i => j (c i)) '' (N : Set (Fin n → K))) → w ∈ N := by
  intro K K' _ _ _ _ j n N w hw
  letI := j.toAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K') (nonZeroDivisors (𝓞 K))) K' :=
    IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')
  have hP : Algebra.IsPushout (𝓞 K) (𝓞 K') K K' :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors (𝓞 K)) K (𝓞 K') K'
  have hb : IsBaseChange (𝓞 K')
      ((IsScalarTower.toAlgHom (𝓞 K) K K').toLinearMap.compLeft (Fin n)) :=
    hP.out.finitePow (Fin n)
  exact mem_of_mem_span_of_isBaseChange hb N w hw

end GlobalTheory.FlatDescent
