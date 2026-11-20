import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

namespace GlobalTheory.EigenSplit

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r b => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]`. Consider the case `add s t hs ht => simp only [map_add, hs, ht, add_mul]`.
-/
theorem baseChangeAction_toModuleEnd_self_apply {O R : Type} [CommRing O] [CommRing R] (a : O)
    (t : R ⊗[ℤ] O) :
    baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O) a t = t * (1 ⊗ₜ a) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add s t hs ht => simp only [map_add, hs, ht, add_mul]

/- English proof (translation)
Use `set ρO := (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)`. Use `set ρ := (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)`. Establish `hact : ∀ a, baseChangeAction R ρ a = tensorAction (baseChangeAction R ρ) (1 ⊗ₜ a)`. Introduce `a`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' O Λ`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`.

Set `F : Fin n → R ⊗[ℤ] Λ →ₗ[R] R ⊗[ℤ] O` to `fun k => (((LinearMap.proj k : (Fin n → O) →ₗ[O] O) ∘ₗ s).restrictScalars ℤ).baseChange R`. Set `lam : Fin n → Λ` to `fun k => π (Pi.single k 1)`. Establish `hsum : ∀ l, ∑ k, s l k • lam k = l`. Introduce `l`. Establish `h1` using `LinearMap.congr_fun hs l`.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at h1`. Use `conv_rhs => rw [← h1]`. Rewrite using `[← Finset.univ_sum_single (s l), map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [lam, ← map_smul]`.

Use `congr 1`. Use extensionality with `j`. Apply the tactic sequence `by_cases hj : j = k <;> simp [Pi.single_apply, hj]`. Establish `hid : ∀ y, y = ∑ k, tensorAction (baseChangeAction R ρ) (F k y) (1 ⊗ₜ lam k)`. Introduce `y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r l`. Simplify using `only [F, LinearMap.baseChange_tmul, tensorAction_tmul, baseChangeAction_apply, LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.proj_apply]`. Simplify using `[ρ, ← TensorProduct.tmul_sum, hsum, TensorProduct.smul_tmul']`.

Consider the case `add y z hy hz => conv_lhs => rw [hy, hz]`. Simplify using `only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]`. Establish `hF : ∀ k, IsEquivariant (baseChangeAction R ρ) (baseChangeAction R ρO) (F k)`. Introduce `k a y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r l => simp [F, ρ, ρO]`. Consider the case `add y z hy hz => simp only [map_add, hy, hz]`. Establish `hc : ∀ k, ∃ c : R, c • e = F k x` using `fun k => Submodule.mem_span_singleton.1 (hspan ((hF k).map_mem hx))`. Use `choose c hc using hc`.

Use `⟨∑ k, c k • (1 ⊗ₜ lam k), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `conv_rhs => rw [hid x]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← hc k, map_smul, map_smul, LinearMap.smul_apply]`.

Introduce and unpack `_ ⟨m, rfl⟩`. Use `mem_eigenSub.2 fun a => ?_` and prove the remaining obligations. Rewrite using `[hact a, ← Module.End.mul_apply, ← map_mul, mul_comm, ← baseChangeAction_toModuleEnd_self_apply, mem_eigenSub.1 he a, map_smul, LinearMap.smul_apply]`.
-/
theorem eigenSub_eq_range_tensorAction_of_le_span {O R Λ : Type} [CommRing O] [CommRing R]
    [AddCommGroup Λ] [Module O Λ] [Module.Finite O Λ] [Module.Projective O Λ] (χ : O →+* R)
    (e : R ⊗[ℤ] O)
    (he : e ∈ eigenSub (baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)) χ)
    (hspan : eigenSub (baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)) χ
      ≤ Submodule.span R {e}) :
    eigenSub (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) χ
      = LinearMap.range
          (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) := by
  set ρO := (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)
  set ρ := (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)
  have hact : ∀ a, baseChangeAction R ρ a = tensorAction (baseChangeAction R ρ) (1 ⊗ₜ a) := by
    intro a; ext y; simp
  apply le_antisymm
  · intro x hx
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' O Λ
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    let F : Fin n → R ⊗[ℤ] Λ →ₗ[R] R ⊗[ℤ] O := fun k =>
      (((LinearMap.proj k : (Fin n → O) →ₗ[O] O) ∘ₗ s).restrictScalars ℤ).baseChange R
    let lam : Fin n → Λ := fun k => π (Pi.single k 1)
    have hsum : ∀ l, ∑ k, s l k • lam k = l := by
      intro l
      have h1 := LinearMap.congr_fun hs l
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
      conv_rhs => rw [← h1]
      rw [← Finset.univ_sum_single (s l), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lam, ← map_smul]
      congr 1
      ext j
      by_cases hj : j = k <;> simp [Pi.single_apply, hj]
    have hid : ∀ y, y = ∑ k, tensorAction (baseChangeAction R ρ) (F k y) (1 ⊗ₜ lam k) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r l =>
        simp only [F, LinearMap.baseChange_tmul, tensorAction_tmul, baseChangeAction_apply,
          LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.proj_apply]
        simp [ρ, ← TensorProduct.tmul_sum, hsum, TensorProduct.smul_tmul']
      | add y z hy hz =>
        conv_lhs => rw [hy, hz]
        simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
    have hF : ∀ k, IsEquivariant (baseChangeAction R ρ) (baseChangeAction R ρO) (F k) := by
      intro k a y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r l => simp [F, ρ, ρO]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hc : ∀ k, ∃ c : R, c • e = F k x := fun k =>
      Submodule.mem_span_singleton.1 (hspan ((hF k).map_mem hx))
    choose c hc using hc
    refine ⟨∑ k, c k • (1 ⊗ₜ lam k), ?_⟩
    rw [map_sum]
    conv_rhs => rw [hid x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hc k, map_smul, map_smul, LinearMap.smul_apply]
  · rintro _ ⟨m, rfl⟩
    refine mem_eigenSub.2 fun a => ?_
    rw [hact a, ← Module.End.mul_apply, ← map_mul, mul_comm,
      ← baseChangeAction_toModuleEnd_self_apply, mem_eigenSub.1 he a, map_smul, LinearMap.smul_apply]

end GlobalTheory.EigenSplit
