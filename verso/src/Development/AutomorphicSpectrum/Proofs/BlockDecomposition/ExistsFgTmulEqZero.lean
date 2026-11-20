import Mathlib

open TensorProduct

namespace GlobalTheory.CompanionTheory.EqCrit

/- English proof (translation)
Establish `h' : z ⊗ₜ[A] (1 : B) = 0`. Use `congrArg (TensorProduct.comm A B Q) h` as an intermediate fact. Rewrite `this` using `[TensorProduct.comm_tmul, map_zero]`. Then use the resulting hypothesis. Set `N0 : {N : Submodule A Q // N.FG}` to `⟨Submodule.span A {z}, Submodule.fg_span_singleton z⟩`. Establish `hz0 : z ∈ (N0 : Submodule A Q)` using `Submodule.mem_span_singleton_self z`.

Establish `he : (Module.fgSystem.equiv A Q).symm z = Module.DirectLimit.of A {N : Submodule A Q // N.FG} (fun i => ↥(i : Submodule A Q)) (Module.fgSystem A Q) N0 ⟨z, hz0⟩`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Use `congrArg (fun f => f ⟨z, hz0⟩) (Module.fgSystem.equiv_comp_of (R := A) (M := Q) N0)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply] at this`. Conclude with `this.symm`.

Establish `h2 : (TensorProduct.directLimitLeft (Module.fgSystem A Q) B) ((LinearMap.rTensor B ((Module.fgSystem.equiv A Q).symm : Q →ₗ[A] _)) (z ⊗ₜ[A] (1 : B))) = 0`. Rewrite using `[h', map_zero, map_zero]`. Rewrite `h2` using `[LinearMap.rTensor_tmul, LinearEquiv.coe_coe, he, TensorProduct.directLimitLeft_tmul_of]`. Use `haveI : DirectedSystem (fun i : {N : Submodule A Q // N.FG} => TensorProduct A (↥(i : Submodule A Q)) B) (fun i j h => ⇑(LinearMap.rTensor B (Module.fgSystem A Q i j h))) := DirectedSystem.rTensor A B (f := fun ⦃i j⦄ h => Module.fgSystem A Q i j h) inferInstance`. Take `⟨j, hij, hj⟩` from `Module.DirectLimit.of.zero_exact h2`.

Use `⟨(j : Submodule A Q), (show (N0 : Submodule A Q) ≤ j from hij) hz0, j.2, ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[LinearMap.rTensor_tmul]`. Conclude with `hj`.
-/
theorem exists_fg_tmul_eq_zero {A : Type} [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    {Q : Type} [AddCommGroup Q] [Module A Q] (z : Q) (h : (1 : B) ⊗ₜ[A] z = 0) :
    ∃ (Q' : Submodule A Q) (hz : z ∈ Q'), Q'.FG ∧ (⟨z, hz⟩ : Q') ⊗ₜ[A] (1 : B) = 0 := by
  classical
  have h' : z ⊗ₜ[A] (1 : B) = 0 := by
    have := congrArg (TensorProduct.comm A B Q) h
    rwa [TensorProduct.comm_tmul, map_zero] at this
  let N0 : {N : Submodule A Q // N.FG} := ⟨Submodule.span A {z}, Submodule.fg_span_singleton z⟩
  have hz0 : z ∈ (N0 : Submodule A Q) := Submodule.mem_span_singleton_self z
  have he : (Module.fgSystem.equiv A Q).symm z =
      Module.DirectLimit.of A {N : Submodule A Q // N.FG} (fun i => ↥(i : Submodule A Q))
        (Module.fgSystem A Q) N0 ⟨z, hz0⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    have := congrArg (fun f => f ⟨z, hz0⟩) (Module.fgSystem.equiv_comp_of (R := A) (M := Q) N0)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply] at this
    exact this.symm
  have h2 : (TensorProduct.directLimitLeft (Module.fgSystem A Q) B)
      ((LinearMap.rTensor B ((Module.fgSystem.equiv A Q).symm : Q →ₗ[A] _)) (z ⊗ₜ[A] (1 : B))) = 0 := by
    rw [h', map_zero, map_zero]
  rw [LinearMap.rTensor_tmul, LinearEquiv.coe_coe, he, TensorProduct.directLimitLeft_tmul_of] at h2
  haveI : DirectedSystem (fun i : {N : Submodule A Q // N.FG} => TensorProduct A (↥(i : Submodule A Q)) B)
      (fun i j h => ⇑(LinearMap.rTensor B (Module.fgSystem A Q i j h))) :=
    DirectedSystem.rTensor A B (f := fun ⦃i j⦄ h => Module.fgSystem A Q i j h) inferInstance
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact h2
  refine ⟨(j : Submodule A Q), (show (N0 : Submodule A Q) ≤ j from hij) hz0, j.2, ?_⟩
  rw [LinearMap.rTensor_tmul] at hj
  exact hj

/- English proof (translation)
Take `⟨Q', hz, hfg, hzero⟩` from `exists_fg_tmul_eq_zero B z h`. Use `haveI : Module.Finite A Q' := Module.Finite.iff_fg.mpr hfg`. Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' A Q'`. Take `⟨w, hw⟩` from `hπ ⟨z, hz⟩`. Establish `hex` using `lTensor_exact B (LinearMap.exact_subtype_ker_map π) hπ`.

Establish `h1 : LinearMap.lTensor B π ((1 : B) ⊗ₜ[A] w) = 0`. Rewrite using `[LinearMap.lTensor_tmul, hw]`. Use `congrArg (TensorProduct.comm A Q' B) hzero` as an intermediate fact. Rewrite `this` using `[TensorProduct.comm_tmul, map_zero]`. Then use the resulting hypothesis. Take `⟨x, hx⟩` from `(hex ((1 : B) ⊗ₜ[A] w)).mp h1`.

Take `⟨S, hS⟩` from `TensorProduct.exists_finset x`. Set `e` to `S.equivFin`. Set `b : Fin S.card → B` to `fun t => (e.symm t : B × LinearMap.ker π).1`. Set `kk : Fin S.card → LinearMap.ker π` to `fun t => (e.symm t : B × LinearMap.ker π).2`. Establish `hxsum : x = ∑ t, b t ⊗ₜ[A] kk t`.

Rewrite using `[hS, ← Finset.sum_coe_sort, ← Equiv.sum_comp e.symm]`. Establish `hx' : ∑ t, b t ⊗ₜ[A] (kk t : Fin n → A) = (1 : B) ⊗ₜ[A] w`. Rewrite using `[← hx, hxsum, map_sum]`. Simplify using `only [LinearMap.lTensor_tmul, Submodule.subtype_apply]`. Use `⟨n, S.card, fun s t => (kk t : Fin n → A) s, w, ⟨b, fun s => ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `hvec` using `congrFun (congrArg (TensorProduct.piScalarRight A B B (Fin n)) hx') s`. Simplify using `only [map_sum, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Finset.sum_apply] at hvec`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `hvec`. Introduce `B₁ _ _ hy`.

Take `⟨y, hy⟩` from `hy`. Establish `h2 : ∑ t, y t ⊗ₜ[A] (kk t : Fin n → A) = (1 : B₁) ⊗ₜ[A] w`. Apply `(TensorProduct.piScalarRight A B₁ B₁ (Fin n)).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `s`. Simplify using `only [map_sum, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Finset.sum_apply]`.

Rewrite using `[← Algebra.algebraMap_eq_smul_one]`. Conclude with `hy s`. Establish `h3` using `congrArg (LinearMap.lTensor B₁ (Q'.subtype ∘ₗ π)) h2`. Establish `hk : ∀ t, π (kk t : Fin n → A) = 0` using `fun t => LinearMap.mem_ker.mp (kk t).2`. Simplify using `only [map_sum, LinearMap.lTensor_tmul, LinearMap.comp_apply, hk, hw, map_zero, TensorProduct.tmul_zero, Finset.sum_const_zero, Submodule.subtype_apply] at h3`.

Conclude with `h3.symm`.
-/
theorem exists_system {A : Type} [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    {Q : Type} [AddCommGroup Q] [Module A Q] (z : Q) (h : (1 : B) ⊗ₜ[A] z = 0) :
    ∃ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A),
      (∃ y : Fin n → B, ∀ t, ∑ j, a t j • y j = algebraMap A B (c t)) ∧
      ∀ (B₁ : Type) [CommRing B₁] [Algebra A B₁],
        (∃ y : Fin n → B₁, ∀ t, ∑ j, a t j • y j = algebraMap A B₁ (c t)) →
          (1 : B₁) ⊗ₜ[A] z = 0 := by
  classical
  obtain ⟨Q', hz, hfg, hzero⟩ := exists_fg_tmul_eq_zero B z h
  haveI : Module.Finite A Q' := Module.Finite.iff_fg.mpr hfg
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A Q'
  obtain ⟨w, hw⟩ := hπ ⟨z, hz⟩
  have hex := lTensor_exact B (LinearMap.exact_subtype_ker_map π) hπ
  have h1 : LinearMap.lTensor B π ((1 : B) ⊗ₜ[A] w) = 0 := by
    rw [LinearMap.lTensor_tmul, hw]
    have := congrArg (TensorProduct.comm A Q' B) hzero
    rwa [TensorProduct.comm_tmul, map_zero] at this
  obtain ⟨x, hx⟩ := (hex ((1 : B) ⊗ₜ[A] w)).mp h1
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  let e := S.equivFin
  let b : Fin S.card → B := fun t => (e.symm t : B × LinearMap.ker π).1
  let kk : Fin S.card → LinearMap.ker π := fun t => (e.symm t : B × LinearMap.ker π).2
  have hxsum : x = ∑ t, b t ⊗ₜ[A] kk t := by
    rw [hS, ← Finset.sum_coe_sort, ← Equiv.sum_comp e.symm]
  have hx' : ∑ t, b t ⊗ₜ[A] (kk t : Fin n → A) = (1 : B) ⊗ₜ[A] w := by
    rw [← hx, hxsum, map_sum]
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
  refine ⟨n, S.card, fun s t => (kk t : Fin n → A) s, w, ⟨b, fun s => ?_⟩, ?_⟩
  · have hvec := congrFun (congrArg (TensorProduct.piScalarRight A B B (Fin n)) hx') s
    simp only [map_sum, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Finset.sum_apply] at hvec
    rw [Algebra.algebraMap_eq_smul_one]
    exact hvec
  · intro B₁ _ _ hy
    obtain ⟨y, hy⟩ := hy
    have h2 : ∑ t, y t ⊗ₜ[A] (kk t : Fin n → A) = (1 : B₁) ⊗ₜ[A] w := by
      apply (TensorProduct.piScalarRight A B₁ B₁ (Fin n)).injective
      funext s
      simp only [map_sum, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Finset.sum_apply]
      rw [← Algebra.algebraMap_eq_smul_one]
      exact hy s
    have h3 := congrArg (LinearMap.lTensor B₁ (Q'.subtype ∘ₗ π)) h2
    have hk : ∀ t, π (kk t : Fin n → A) = 0 := fun t => LinearMap.mem_ker.mp (kk t).2
    simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.comp_apply, hk, hw, map_zero,
      TensorProduct.tmul_zero, Finset.sum_const_zero, Submodule.subtype_apply] at h3
    exact h3.symm

end GlobalTheory.CompanionTheory.EqCrit
