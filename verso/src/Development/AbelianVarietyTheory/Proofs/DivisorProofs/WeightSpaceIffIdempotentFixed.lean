import Mathlib
open scoped TensorProduct
universe u

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ C _ M _ _ _ _ _ χ e he he1 hnil m`. Use `set φ : k ⊗[ℤ] C →ₐ[k] k := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) with hφ`. Establish `hφt : ∀ (x : k) (c : C), φ (x ⊗ₜ[ℤ] c) = x * χ c`. Introduce `x c`. Simplify using `[hφ]`.

Set `ρ : k ⊗[ℤ] C →ₐ[k] Module.End k M` to `Algebra.lsmul k k M`. Set `T : C → k ⊗[ℤ] C` to `fun c => (1 : k) ⊗ₜ[ℤ] c - algebraMap k (k ⊗[ℤ] C) (χ c)`. Establish `hφT : ∀ c, φ (T c) = 0`. Introduce `c`. Simplify using `[T, hφt, AlgHom.commutes]`.

Establish `hρT : ∀ c, ρ (T c) = DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c) - χ c • (1 : Module.End k M)`. Introduce `c`. Simplify using `only [T]`. Rewrite using `[map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]`. Both sides reduce to the same expression.

Prove the components needed by the constructor for the conclusion. Introduce `hm set X := ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c) with hX`. Establish `hstab : ∀ (a : k ⊗[ℤ] C) (x : M), x ∈ X → a • x ∈ X`. Introduce `a x hx`. Rewrite `hx`, the goal using `[hX, Submodule.mem_iInf]`.

Introduce `c`. Establish `hc : Commute (ρ ((1 : k) ⊗ₜ[ℤ] c)) (ρ a)` using `(Commute.all _ _).map ρ`. Conclude with `Module.End.mapsTo_maxGenEigenspace_of_comm hc (χ c) (hx c)`. Set `X' : Submodule (k ⊗[ℤ] C) M` to `{ carrier := X add_mem' := fun ha hb => X.add_mem ha hb zero_mem' := X.zero_mem smul_mem' := fun a x hx => hstab a x hx }`. Set `ρX : k ⊗[ℤ] C →ₐ[k] Module.End k X'` to `Algebra.lsmul k k X'`.

Establish `hT : ∀ c, IsNilpotent (ρX (T c))`. Introduce `c`. Use `⟨Module.End.maxGenEigenspaceIndex (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c), ?_⟩` and prove the remaining obligations. Use extensionality with `⟨x, hx⟩`. Establish `hx' : x ∈ Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c)` using `(Submodule.mem_iInf _).1 hx c`.

Rewrite `hx'` using `[Module.End.maxGenEigenspace_eq, Module.End.mem_genEigenspace_nat]`. Rewrite `hx'` using `[← hρT, ← map_pow]`. Rewrite `hx'` using `[LinearMap.mem_ker]`. Rewrite using `[← map_pow, LinearMap.zero_apply]`. Conclude with `hx'`.

Establish `hall : ∀ a, IsNilpotent (ρX (a - algebraMap k (k ⊗[ℤ] C) (φ a)))`. Introduce `a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x c`.

Establish `: x ⊗ₜ[ℤ] c - algebraMap k (k ⊗[ℤ] C) (φ (x ⊗ₜ[ℤ] c)) = x • T c`. Simplify using `only [T, hφt, smul_sub, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]`. Simplify using the standard rewrite rules. Rewrite using `[this, map_smul]`.

Conclude with `(hT c).smul x`. Consider the case `add a b ha hb`. Establish `: a + b - algebraMap k (k ⊗[ℤ] C) (φ (a + b)) = (a - algebraMap k (k ⊗[ℤ] C) (φ a)) + (b - algebraMap k (k ⊗[ℤ] C) (φ b))`. Rewrite using `[map_add, map_add]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this, map_add]`. Conclude with `Commute.isNilpotent_add ((Commute.all _ _).map ρX) ha hb`. Establish `h1e : IsNilpotent (ρX (1 - e))`. Use `hall (1 - e)` as an intermediate fact. Rewrite `this` using `[show φ (1 - e) = 0 by rw [map_sub, map_one, he1, sub_self], map_zero, sub_zero]`. Then use the resulting hypothesis.

Establish `hid : IsIdempotentElem (ρX (1 - e))` using `he.one_sub.map ρX`. Establish `h0` using `hid.eq_zero_of_isNilpotent h1e`. Use `congrArg (fun f => (f ⟨m, hm⟩ : X')) h0` as an intermediate fact. Simplify using `only [LinearMap.zero_apply] at this`. Use `congrArg Subtype.val this` as an intermediate fact.

Express the relevant statement in the definitionally equal form `(1 - e) • m = 0 at this`. Rewrite `this` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `this.symm`. Introduce `hm`. Rewrite using `[Submodule.mem_iInf]`.

Introduce `c`. Rewrite using `[Module.End.mem_maxGenEigenspace]`. Take `⟨n, hn⟩` from `hnil (T c) (hφT c)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hen : ∀ j : ℕ, e ^ j • m = m`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ, mul_smul, hm, ih]`. Rewrite using `[← hρT, ← map_pow]`.

Express the relevant statement in the definitionally equal form `T c ^ n • m = 0`. Rewrite using `[← hen n, smul_smul, mul_comm, ← mul_pow, hn, zero_smul]`.
-/
theorem weightSpace_iff_idempotent_fixed : ∀ (k : Type) [Field k] (C : Type) [CommRing C] (M : Type u) [AddCommGroup M] [Module k M] [Module (k ⊗[ℤ] C) M] [IsScalarTower k (k ⊗[ℤ] C) M] [FiniteDimensional k M] (χ : C →+* k) (e : k ⊗[ℤ] C), IsIdempotentElem e → (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) e = 1 → (∀ a, (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) a = 0 → IsNilpotent (e * a)) → ∀ m : M, m ∈ (⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c)) ↔ e • m = m := by
  intro k _ C _ M _ _ _ _ _ χ e he he1 hnil m
  set φ : k ⊗[ℤ] C →ₐ[k] k := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) with hφ
  have hφt : ∀ (x : k) (c : C), φ (x ⊗ₜ[ℤ] c) = x * χ c := by
    intro x c
    simp [hφ]
  let ρ : k ⊗[ℤ] C →ₐ[k] Module.End k M := Algebra.lsmul k k M
  let T : C → k ⊗[ℤ] C := fun c => (1 : k) ⊗ₜ[ℤ] c - algebraMap k (k ⊗[ℤ] C) (χ c)
  have hφT : ∀ c, φ (T c) = 0 := by
    intro c
    simp [T, hφt, AlgHom.commutes]
  have hρT : ∀ c, ρ (T c) = DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c) - χ c • (1 : Module.End k M) := by
    intro c
    simp only [T]
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    rfl
  constructor
  · intro hm
    set X := ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c) with hX
    have hstab : ∀ (a : k ⊗[ℤ] C) (x : M), x ∈ X → a • x ∈ X := by
      intro a x hx
      rw [hX, Submodule.mem_iInf] at hx ⊢
      intro c
      have hc : Commute (ρ ((1 : k) ⊗ₜ[ℤ] c)) (ρ a) := (Commute.all _ _).map ρ
      exact Module.End.mapsTo_maxGenEigenspace_of_comm hc (χ c) (hx c)
    let X' : Submodule (k ⊗[ℤ] C) M :=
      { carrier := X
        add_mem' := fun ha hb => X.add_mem ha hb
        zero_mem' := X.zero_mem
        smul_mem' := fun a x hx => hstab a x hx }
    let ρX : k ⊗[ℤ] C →ₐ[k] Module.End k X' := Algebra.lsmul k k X'
    have hT : ∀ c, IsNilpotent (ρX (T c)) := by
      intro c
      refine ⟨Module.End.maxGenEigenspaceIndex (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c), ?_⟩
      ext ⟨x, hx⟩
      have hx' : x ∈ Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
        (Submodule.mem_iInf _).1 hx c
      rw [Module.End.maxGenEigenspace_eq, Module.End.mem_genEigenspace_nat] at hx'
      rw [← hρT, ← map_pow] at hx'
      rw [LinearMap.mem_ker] at hx'
      rw [← map_pow, LinearMap.zero_apply]
      exact hx'
    have hall : ∀ a, IsNilpotent (ρX (a - algebraMap k (k ⊗[ℤ] C) (φ a))) := by
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        have : x ⊗ₜ[ℤ] c - algebraMap k (k ⊗[ℤ] C) (φ (x ⊗ₜ[ℤ] c)) = x • T c := by
          simp only [T, hφt, smul_sub, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.tmul_mul_tmul]
          rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
          simp
        rw [this, map_smul]
        exact (hT c).smul x
      | add a b ha hb =>
        have : a + b - algebraMap k (k ⊗[ℤ] C) (φ (a + b)) =
            (a - algebraMap k (k ⊗[ℤ] C) (φ a)) + (b - algebraMap k (k ⊗[ℤ] C) (φ b)) := by
          rw [map_add, map_add]; abel
        rw [this, map_add]
        exact Commute.isNilpotent_add ((Commute.all _ _).map ρX) ha hb
    have h1e : IsNilpotent (ρX (1 - e)) := by
      have := hall (1 - e)
      rwa [show φ (1 - e) = 0 by rw [map_sub, map_one, he1, sub_self], map_zero, sub_zero] at this
    have hid : IsIdempotentElem (ρX (1 - e)) := he.one_sub.map ρX
    have h0 := hid.eq_zero_of_isNilpotent h1e
    have := congrArg (fun f => (f ⟨m, hm⟩ : X')) h0
    simp only [LinearMap.zero_apply] at this
    have := congrArg Subtype.val this
    change (1 - e) • m = 0 at this
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · intro hm
    rw [Submodule.mem_iInf]
    intro c
    rw [Module.End.mem_maxGenEigenspace]
    obtain ⟨n, hn⟩ := hnil (T c) (hφT c)
    refine ⟨n, ?_⟩
    have hen : ∀ j : ℕ, e ^ j • m = m := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, mul_smul, hm, ih]
    rw [← hρT, ← map_pow]
    change T c ^ n • m = 0
    rw [← hen n, smul_smul, mul_comm, ← mul_pow, hn, zero_smul]

end GlobalTheory
