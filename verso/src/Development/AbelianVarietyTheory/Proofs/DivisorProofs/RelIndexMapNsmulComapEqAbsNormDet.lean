import Mathlib

open NumberField Module

namespace GlobalTheory

/- English proof (translation)
Establish `: IsAddTorsionFree Γ` using `.of_module_rat Γ`. Establish `: Module.Finite ℤ A` using `Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg A).mpr hA)`. Set `bA` to `Module.finBasis ℤ A`. Set `v : Fin (Module.finrank ℤ A) → Γ` to `fun i => (bA i : Γ)`. Establish `hliZ : LinearIndependent ℤ v` using `bA.linearIndependent.map' A.subtype.toIntLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)`.

Establish `hli : LinearIndependent ℚ v` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ`. Establish `hcl : A = AddSubgroup.closure (Set.range v)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `a ha`. Establish `h' : a = ∑ i, bA.repr ⟨a, ha⟩ i • v i` using `by conv_lhs => rw [show a = ((⟨a, ha⟩ : A) : Γ) from rfl, ← bA.sum_repr ⟨a, ha⟩]`.

Rewrite using `[AddSubgroup.val_finsetSum]`. Simplify using `[v]`. Rewrite using `[h']`. Conclude with `AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _`. Rewrite using `[AddSubgroup.closure_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(bA i).2`. Establish `hsp : ⊤ ≤ Submodule.span ℚ (Set.range v)`. Introduce `x _`. Take `⟨N, hN0, hNx⟩` from `hN x`.

Establish `hmem : N • x ∈ Submodule.span ℚ (Set.range v)`. Rewrite `hNx` using `[hcl]`. Conclude with `(AddSubgroup.closure_le (Submodule.span ℚ (Set.range v)).toAddSubgroup).mpr Submodule.subset_span hNx`. Rewrite `hmem` using `[← Nat.cast_smul_eq_nsmul ℚ]`. Establish `hN' : (N : ℚ) ≠ 0` using `by exact_mod_cast hN0.ne'`.

Use `Submodule.smul_mem _ (N : ℚ)⁻¹ hmem` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hN', one_smul]`. Then use the resulting hypothesis. Use `⟨Module.finrank ℤ A, Basis.mk hli hsp, ?_⟩` and prove the remaining obligations. Rewrite using `[Basis.coe_mk]`. Conclude with `hcl`.
-/
theorem exists_basis_closure_eq_of_fg_of_nsmul_mem {Γ : Type} [AddCommGroup Γ] [Module ℚ Γ]
    (A : AddSubgroup Γ) (hA : A.FG) (hN : ∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ Γ), A = AddSubgroup.closure (Set.range b) := by
  classical
  have : IsAddTorsionFree Γ := .of_module_rat Γ
  have : Module.Finite ℤ A :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg A).mpr hA)
  let bA := Module.finBasis ℤ A
  let v : Fin (Module.finrank ℤ A) → Γ := fun i => (bA i : Γ)
  have hliZ : LinearIndependent ℤ v :=
    bA.linearIndependent.map' A.subtype.toIntLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hli : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hcl : A = AddSubgroup.closure (Set.range v) := by
    apply le_antisymm
    · intro a ha
      have h' : a = ∑ i, bA.repr ⟨a, ha⟩ i • v i := by
        conv_lhs => rw [show a = ((⟨a, ha⟩ : A) : Γ) from rfl, ← bA.sum_repr ⟨a, ha⟩]
        rw [AddSubgroup.val_finsetSum]
        simp [v]
      rw [h']
      exact AddSubgroup.sum_mem _ fun i _ =>
        AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact (bA i).2
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    intro x _
    obtain ⟨N, hN0, hNx⟩ := hN x
    have hmem : N • x ∈ Submodule.span ℚ (Set.range v) := by
      rw [hcl] at hNx
      exact (AddSubgroup.closure_le (Submodule.span ℚ (Set.range v)).toAddSubgroup).mpr
        Submodule.subset_span hNx
    rw [← Nat.cast_smul_eq_nsmul ℚ] at hmem
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
    have := Submodule.smul_mem _ (N : ℚ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hN', one_smul] at this
  refine ⟨Module.finrank ℤ A, Basis.mk hli hsp, ?_⟩
  rw [Basis.coe_mk]
  exact hcl

/- English proof (translation)
Introduce `E Γ _ _ _ _ _ A hA hAN m N hN0 hdet hmA`. Use `letI : Module ℚ Γ := Module.compHom Γ (algebraMap ℚ E)`. Establish `: IsScalarTower ℚ E Γ` using `⟨fun q c x => by show (q • c) • x = algebraMap ℚ E q • (c • x)`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Take `⟨n, b, hb⟩` from `exists_basis_closure_eq_of_fg_of_nsmul_mem A hA hAN`.

Establish `: FiniteDimensional ℚ Γ` using `Module.Finite.of_basis b`. Set `mQ : Γ →ₗ[ℚ] Γ` to `m.restrictScalars ℚ`. Establish `hdetQ : LinearMap.det mQ = Algebra.norm ℚ (LinearMap.det m)` using `LinearMap.det_restrictScalars`. Establish `hdetQ0 : LinearMap.det mQ ≠ 0`. Rewrite using `[hdetQ]`.

Conclude with `Algebra.norm_ne_zero_iff.mpr hdet`. Establish `hu : IsUnit mQ` using `(LinearMap.isUnit_iff_isUnit_det mQ).mpr (isUnit_iff_ne_zero.mpr hdetQ0)`. Set `e : Γ ≃ₗ[ℚ] Γ` to `LinearEquiv.ofBijective mQ ((Module.End.isUnit_iff mQ).mp hu)`. Establish `he : ∀ x, e x = m x` using `fun x => rfl`. Establish `hN' : (N : ℚ) ≠ 0` using `by exact_mod_cast hN0`.

Set `b₁ : Basis (Fin n) ℚ Γ` to `b.map (LinearEquiv.smulOfNeZero ℚ Γ (N : ℚ) hN')`. Set `b₂ : Basis (Fin n) ℚ Γ` to `b.map e.symm`. Establish `hb₁ : ∀ i, b₁ i = N • b i` using `fun i => by`. Simplify using `[b₁, Nat.cast_smul_eq_nsmul]`. Establish `h₁ : A.map (N • AddMonoidHom.id Γ) = AddSubgroup.closure (Set.range b₁)`.

Rewrite using `[hb, AddMonoidHom.map_closure, ← Set.range_comp]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[hb₁]`. Establish `h₂ : A.comap m.toAddMonoidHom = AddSubgroup.closure (Set.range b₂)`.

Establish `hr : Set.range b₂ = e.symm.toLinearMap.toAddMonoidHom '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[hr, ← AddMonoidHom.map_closure, ← hb]`. Use extensionality with `x`.

Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨m x, hx, by rw [← he]; exact e.symm_apply_apply x⟩`. Introduce and unpack `⟨a, ha, rfl⟩`.

Express the relevant statement in the definitionally equal form `m (e.symm a) ∈ A`. Rewrite using `[← he, e.apply_symm_apply]`. Conclude with `ha`. Establish `hle : A.map (N • AddMonoidHom.id Γ) ≤ A.comap m.toAddMonoidHom`. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Express the relevant statement in the definitionally equal form `m (N • a) ∈ A`. Rewrite using `[map_nsmul]`. Conclude with `hmA a ha`. Rewrite using `[AddSubgroup.relIndex_eq_abs_det _ _ hle b₁ b₂ h₁ h₂]`. Use `congr 1`.

Establish `hcomp : e.symm.symm ∘ b₁ = ((N : ℚ) • mQ) ∘ b`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, LinearEquiv.symm_symm, hb₁, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]`. Rewrite using `[he, map_nsmul]`. Both sides reduce to the same expression.

Rewrite using `[Basis.det_map, hcomp, Basis.det_comp, Basis.det_self, mul_one, LinearMap.det_smul, hdetQ, map_mul, map_pow, ← map_natCast (algebraMap ℚ E), Algebra.norm_algebraMap, ← pow_mul, Module.finrank_mul_finrank]`.
-/
theorem relIndex_map_nsmul_comap_eq_abs_norm_det :
    ∀ (E Γ : Type) [Field E] [NumberField E] [AddCommGroup Γ] [Module E Γ] [FiniteDimensional E Γ] (A : AddSubgroup Γ), A.FG → (∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) → ∀ (m : Module.End E Γ) (N : ℕ), N ≠ 0 → LinearMap.det m ≠ 0 → (∀ x ∈ A, N • m x ∈ A) → (((A.map (N • AddMonoidHom.id Γ)).relIndex (A.comap m.toAddMonoidHom) : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ Module.finrank E Γ * LinearMap.det m)| := by
  intro E Γ _ _ _ _ _ A hA hAN m N hN0 hdet hmA
  classical
  letI : Module ℚ Γ := Module.compHom Γ (algebraMap ℚ E)
  have : IsScalarTower ℚ E Γ := ⟨fun q c x => by
    show (q • c) • x = algebraMap ℚ E q • (c • x)
    rw [Algebra.smul_def, mul_smul]⟩
  obtain ⟨n, b, hb⟩ := exists_basis_closure_eq_of_fg_of_nsmul_mem A hA hAN
  have : FiniteDimensional ℚ Γ := Module.Finite.of_basis b
  let mQ : Γ →ₗ[ℚ] Γ := m.restrictScalars ℚ
  have hdetQ : LinearMap.det mQ = Algebra.norm ℚ (LinearMap.det m) :=
    LinearMap.det_restrictScalars
  have hdetQ0 : LinearMap.det mQ ≠ 0 := by
    rw [hdetQ]
    exact Algebra.norm_ne_zero_iff.mpr hdet
  have hu : IsUnit mQ := (LinearMap.isUnit_iff_isUnit_det mQ).mpr (isUnit_iff_ne_zero.mpr hdetQ0)
  let e : Γ ≃ₗ[ℚ] Γ := LinearEquiv.ofBijective mQ ((Module.End.isUnit_iff mQ).mp hu)
  have he : ∀ x, e x = m x := fun x => rfl
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  let b₁ : Basis (Fin n) ℚ Γ := b.map (LinearEquiv.smulOfNeZero ℚ Γ (N : ℚ) hN')
  let b₂ : Basis (Fin n) ℚ Γ := b.map e.symm
  have hb₁ : ∀ i, b₁ i = N • b i := fun i => by
    simp [b₁, Nat.cast_smul_eq_nsmul]
  have h₁ : A.map (N • AddMonoidHom.id Γ) = AddSubgroup.closure (Set.range b₁) := by
    rw [hb, AddMonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext x
    simp [hb₁]
  have h₂ : A.comap m.toAddMonoidHom = AddSubgroup.closure (Set.range b₂) := by
    have hr : Set.range b₂ = e.symm.toLinearMap.toAddMonoidHom '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← AddMonoidHom.map_closure, ← hb]
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map]
    constructor
    · intro hx
      exact ⟨m x, hx, by rw [← he]; exact e.symm_apply_apply x⟩
    · rintro ⟨a, ha, rfl⟩
      change m (e.symm a) ∈ A
      rw [← he, e.apply_symm_apply]
      exact ha
  have hle : A.map (N • AddMonoidHom.id Γ) ≤ A.comap m.toAddMonoidHom := by
    rintro _ ⟨a, ha, rfl⟩
    change m (N • a) ∈ A
    rw [map_nsmul]
    exact hmA a ha
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hle b₁ b₂ h₁ h₂]
  congr 1
  have hcomp : e.symm.symm ∘ b₁ = ((N : ℚ) • mQ) ∘ b := by
    funext i
    simp only [Function.comp_apply, LinearEquiv.symm_symm, hb₁, LinearMap.smul_apply,
      Nat.cast_smul_eq_nsmul]
    rw [he, map_nsmul]
    rfl
  rw [Basis.det_map, hcomp, Basis.det_comp, Basis.det_self, mul_one, LinearMap.det_smul, hdetQ,
    map_mul, map_pow, ← map_natCast (algebraMap ℚ E), Algebra.norm_algebraMap, ← pow_mul,
    Module.finrank_mul_finrank]

end GlobalTheory
