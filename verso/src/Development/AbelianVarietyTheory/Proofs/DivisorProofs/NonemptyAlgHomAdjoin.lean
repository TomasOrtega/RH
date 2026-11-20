import Mathlib

namespace GlobalTheory.AdjoinAlgebraHomNonempty

/- English proof (translation)
Establish `h0 : h ≠ 0` using `fun e => hh (by rw [e, map_zero])`. Establish `h0F : (h : F) ≠ 0` using `fun e => h0 (Subtype.ext e)`. Establish `hu : ∀ y : Submonoid.powers h, IsUnit (S.val y)`. Introduce and unpack `⟨y, n, rfl⟩`. Simplify using `only [map_pow]`.

Conclude with `(IsUnit.mk0 _ h0F).pow n`. Establish `hv : ∀ y : Submonoid.powers h, IsUnit (ψ y)`. Introduce and unpack `⟨y, n, rfl⟩`. Simplify using `only [map_pow]`. Conclude with `(IsUnit.mk0 _ hh).pow n`.

Set `f : Localization.Away h →ₐ[k] F` to `IsLocalization.liftAlgHom (M := Submonoid.powers h) hu`. Set `g : Localization.Away h →ₐ[k] Ω` to `IsLocalization.liftAlgHom (M := Submonoid.powers h) hv`. Establish `hf : ∀ s : S, f (algebraMap S (Localization.Away h) s) = (s : F)` using `fun s => by`. Simplify using `[f, IsLocalization.liftAlgHom_apply]`. Establish `hinj : Function.Injective f`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (Submonoid.powers h) z`. Establish `h1` using `congrArg f hab`. Rewrite `h1` using `[map_mul, hz, zero_mul, hf]`.

Establish `ha : a = 0` using `Subtype.ext h1.symm`. Rewrite `hab` using `[ha, map_zero]`. Conclude with `(IsLocalization.map_units (Localization.Away h) b).mul_left_eq_zero.mp hab`. Establish `hle : Algebra.adjoin k T ≤ f.range`. Use `Algebra.adjoin_le fun x hx => ?_` and prove the remaining obligations.

Take `⟨u, hu'⟩` from `IsLocalization.map_units (Localization.Away h) (⟨h, Submonoid.mem_powers h⟩ : Submonoid.powers h)`. Use `⟨(↑u⁻¹ : Localization.Away h) * algebraMap S _ ⟨_, hT x hx⟩, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ h0F` to reduce the goal to its premises. Establish `e : f u = (h : F)` using `by rw [hu']; exact hf h`. Express the relevant statement in the definitionally equal form `(h : F) * f _ = _`.

Rewrite using `[map_mul, hf, ← mul_assoc]`. Establish `e2 : (h : F) * f (↑u⁻¹ : Localization.Away h) = 1`. Rewrite using `[← e, ← map_mul, Units.mul_inv, map_one]`. Rewrite using `[e2, one_mul]`. Conclude with `⟨(g.comp (AlgEquiv.ofInjective f hinj).symm.toAlgHom).comp (Subalgebra.inclusion hle)⟩`.
-/
theorem nonempty_algHom_adjoin (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hh : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  have h0 : h ≠ 0 := fun e => hh (by rw [e, map_zero])
  have h0F : (h : F) ≠ 0 := fun e => h0 (Subtype.ext e)
  have hu : ∀ y : Submonoid.powers h, IsUnit (S.val y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact (IsUnit.mk0 _ h0F).pow n
  have hv : ∀ y : Submonoid.powers h, IsUnit (ψ y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact (IsUnit.mk0 _ hh).pow n
  let f : Localization.Away h →ₐ[k] F := IsLocalization.liftAlgHom (M := Submonoid.powers h) hu
  let g : Localization.Away h →ₐ[k] Ω := IsLocalization.liftAlgHom (M := Submonoid.powers h) hv
  have hf : ∀ s : S, f (algebraMap S (Localization.Away h) s) = (s : F) := fun s => by
    simp [f, IsLocalization.liftAlgHom_apply]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (Submonoid.powers h) z
    have h1 := congrArg f hab
    rw [map_mul, hz, zero_mul, hf] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    rw [ha, map_zero] at hab
    exact (IsLocalization.map_units (Localization.Away h) b).mul_left_eq_zero.mp hab
  have hle : Algebra.adjoin k T ≤ f.range := by
    refine Algebra.adjoin_le fun x hx => ?_
    obtain ⟨u, hu'⟩ := IsLocalization.map_units (Localization.Away h)
      (⟨h, Submonoid.mem_powers h⟩ : Submonoid.powers h)
    refine ⟨(↑u⁻¹ : Localization.Away h) * algebraMap S _ ⟨_, hT x hx⟩, ?_⟩
    apply mul_left_cancel₀ h0F
    have e : f u = (h : F) := by rw [hu']; exact hf h
    change (h : F) * f _ = _
    rw [map_mul, hf, ← mul_assoc]
    have e2 : (h : F) * f (↑u⁻¹ : Localization.Away h) = 1 := by
      rw [← e, ← map_mul, Units.mul_inv, map_one]
    rw [e2, one_mul]
  exact ⟨(g.comp (AlgEquiv.ofInjective f hinj).symm.toAlgHom).comp (Subalgebra.inclusion hle)⟩

end GlobalTheory.AdjoinAlgebraHomNonempty
