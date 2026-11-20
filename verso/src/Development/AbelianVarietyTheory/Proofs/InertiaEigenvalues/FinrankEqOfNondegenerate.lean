import Mathlib

namespace GlobalTheory.NondegenerateFinrank

/- English proof (translation)
Establish `i1 : Function.Injective P`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Conclude with `h1 x (fun y => by simp [hx])`. Establish `i2 : Function.Injective P.flip`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Conclude with `h2 y (fun x => by`. Use `LinearMap.congr_fun hy x` as an intermediate fact. Simplify using `using this)`.

Establish `a` using `LinearMap.finrank_le_finrank_of_injective i1`. Establish `b` using `LinearMap.finrank_le_finrank_of_injective i2`. Establish `ea : Module.finrank LL (V' →ₗ[LL] LL) = Module.finrank LL V'` using `Subspace.dual_finrank_eq`. Establish `eb : Module.finrank LL (V →ₗ[LL] LL) = Module.finrank LL V` using `Subspace.dual_finrank_eq`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_eq_of_nondegenerate {LL : Type} [Field LL] {V V' : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (h1 : ∀ (x : V), (∀ (y : V'), P x y = 0) → x = 0)
    (h2 : ∀ (y : V'), (∀ (x : V), P x y = 0) → y = 0) :
    Module.finrank LL V = Module.finrank LL V' := by
  have i1 : Function.Injective P := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact h1 x (fun y => by simp [hx])
  have i2 : Function.Injective P.flip := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact h2 y (fun x => by
      have := LinearMap.congr_fun hy x
      simpa using this)
  have a := LinearMap.finrank_le_finrank_of_injective i1
  have b := LinearMap.finrank_le_finrank_of_injective i2
  have ea : Module.finrank LL (V' →ₗ[LL] LL) = Module.finrank LL V' := Subspace.dual_finrank_eq
  have eb : Module.finrank LL (V →ₗ[LL] LL) = Module.finrank LL V := Subspace.dual_finrank_eq
  omega

/- English proof (translation)
Introduce `P h1 h2` and use `finrank_eq_of_nondegenerate P h1 h2`.
-/
theorem main : ∀ {LL : Type} [inst : Field LL] {V V' : Type} [inst_1 : AddCommGroup V] [inst_2 : Module LL V] [FiniteDimensional LL V] [inst_4 : AddCommGroup V'] [inst_5 : Module LL V'] [FiniteDimensional LL V'] (P : V →ₗ[LL] V' →ₗ[LL] LL), (∀ (x : V), (∀ (y : V'), ((P : V → V' →ₗ[LL] LL) x : V' → LL) y = (0 : LL)) → x = (0 : V)) → (∀ (y : V'), (∀ (x : V), ((P : V → V' →ₗ[LL] LL) x : V' → LL) y = (0 : LL)) → y = (0 : V')) → Module.finrank LL V = Module.finrank LL V' :=
  fun P h1 h2 => finrank_eq_of_nondegenerate P h1 h2

end GlobalTheory.NondegenerateFinrank
