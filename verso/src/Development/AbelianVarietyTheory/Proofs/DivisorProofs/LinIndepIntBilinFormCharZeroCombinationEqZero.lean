import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `hli hsum`. Set `L : LinearMap.BilinForm ℤ X →ₗ[ℤ] (X → X → ℚ)` to `{ toFun := fun B y z => ((B y z : ℤ) : ℚ) map_add' := by intro B C; funext y z; simp map_smul' := by intro n B; funext y z; simp }`. Establish `hker : LinearMap.ker L = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `B hB`.

Use extensionality with `y z`. Use `congrFun (congrFun hB y) z` as an intermediate fact. Simplify `this` using `[L]`. Establish `hZ : LinearIndependent ℤ (L ∘ gam)` using `hli.map' L hker`. Establish `hQ : LinearIndependent ℚ (L ∘ gam)` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ`.

Use function extensionality and compare the values at `j`. Assume the negation of the conclusion as `hj`. Take `⟨ℓ, hℓ⟩` from `Module.Projective.exists_dual_ne_zero ℚ (V := k) hj`. Establish `hrel : ∑ i, ℓ (a i) • (L ∘ gam) i = 0`. Use function extensionality and compare the values at `y z`.

Establish `h0` using `congrArg ℓ (hsum y z)`. Rewrite `h0` using `[map_sum, map_zero]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply, smul_eq_mul, L, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[← h0]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]`. Use `(Fintype.linearIndependent_iff.mp hQ) _ hrel j` as an intermediate fact. Conclude with `hℓ this`.
-/
theorem linIndep_intBilinForm_charZero_comb_eq_zero
    {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X)
    (k : Type) [Field k] [CharZero k] (a : Fin m → k) :
    LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by
  intro hli hsum

  let L : LinearMap.BilinForm ℤ X →ₗ[ℤ] (X → X → ℚ) :=
    { toFun := fun B y z => ((B y z : ℤ) : ℚ)
      map_add' := by intro B C; funext y z; simp
      map_smul' := by intro n B; funext y z; simp }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro B hB
    ext y z
    have := congrFun (congrFun hB y) z
    simpa [L] using this
  have hZ : LinearIndependent ℤ (L ∘ gam) := hli.map' L hker
  have hQ : LinearIndependent ℚ (L ∘ gam) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ
  funext j
  by_contra hj
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero ℚ (V := k) hj
  have hrel : ∑ i, ℓ (a i) • (L ∘ gam) i = 0 := by
    funext y z
    have h0 := congrArg ℓ (hsum y z)
    rw [map_sum, map_zero] at h0
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply, smul_eq_mul, L,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  have := (Fintype.linearIndependent_iff.mp hQ) _ hrel j
  exact hℓ this

end GlobalTheory
