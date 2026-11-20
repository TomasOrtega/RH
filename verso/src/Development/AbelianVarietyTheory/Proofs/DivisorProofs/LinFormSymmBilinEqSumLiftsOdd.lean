import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormBilinFormsEqSumMinimiserValues
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc

/- English proof (translation)
Establish `hdec : ∀ x : Y, ∃ y : Y, x = μ (fun i => (eb x i : ZMod N)) + (N : ℤ) • y`. Introduce `x`. Establish `hd : ∀ i, (N : ℤ) ∣ eb x i - eb (μ (fun i => (eb x i : ZMod N))) i`. Introduce `i`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Use `push_cast`. Rewrite using `[hμ _ i, sub_self]`. Use `choose z hz using hd`. Use `⟨eb.symm z, ?_⟩` and prove the remaining obligations. Apply `eb.injective` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Rewrite using `[map_add, map_smul, LinearEquiv.apply_symm_apply]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Combine the linear relations using `[hz i]`. Establish `hdiag : ∀ k, (∀ x y, (N : ℤ) ^ k ∣ B x y) → ∀ x, (N : ℤ) ^ (k + 1) ∣ B x x`.

Introduce `k hk x`. Take `⟨y, hy⟩` from `hdec x`. Establish `hm` using `h0 (fun i => (eb x i : ZMod N))`. Generalize the expression as in `μ (fun i => (eb x i : ZMod N)) = m at hy hm`. Substitute `hy` using the available equality.

Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hm]`. Rewrite using `[hB y m]`. Take `⟨a, ha⟩` from `hk m y`. Take `⟨b, hb⟩` from `hk y y`. Rewrite using `[ha, hb]`.

Conclude with `⟨2 * a + N * b, by ring⟩`. Establish `hcop : IsCoprime (N : ℤ) 2`. Use `Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_right.mpr hodd)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro x y`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `x y`.

Establish `h2 : (N : ℤ) ^ (k + 1) ∣ 2 * B x y`. Establish `hxy` using `hdiag k ih (x + y)`. Establish `hx` using `hdiag k ih x`. Establish `hy` using `hdiag k ih y`. Establish `e : 2 * B x y = B (x + y) (x + y) - B x x - B y y`.

Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[hB y x]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_sub (dvd_sub hxy hx) hy`.

Conclude with `(hcop.pow_left).dvd_of_dvd_mul_left h2`.
-/
theorem symm_bilin_pow_dvd_of_lifts {Y : Type} [AddCommGroup Y] (n N : ℕ) (hodd : Odd N)
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y)
    (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (B : LinearMap.BilinForm ℤ Y) (hB : ∀ x y, B x y = B y x) (h0 : ∀ cl, B (μ cl) (μ cl) = 0) :
    ∀ k : ℕ, ∀ x y, (N : ℤ) ^ k ∣ B x y := by
  have hdec : ∀ x : Y, ∃ y : Y, x = μ (fun i => (eb x i : ZMod N)) + (N : ℤ) • y := by
    intro x
    have hd : ∀ i, (N : ℤ) ∣ eb x i - eb (μ (fun i => (eb x i : ZMod N))) i := by
      intro i
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hμ _ i, sub_self]
    choose z hz using hd
    refine ⟨eb.symm z, ?_⟩
    apply eb.injective
    funext i
    rw [map_add, map_smul, LinearEquiv.apply_symm_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hz i]
  have hdiag : ∀ k, (∀ x y, (N : ℤ) ^ k ∣ B x y) → ∀ x, (N : ℤ) ^ (k + 1) ∣ B x x := by
    intro k hk x
    obtain ⟨y, hy⟩ := hdec x
    have hm := h0 (fun i => (eb x i : ZMod N))
    generalize μ (fun i => (eb x i : ZMod N)) = m at hy hm
    subst hy
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hm]
    rw [hB y m]
    obtain ⟨a, ha⟩ := hk m y
    obtain ⟨b, hb⟩ := hk y y
    rw [ha, hb]
    exact ⟨2 * a + N * b, by ring⟩
  have hcop : IsCoprime (N : ℤ) 2 := by
    have := Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_right.mpr hodd)
    exact_mod_cast this
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    have h2 : (N : ℤ) ^ (k + 1) ∣ 2 * B x y := by
      have hxy := hdiag k ih (x + y)
      have hx := hdiag k ih x
      have hy := hdiag k ih y
      have e : 2 * B x y = B (x + y) (x + y) - B x x - B y y := by
        simp only [map_add, LinearMap.add_apply]
        rw [hB y x]
        ring
      rw [e]
      exact dvd_sub (dvd_sub hxy hx) hy
    exact (hcop.pow_left).dvd_of_dvd_mul_left h2

/- English proof (translation)
Use extensionality with `x y`. Establish `h` using `symm_bilin_pow_dvd_of_lifts n N hodd eb μ hμ B hB h0 (B x y).natAbs x y`. Use `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_` and prove the remaining obligations. Rewrite using `[Int.natAbs_pow, Int.natAbs_natCast]`. Conclude with `Nat.lt_pow_self (by omega)`.
-/
theorem symm_bilin_eq_zero_of_lifts {Y : Type} [AddCommGroup Y] (n N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y)
    (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (B : LinearMap.BilinForm ℤ Y) (hB : ∀ x y, B x y = B y x) (h0 : ∀ cl, B (μ cl) (μ cl) = 0) :
    B = 0 := by
  ext x y
  have h := symm_bilin_pow_dvd_of_lifts n N hodd eb μ hμ B hB h0 (B x y).natAbs x y
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

/- English proof (translation)
Introduce `Y _ n N _ hN hodd eb μ hμ ℓ`. Use `haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm`. Use `haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm`. Set `S : Submodule ℤ (LinearMap.BilinForm ℤ Y)` to `{ carrier := {b | ∀ x y, b x y = b y x} add_mem' := by intro a b ha hb x y; simp [ha x y, hb x y] zero_mem' := by intro x y; simp smul_mem' := by intro c b hb x y; simp [hb x y] }`. Set `Φ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ((Fin n → ZMod N) → ℤ)` to `{ toFun := fun b c => b (μ c) (μ c) map_add' := by intro a b; funext c; simp map_smul' := by intro k b; funext c; simp }`.

Establish `hinj : Function.Injective (Φ ∘ₗ S.subtype)`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `sub_eq_zero.mp` to reduce the goal to its premises. Use `symm_bilin_eq_zero_of_lifts n N hN hodd eb μ hμ _ ?_ ?_` and prove the remaining obligations.

Introduce `u v`. Simplify using `[x.2 u v, y.2 u v]`. Introduce `c`. Use `congrFun hxy c` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Φ] at this`.

Simplify using `[this]`. Take `⟨D, hD, ν, hν⟩` from `exists_nat_mul_eq_sum_of_injective (Φ ∘ₗ S.subtype) hinj (ℓ ∘ₗ S.subtype)`. Conclude with `⟨D, ν, hD, fun b hb => hν ⟨b, hb⟩⟩`.
-/
theorem linForm_eq_sum_lifts : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N], 3 ≤ N → Odd N →
    ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) →
    ∀ ℓ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin n → ZMod N) → ℤ), 0 < D ∧
      ∀ b : LinearMap.BilinForm ℤ Y, (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ cl, ν cl * b (μ cl) (μ cl) := by
  intro Y _ n N _ hN hodd eb μ hμ ℓ
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  let S : Submodule ℤ (LinearMap.BilinForm ℤ Y) :=
    { carrier := {b | ∀ x y, b x y = b y x}
      add_mem' := by intro a b ha hb x y; simp [ha x y, hb x y]
      zero_mem' := by intro x y; simp
      smul_mem' := by intro c b hb x y; simp [hb x y] }
  let Φ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ((Fin n → ZMod N) → ℤ) :=
    { toFun := fun b c => b (μ c) (μ c)
      map_add' := by intro a b; funext c; simp
      map_smul' := by intro k b; funext c; simp }
  have hinj : Function.Injective (Φ ∘ₗ S.subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    refine symm_bilin_eq_zero_of_lifts n N hN hodd eb μ hμ _ ?_ ?_
    · intro u v
      simp [x.2 u v, y.2 u v]
    · intro c
      have := congrFun hxy c
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Φ] at this
      simp [this]
  obtain ⟨D, hD, ν, hν⟩ := exists_nat_mul_eq_sum_of_injective (Φ ∘ₗ S.subtype) hinj (ℓ ∘ₗ S.subtype)
  exact ⟨D, ν, hD, fun b hb => hν ⟨b, hb⟩⟩

end GlobalTheory.Poinc
