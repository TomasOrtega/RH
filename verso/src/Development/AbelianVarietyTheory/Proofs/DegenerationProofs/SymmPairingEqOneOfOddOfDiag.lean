import Mathlib

open scoped BigOperators
open Matrix

namespace GlobalTheory

/- English proof (translation)
Take `⟨m, hm⟩` from `hb`. Establish `h2 : u ^ (2 * b) = 1` using `by rw [two_mul, _root_.zpow_add]; exact h`. Establish `hk : u ^ (k : ℤ) = 1` using `by rw [zpow_natCast]; exact hu`. Establish `hsplit : 2 * b = k * m + 1` using `by linarith`. Rewrite `h2` using `[hsplit, _root_.zpow_add, _root_.zpow_mul, hk, _root_.one_zpow, one_mul, _root_.zpow_one]`.

Conclude with `h2`.
-/
private lemma eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one {U : Type} [CommGroup U] (k : ℕ) (b : ℤ) (hb : (k : ℤ) ∣ 2 * b - 1)
    (u : U) (hu : u ^ k = 1) (h : u ^ b * u ^ b = 1) : u = 1 := by
  obtain ⟨m, hm⟩ := hb
  have h2 : u ^ (2 * b) = 1 := by rw [two_mul, _root_.zpow_add]; exact h
  have hk : u ^ (k : ℤ) = 1 := by rw [zpow_natCast]; exact hu
  have hsplit : 2 * b = k * m + 1 := by linarith
  rw [hsplit, _root_.zpow_add, _root_.zpow_mul, hk, _root_.one_zpow, one_mul, _root_.zpow_one] at h2
  exact h2

/- English proof (translation)
Establish `h0 : f 0 = 1`. Establish `h` using `hf 0 0`. Rewrite `h` using `[add_zero]`. Simplify using `using h`. Set `g : X →+ Additive U` to `{ toFun := fun x => Additive.ofMul (f x) map_zero' := by simp [h0] map_add' := fun x x' => by simp [hf] }`.

Establish `hg : g.toIntLinearMap = 0` using `e.ext fun i => by simp [g, he]`. Establish `hx` using `LinearMap.congr_fun hg x`. Simplify `hx` using `[g]`.
-/
private lemma eq_one_of_hom_eq_one_on_basis {X U : Type} [AddCommGroup X] [CommGroup U] {d : ℕ}
    (e : Module.Basis (Fin d) ℤ X) (f : X → U) (hf : ∀ x x', f (x + x') = f x * f x')
    (he : ∀ i, f (e i) = 1) (x : X) : f x = 1 := by
  have h0 : f 0 = 1 := by
    have h := hf 0 0
    rw [add_zero] at h
    simpa using h
  let g : X →+ Additive U :=
    { toFun := fun x => Additive.ofMul (f x)
      map_zero' := by simp [h0]
      map_add' := fun x x' => by simp [hf] }
  have hg : g.toIntLinearMap = 0 := e.ext fun i => by simp [g, he]
  have hx := LinearMap.congr_fun hg x
  simpa [g] using hx

/- English proof (translation)
Introduce `X U _ _ d k e b _ hb δ hadd hsymm hk1 hdiag hdiag2`. Establish `hadd2 : ∀ x y y', δ x (y + y') = δ x y * δ x y'`. Introduce `x y y'`. Rewrite using `[hsymm x, hadd, hsymm y, hsymm y']`. Establish `hoff : ∀ i j, δ (e i) (e j) = 1`.

Introduce `i j`. Establish `h` using `hdiag2 i j`. Rewrite `h` using `[hadd, hadd2, hadd2, hsymm (e j) (e i), _root_.mul_zpow, _root_.mul_zpow, _root_.mul_zpow, hdiag i, hdiag j]`. Apply `eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one k b hb _ (hk1 _ _)` to reduce the goal to its premises. Simplify using `using h`.

Establish `hrow : ∀ i y, δ (e i) y = 1` using `fun i => eq_one_of_hom_eq_one_on_basis e (δ (e i)) (hadd2 (e i)) (hoff i)`. Introduce `x y`. Conclude with `eq_one_of_hom_eq_one_on_basis e (fun x => δ x y) (fun x x' => hadd x x' y) (fun i => hrow i y) x`.
-/
theorem symm_pairing_eq_one_of_odd_of_diag :
    ∀ (X U : Type) [AddCommGroup X] [CommGroup U] (d k : ℕ) (e : Module.Basis (Fin d) ℤ X) (b : ℤ), Odd k → (k : ℤ) ∣ 2 * b - 1 → ∀ δ : X → X → U, (∀ x x' y, δ (x + x') y = δ x y * δ x' y) → (∀ x y, δ x y = δ y x) → (∀ x y, δ x y ^ k = 1) → (∀ i, δ (e i) (e i) ^ b = 1) → (∀ i j, δ (e i + e j) (e i + e j) ^ b = 1) → ∀ x y, δ x y = 1 := by
  intro X U _ _ d k e b _ hb δ hadd hsymm hk1 hdiag hdiag2
  have hadd2 : ∀ x y y', δ x (y + y') = δ x y * δ x y' := by
    intro x y y'
    rw [hsymm x, hadd, hsymm y, hsymm y']
  have hoff : ∀ i j, δ (e i) (e j) = 1 := by
    intro i j
    have h := hdiag2 i j
    rw [hadd, hadd2, hadd2, hsymm (e j) (e i), _root_.mul_zpow, _root_.mul_zpow, _root_.mul_zpow, hdiag i, hdiag j] at h
    apply eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one k b hb _ (hk1 _ _)
    simpa using h
  have hrow : ∀ i y, δ (e i) y = 1 := fun i =>
    eq_one_of_hom_eq_one_on_basis e (δ (e i)) (hadd2 (e i)) (hoff i)
  intro x y
  exact eq_one_of_hom_eq_one_on_basis e (fun x => δ x y) (fun x x' => hadd x x' y) (fun i => hrow i y) x

end GlobalTheory
