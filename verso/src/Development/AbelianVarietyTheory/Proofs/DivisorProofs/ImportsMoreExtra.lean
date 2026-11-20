import Mathlib

namespace GlobalTheory.SimplifiedIdentity

/- English proof (translation)
Introduce `E V _ _ _ _ s r B hB x y hxx hyy hxy z w₀ hxz hyz hzz hzw`. Establish `hsym : ∀ u v : V, B u v = 0 → B v u = 0`. Introduce `u v h`. Rewrite using `[hB, h, map_zero]`. Establish `hyx : ∀ i j : Fin r, B (y i) (x j) = if j = i then (1:E) else 0`.

Apply the tactic sequence `intro i j; rw [hB, hxy]; split_ifs <;> simp`. Use `set w1 : V := w₀ - ∑ i, (B (y i) w₀ • x i + B (x i) w₀ • y i) with hw1`. Establish `hxw1 : ∀ j, B (x j) w1 = 0`. Introduce `j`. Simplify using `[hw1, map_sum, hxx, hxy]`.

Establish `hyw1 : ∀ j, B (y j) w1 = 0`. Introduce `j`. Simplify using `[hw1, map_sum, hyy, hyx]`. Establish `hzx : ∀ i, B z (x i) = 0` using `fun i => hsym _ _ (hxz i)`. Establish `hzy : ∀ i, B z (y i) = 0` using `fun i => hsym _ _ (hyz i)`.

Establish `hzw1 : B z w1 = 1`. Simplify using `[hw1, map_sum, hzx, hzy, hzw]`. Establish `hw1z : B w1 z = 1` using `by rw [hB, hzw1, map_one]`. Use `set c : E := B w1 w1 / 2 with hc`. Establish `hsc : s c = c`.

Rewrite using `[hc, map_div₀, ← hB, map_ofNat]`. Use `set w : V := w1 - c • z with hw`. Establish `hxw : ∀ j, B (x j) w = 0` using `by intro j; simp [hw, hxw1, hxz]`. Establish `hyw : ∀ j, B (y j) w = 0` using `by intro j; simp [hw, hyw1, hyz]`. Establish `hzw' : B z w = 1` using `by simp [hw, hzw1, hzz]`.

Establish `hww : B w w = 0`. Simplify using `only [hw, map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hw1z, hzw1, hzz, hsc]`. Rewrite using `[hc]`. Simplify using `only [RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨Fin.snoc x z, Fin.snoc y w, ?_, ?_, ?_, fun i => Fin.snoc_castSucc .., fun i => Fin.snoc_castSucc ..⟩` and prove the remaining obligations. Introduce `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[Fin.snoc_castSucc, Fin.snoc_last, hxx, hxz, hzx, hzz]`. Introduce `i j`.

Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[Fin.snoc_castSucc, Fin.snoc_last, hyy, hyw, hww, hsym _ _ (hyw _)]`. Introduce `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[Fin.snoc_castSucc, Fin.snoc_last, hxy, hxw, hzy, hzw', Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]`.
-/
theorem main : ∀ {E V : Type} [inst : Field E] [CharZero E] [inst_2 : AddCommGroup V] [inst_3 : Module E V] {s : E →+* E} {r : ℕ} (B : V →ₛₗ[s] V →ₗ[E] E), (∀ (u v : V), ((B : V → V →ₗ[E] E) u : V → E) v = (s : E → E) (((B : V → V →ₗ[E] E) v : V → E) u)) → ∀ {x y : Fin r → V}, (∀ (i j : Fin r), ((B : V → V →ₗ[E] E) (x i) : V → E) (x j) = (0 : E)) → (∀ (i j : Fin r), ((B : V → V →ₗ[E] E) (y i) : V → E) (y j) = (0 : E)) → (∀ (i j : Fin r), ((B : V → V →ₗ[E] E) (x i) : V → E) (y j) = if i = j then (1 : E) else (0 : E)) → ∀ {z w₀ : V}, (∀ (i : Fin r), ((B : V → V →ₗ[E] E) (x i) : V → E) z = (0 : E)) → (∀ (i : Fin r), ((B : V → V →ₗ[E] E) (y i) : V → E) z = (0 : E)) → ((B : V → V →ₗ[E] E) z : V → E) z = (0 : E) → ((B : V → V →ₗ[E] E) z : V → E) w₀ = (1 : E) → ∃ (x' : Fin (r + (1 : ℕ)) → V) (y' : Fin (r + (1 : ℕ)) → V), (∀ (i j : Fin (r + (1 : ℕ))), ((B : V → V →ₗ[E] E) (x' i) : V → E) (x' j) = (0 : E)) ∧ (∀ (i j : Fin (r + (1 : ℕ))), ((B : V → V →ₗ[E] E) (y' i) : V → E) (y' j) = (0 : E)) ∧ (∀ (i j : Fin (r + (1 : ℕ))), ((B : V → V →ₗ[E] E) (x' i) : V → E) (y' j) = if i = j then (1 : E) else (0 : E)) ∧ (∀ (i : Fin r), x' (Fin.castSucc i) = x i) ∧ ∀ (i : Fin r), y' (Fin.castSucc i) = y i := by
  intro E V _ _ _ _ s r B hB x y hxx hyy hxy z w₀ hxz hyz hzz hzw
  have hsym : ∀ u v : V, B u v = 0 → B v u = 0 := by
    intro u v h; rw [hB, h, map_zero]
  have hyx : ∀ i j : Fin r, B (y i) (x j) = if j = i then (1:E) else 0 := by
    intro i j; rw [hB, hxy]; split_ifs <;> simp
  set w1 : V := w₀ - ∑ i, (B (y i) w₀ • x i + B (x i) w₀ • y i) with hw1
  have hxw1 : ∀ j, B (x j) w1 = 0 := by
    intro j; simp [hw1, map_sum, hxx, hxy]
  have hyw1 : ∀ j, B (y j) w1 = 0 := by
    intro j; simp [hw1, map_sum, hyy, hyx]
  have hzx : ∀ i, B z (x i) = 0 := fun i => hsym _ _ (hxz i)
  have hzy : ∀ i, B z (y i) = 0 := fun i => hsym _ _ (hyz i)
  have hzw1 : B z w1 = 1 := by
    simp [hw1, map_sum, hzx, hzy, hzw]
  have hw1z : B w1 z = 1 := by rw [hB, hzw1, map_one]
  set c : E := B w1 w1 / 2 with hc
  have hsc : s c = c := by
    rw [hc, map_div₀, ← hB, map_ofNat]
  set w : V := w1 - c • z with hw
  have hxw : ∀ j, B (x j) w = 0 := by intro j; simp [hw, hxw1, hxz]
  have hyw : ∀ j, B (y j) w = 0 := by intro j; simp [hw, hyw1, hyz]
  have hzw' : B z w = 1 := by simp [hw, hzw1, hzz]
  have hww : B w w = 0 := by
    simp only [hw, map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hw1z, hzw1, hzz, hsc]
    rw [hc]; simp only [RingHom.id_apply]; ring
  refine ⟨Fin.snoc x z, Fin.snoc y w, ?_, ?_, ?_, fun i => Fin.snoc_castSucc .., fun i => Fin.snoc_castSucc ..⟩
  · intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hxx, hxz, hzx, hzz]
  · intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hyy, hyw, hww, hsym _ _ (hyw _)]
  · intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hxy, hxw, hzy, hzw', Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

end GlobalTheory.SimplifiedIdentity
