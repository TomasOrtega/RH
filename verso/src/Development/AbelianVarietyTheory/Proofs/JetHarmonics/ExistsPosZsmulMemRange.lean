import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

section CosetMin
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}

/- English proof (translation)
Establish `h1` using `hQ (y + t • w)`. Establish `h2` using `hQ y`. Establish `h3` using `hQ w`. Establish `h4` using `hs w y`. Simplify using `only [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul] at h1`.

Establish `h5 : 2 * Q (y + t • w) = 2 * (Q y + t * Bf y w + t ^ 2 * Q w)`. Take the linear combination `h1 - h2 + t * h4 - t ^ 2 * h3`. Conclude with `mul_left_cancel₀ two_ne_zero h5`.
-/
theorem quad_add_zsmul (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (t : ℤ) : Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w := by
  have h1 := hQ (y + t • w)
  have h2 := hQ y
  have h3 := hQ w
  have h4 := hs w y
  simp only [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul] at h1
  have h5 : 2 * Q (y + t • w) = 2 * (Q y + t * Bf y w + t ^ 2 * Q w) := by
    linear_combination h1 - h2 + t * h4 - t ^ 2 * h3
  exact mul_left_cancel₀ two_ne_zero h5

/- English proof (translation)
Establish `h` using `hQ 0`. Simplify using `only [map_zero] at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem quad_zero (hQ : ∀ x, 2 * Q x = Bf x x) : Q 0 = 0 := by
  have h := hQ 0
  simp only [map_zero] at h
  omega

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Conclude with `(quad_zero hQ).ge`. Conclude with `le_trans zero_le_one (hp x hx)`.
-/
theorem quad_nonneg (hQ : ∀ x, 2 * Q x = Bf x x) (hp : ∀ x, x ≠ 0 → 1 ≤ Q x) (x : X) :
    0 ≤ Q x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact (quad_zero hQ).ge
  · exact le_trans zero_le_one (hp x hx)

/- English proof (translation)
Establish `hD : 0 < 2 * q * N` using `by positivity`. Establish `h1` using `Int.mul_ediv_add_emod (2 * q * a + B + N * q) (2 * q * N)`. Establish `h2` using `Int.emod_nonneg (2 * q * a + B + N * q) hD.ne'`. Establish `h3` using `Int.emod_lt_of_pos (2 * q * a + B + N * q) hD`. Use `⟨-((2 * q * a + B + N * q) / (2 * q * N)), ?_, ?_⟩` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma exists_int_shift_within_bounds (q B N a : ℤ) (hq : 0 < q) (hN : 0 < N) :
    ∃ m : ℤ, -(N * q) ≤ 2 * q * (a + N * m) + B ∧ 2 * q * (a + N * m) + B ≤ N * q := by
  have hD : 0 < 2 * q * N := by positivity
  have h1 := Int.mul_ediv_add_emod (2 * q * a + B + N * q) (2 * q * N)
  have h2 := Int.emod_nonneg (2 * q * a + B + N * q) hD.ne'
  have h3 := Int.emod_lt_of_pos (2 * q * a + B + N * q) hD
  refine ⟨-((2 * q * a + B + N * q) / (2 * q * N)), ?_, ?_⟩
  · linarith
  · linarith

/- English proof (translation)
Establish `key : ∀ t : ℤ, Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w` using `fun t => quad_add_zsmul hs hQ y w t`. Break down `hw.lt_or_eq with hq | hq` into its components or cases. Take `⟨m, hm1, hm2⟩` from `exists_int_shift_within_bounds (Q w) (Bf y w) N a hq hN`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[key]`.

Use `set t := a + N * m`. Establish `hsq : (2 * Q w * t + Bf y w) ^ 2 ≤ (N * Q w) ^ 2`. Use the polynomial consequences of the given equalities and inequalities. Establish `hmul : Q w * (4 * (t * Bf y w + t ^ 2 * Q w)) ≤ Q w * (N ^ 2 * Q w)`. Use polynomial arithmetic with `[sq_nonneg (Bf y w)]`.

Use `le_of_mul_le_mul_left hmul hq` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hB : 0 ≤ Bf y w`. Use `⟨-|a|, ?_⟩` and prove the remaining obligations. Rewrite using `[key, ← hq]`.

Establish `h1 : a + N * -|a| ≤ 0`. Use polynomial arithmetic with `[le_abs_self a, abs_nonneg a]`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨|a|, ?_⟩` and prove the remaining obligations. Rewrite using `[key, ← hq]`.

Establish `h1 : 0 ≤ a + N * |a|`. Use polynomial arithmetic with `[neg_abs_le a, abs_nonneg a]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem quad_round_step (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (hw : 0 ≤ Q w) (N : ℤ) (hN : 0 < N) (a : ℤ) :
    ∃ m : ℤ, 4 * Q (y + (a + N * m) • w) ≤ 4 * Q y + N ^ 2 * Q w := by
  have key : ∀ t : ℤ, Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w :=
    fun t => quad_add_zsmul hs hQ y w t
  rcases hw.lt_or_eq with hq | hq
  · obtain ⟨m, hm1, hm2⟩ := exists_int_shift_within_bounds (Q w) (Bf y w) N a hq hN
    refine ⟨m, ?_⟩
    rw [key]
    set t := a + N * m
    have hsq : (2 * Q w * t + Bf y w) ^ 2 ≤ (N * Q w) ^ 2 := by
      nlinarith
    have hmul : Q w * (4 * (t * Bf y w + t ^ 2 * Q w)) ≤ Q w * (N ^ 2 * Q w) := by
      nlinarith [sq_nonneg (Bf y w)]
    have := le_of_mul_le_mul_left hmul hq
    linarith
  · by_cases hB : 0 ≤ Bf y w
    · refine ⟨-|a|, ?_⟩
      rw [key, ← hq]
      have h1 : a + N * -|a| ≤ 0 := by
        nlinarith [le_abs_self a, abs_nonneg a]
      nlinarith
    · refine ⟨|a|, ?_⟩
      rw [key, ← hq]
      have h1 : 0 ≤ a + N * |a| := by
        nlinarith [neg_abs_le a, abs_nonneg a]
      nlinarith

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, by simp [quad_zero hQ]⟩`. Consider the case `insert i s hi ih`. Take `⟨m, hm⟩` from `ih`. Take `⟨m0, h0⟩` from `quad_round_step hs hQ (∑ j ∈ s, (a j + N * m j) • v j) (v i) (hv i) N hN (a i)`.

Use `⟨Function.update m i m0, ?_⟩` and prove the remaining obligations. Establish `hs' : ∑ j ∈ s, (a j + N * Function.update m i m0 j) • v j = ∑ j ∈ s, (a j + N * m j) • v j`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (fun h : j = i => hi (h ▸ hj))]`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, hs', Function.update_self, add_comm]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem quad_round_sum (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    {ι : Type} [DecidableEq ι] (v : ι → X) (hv : ∀ j, 0 ≤ Q (v j)) (N : ℤ) (hN : 0 < N)
    (a : ι → ℤ) (s : Finset ι) :
    ∃ m : ι → ℤ, 4 * Q (∑ j ∈ s, (a j + N * m j) • v j) ≤ N ^ 2 * ∑ j ∈ s, Q (v j) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [quad_zero hQ]⟩
  | insert i s hi ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨m0, h0⟩ :=
      quad_round_step hs hQ (∑ j ∈ s, (a j + N * m j) • v j) (v i) (hv i) N hN (a i)
    refine ⟨Function.update m i m0, ?_⟩
    have hs' : ∑ j ∈ s, (a j + N * Function.update m i m0 j) • v j
        = ∑ j ∈ s, (a j + N * m j) • v j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (fun h : j = i => hi (h ▸ hj))]
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hs', Function.update_self, add_comm]
    nlinarith

/- English proof (translation)
Establish `: Module.Free ℤ X` using `Module.Free.of_basis b`. Establish `: Module.Finite ℤ X` using `Module.Finite.of_basis b`. Use `set f : X →ₗ[ℤ] X := φ.toIntLinearMap with hf`. Use `set M := LinearMap.toMatrix b b f`. Establish `hinj : Function.Injective f`.

Simplify `hφ` using `[hf, AddMonoidHom.coe_toIntLinearMap]`. Establish `hdet : M.det ≠ 0`. Introduce `h`. Rewrite `h` using `[LinearMap.det_toMatrix, LinearMap.det_eq_zero_iff_ker_ne_bot]`. Conclude with `h (LinearMap.ker_eq_bot.mpr hinj)`.

Establish `e : Matrix.toLin b b M = f` using `Matrix.toLin_toMatrix b b f`. Establish `key : f.comp (Matrix.toLin b b M.adjugate) = M.det • LinearMap.id`. Combine the equalities or inequalities in the displayed calculation. Use `⟨M.det * M.det, mul_self_pos.mpr hdet, M.det • Matrix.toLin b b M.adjugate x, ?_⟩` and prove the remaining obligations. Establish `hx : f (Matrix.toLin b b M.adjugate x) = M.det • x`.

Use `congrArg (fun g => g x) key` as an intermediate fact. Simplify using `using this`. Establish `: φ (M.det • Matrix.toLin b b M.adjugate x) = M.det • f (Matrix.toLin b b M.adjugate x)`. Rewrite using `[map_zsmul]`. Both sides reduce to the same expression.

Rewrite using `[this, hx, smul_smul]`.
-/
theorem exists_pos_zsmul_mem_range {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (φ : X →+ X)
    (hφ : Function.Injective φ) (x : X) : ∃ N : ℤ, 0 < N ∧ ∃ y, φ y = N • x := by
  have : Module.Free ℤ X := Module.Free.of_basis b
  have : Module.Finite ℤ X := Module.Finite.of_basis b
  set f : X →ₗ[ℤ] X := φ.toIntLinearMap with hf
  set M := LinearMap.toMatrix b b f
  have hinj : Function.Injective f := by
    simpa [hf, AddMonoidHom.coe_toIntLinearMap] using hφ
  have hdet : M.det ≠ 0 := by
    intro h
    rw [LinearMap.det_toMatrix, LinearMap.det_eq_zero_iff_ker_ne_bot] at h
    exact h (LinearMap.ker_eq_bot.mpr hinj)
  have e : Matrix.toLin b b M = f := Matrix.toLin_toMatrix b b f
  have key : f.comp (Matrix.toLin b b M.adjugate) = M.det • LinearMap.id := by
    calc f.comp (Matrix.toLin b b M.adjugate)
        = (Matrix.toLin b b M).comp (Matrix.toLin b b M.adjugate) := by rw [e]
      _ = Matrix.toLin b b (M * M.adjugate) := (Matrix.toLin_mul b b b M M.adjugate).symm
      _ = M.det • LinearMap.id := by rw [Matrix.mul_adjugate, map_smul, Matrix.toLin_one]
  refine ⟨M.det * M.det, mul_self_pos.mpr hdet, M.det • Matrix.toLin b b M.adjugate x, ?_⟩
  have hx : f (Matrix.toLin b b M.adjugate x) = M.det • x := by
    have := congrArg (fun g => g x) key
    simpa using this
  have : φ (M.det • Matrix.toLin b b M.adjugate x) = M.det • f (Matrix.toLin b b M.adjugate x) := by
    rw [map_zsmul]; rfl
  rw [this, hx, smul_smul]

end CosetMin

/- English proof (translation)
Introduce `X _ Bf Q hs hQ hp n b Cc hC φ g hg hφ x`. Establish `hQφ : ∀ z, Q (φ z) = g * Q z`. Introduce `z`. Establish `h : 2 * Q (φ z) = 2 * (g * Q z)`. Rewrite using `[hQ, hφ, ← hQ z]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ two_ne_zero h`. Establish `hinj : Function.Injective φ`. Introduce `u v huv`. Assume the negation of the conclusion as `hne`.

Establish `h0 : φ (u - v) = 0` using `by rw [map_sub, huv, sub_self]`. Establish `h1` using `hp (u - v) (sub_ne_zero.mpr hne)`. Establish `h2` using `hQφ (u - v)`. Rewrite `h2` using `[h0, quad_zero hQ]`. Establish `: (1 : ℤ) ≤ g` using `by exact_mod_cast hg`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨N, hN, y, hy⟩` from `exists_pos_zsmul_mem_range b φ hinj x`. Take `⟨m, hm⟩` from `quad_round_sum hs hQ (fun j => φ (b j)) (fun j => quad_nonneg hQ hp _) N hN (fun j => b.repr y j) Finset.univ`. Use `set χ0 : X := ∑ j, m j • b j with hχ0`. Establish `hNx : N • (x + φ χ0) = ∑ j, (b.repr y j + N * m j) • φ (b j)`.

Establish `hyφ : φ y = ∑ j, b.repr y j • φ (b j)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_add, ← hy, hyφ, hχ0, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, smul_smul, add_smul]`.

Establish `hsc : ∀ z : X, Q (N • z) = N ^ 2 * Q z`. Introduce `z`. Use `quad_add_zsmul hs hQ 0 z N` as an intermediate fact. Simplify using `only [zero_add, quad_zero hQ, map_zero, AddMonoidHom.zero_apply, mul_zero] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hbound : 4 * Q (x + φ χ0) ≤ g * ∑ j, Q (b j)`. Establish `h1 : 4 * Q (N • (x + φ χ0)) ≤ N ^ 2 * ∑ j, Q (φ (b j))`. Rewrite using `[hNx]`. Conclude with `hm`. Rewrite `h1` using `[hsc]`.

Simplify using `only [hQφ, ← Finset.mul_sum] at h1`. Establish `hN2 : 0 < N ^ 2` using `by positivity`. Establish `h2 : N ^ 2 * (4 * Q (x + φ χ0)) ≤ N ^ 2 * (g * ∑ j, Q (b j))` using `by linarith`. Conclude with `le_of_mul_le_mul_left h2 hN2`. Establish `hex : ∃ k : ℕ, ∃ χ : X, Q (x + φ χ) = k` using `⟨(Q (x + φ χ0)).toNat, χ0, (Int.toNat_of_nonneg (quad_nonneg hQ hp _)).symm⟩`.

Take `⟨χ, hχ⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ χ' : X, Q (x + φ χ) ≤ Q (x + φ χ')`. Introduce `χ'`. Rewrite using `[hχ]`. Use `Nat.find_min' hex ⟨χ', (Int.toNat_of_nonneg (quad_nonneg hQ hp (x + φ χ'))).symm⟩` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Use `⟨χ, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : 4 * Q (x + φ χ) ≤ g * ∑ j, Q (b j)` using `by linarith [hmin χ0]`. Establish `h2 : (∑ j, (Q (b j) : ℝ)) ≤ n * Cc`. Combine the equalities or inequalities in the displayed calculation.

Establish `h3 : 4 * (Q (x + φ χ) : ℝ) ≤ g * ∑ j, (Q (b j) : ℝ)` using `by exact_mod_cast h1`. Establish `hg' : (0 : ℝ) ≤ g` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Introduce `q z`. Establish `hz` using `hmin (χ + z)`.

Rewrite `hz` using `[map_add, ← add_assoc]`. Establish `e1` using `quad_add_zsmul hs hQ (x + φ χ) (φ z) 1`. Establish `e2` using `quad_add_zsmul hs hQ (x + φ χ) (φ z) q`. Rewrite `e1` using `[one_smul]`. Rewrite `e2` using `[natCast_zsmul]`.

Rewrite using `[e2]`. Establish `hq0 : (0 : ℤ) ≤ q` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_coset_minimiser :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) → (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) → ∀ (n : ℕ) (b : Module.Basis (Fin n) ℤ X) (Cc : ℝ), (∀ j, (Q (b j) : ℝ) ≤ Cc) → ∀ (φ : X →+ X) (g : ℕ), 1 ≤ g → (∀ x y, Bf (φ x) (φ y) = g * Bf x y) → ∀ x : X, ∃ χ : X, ((Q (x + φ χ) : ℝ) ≤ g * n * Cc / 4) ∧ ∀ (q : ℕ) (z : X), (q : ℤ) * (q - 1) * Q (φ z) ≤ Q (x + φ χ + q • φ z) - Q (x + φ χ) := by
  classical
  intro X _ Bf Q hs hQ hp n b Cc hC φ g hg hφ x
  have hQφ : ∀ z, Q (φ z) = g * Q z := by
    intro z
    have h : 2 * Q (φ z) = 2 * (g * Q z) := by
      rw [hQ, hφ, ← hQ z]; ring
    exact mul_left_cancel₀ two_ne_zero h
  have hinj : Function.Injective φ := by
    intro u v huv
    by_contra hne
    have h0 : φ (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h1 := hp (u - v) (sub_ne_zero.mpr hne)
    have h2 := hQφ (u - v)
    rw [h0, quad_zero hQ] at h2
    have : (1 : ℤ) ≤ g := by exact_mod_cast hg
    nlinarith
  obtain ⟨N, hN, y, hy⟩ := exists_pos_zsmul_mem_range b φ hinj x
  obtain ⟨m, hm⟩ := quad_round_sum hs hQ (fun j => φ (b j))
    (fun j => quad_nonneg hQ hp _) N hN (fun j => b.repr y j) Finset.univ
  set χ0 : X := ∑ j, m j • b j with hχ0
  have hNx : N • (x + φ χ0) = ∑ j, (b.repr y j + N * m j) • φ (b j) := by
    have hyφ : φ y = ∑ j, b.repr y j • φ (b j) := by
      calc φ y = φ (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
        _ = ∑ j, b.repr y j • φ (b j) := by rw [map_sum]; simp only [map_zsmul]
    rw [smul_add, ← hy, hyφ, hχ0, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, add_smul]
  have hsc : ∀ z : X, Q (N • z) = N ^ 2 * Q z := by
    intro z
    have := quad_add_zsmul hs hQ 0 z N
    simp only [zero_add, quad_zero hQ, map_zero, AddMonoidHom.zero_apply, mul_zero] at this
    linarith
  have hbound : 4 * Q (x + φ χ0) ≤ g * ∑ j, Q (b j) := by
    have h1 : 4 * Q (N • (x + φ χ0)) ≤ N ^ 2 * ∑ j, Q (φ (b j)) := by
      rw [hNx]; exact hm
    rw [hsc] at h1
    simp only [hQφ, ← Finset.mul_sum] at h1
    have hN2 : 0 < N ^ 2 := by positivity
    have h2 : N ^ 2 * (4 * Q (x + φ χ0)) ≤ N ^ 2 * (g * ∑ j, Q (b j)) := by linarith
    exact le_of_mul_le_mul_left h2 hN2
  have hex : ∃ k : ℕ, ∃ χ : X, Q (x + φ χ) = k :=
    ⟨(Q (x + φ χ0)).toNat, χ0, (Int.toNat_of_nonneg (quad_nonneg hQ hp _)).symm⟩
  obtain ⟨χ, hχ⟩ := Nat.find_spec hex
  have hmin : ∀ χ' : X, Q (x + φ χ) ≤ Q (x + φ χ') := by
    intro χ'
    rw [hχ]
    have := Nat.find_min' hex ⟨χ', (Int.toNat_of_nonneg (quad_nonneg hQ hp (x + φ χ'))).symm⟩
    calc (Nat.find hex : ℤ) ≤ ((Q (x + φ χ')).toNat : ℤ) := by exact_mod_cast this
      _ = Q (x + φ χ') := Int.toNat_of_nonneg (quad_nonneg hQ hp _)
  refine ⟨χ, ?_, ?_⟩
  · have h1 : 4 * Q (x + φ χ) ≤ g * ∑ j, Q (b j) := by linarith [hmin χ0]
    have h2 : (∑ j, (Q (b j) : ℝ)) ≤ n * Cc := by
      calc (∑ j, (Q (b j) : ℝ)) ≤ ∑ _j : Fin n, Cc := Finset.sum_le_sum fun j _ => hC j
        _ = n * Cc := by simp
    have h3 : 4 * (Q (x + φ χ) : ℝ) ≤ g * ∑ j, (Q (b j) : ℝ) := by exact_mod_cast h1
    have hg' : (0 : ℝ) ≤ g := by positivity
    nlinarith
  · intro q z
    have hz := hmin (χ + z)
    rw [map_add, ← add_assoc] at hz
    have e1 := quad_add_zsmul hs hQ (x + φ χ) (φ z) 1
    have e2 := quad_add_zsmul hs hQ (x + φ χ) (φ z) q
    rw [one_smul] at e1
    rw [natCast_zsmul] at e2
    rw [e2]
    have hq0 : (0 : ℤ) ≤ q := by positivity
    nlinarith

end GlobalTheory
