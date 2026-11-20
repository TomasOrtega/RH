import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid

namespace GlobalTheory

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ Y`. Use `⟨fun y => ∑ i, (b.repr y i).natAbs, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sub, Finsupp.sub_apply]`. Conclude with `Int.natAbs_sub_le _ _`. Introduce `m y`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]`. Introduce `y hy`. Rewrite `hy` using `[Finset.sum_eq_zero_iff]`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`.

Simplify using `using hy i (Finset.mem_univ i)`.
-/
theorem exists_nat_length_lattice (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] :
    ∃ q : Y → ℕ, (∀ x y, q (x - y) ≤ q x + q y) ∧ (∀ (m : ℕ) y, q (m • y) = m * q y) ∧
      ∀ y, q y = 0 → y = 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ Y
  refine ⟨fun y => ∑ i, (b.repr y i).natAbs, ?_, ?_, ?_⟩
  · intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_sub, Finsupp.sub_apply]
    exact Int.natAbs_sub_le _ _
  · intro m y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
  · intro y hy
    rw [Finset.sum_eq_zero_iff] at hy
    apply b.repr.injective
    ext i
    simpa using hy i (Finset.mem_univ i)

/- English proof (translation)
Take `⟨q, h1, h2, h3⟩` from `exists_nat_length_lattice Y`. Use `⟨fun y => ∑ j ∈ Finset.range n, q ((σ ^ j) y), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sub]`. Conclude with `h1 _ _`. Introduce `m y`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_nsmul, h2]`. Introduce `y hy`. Rewrite `hy` using `[Finset.sum_eq_zero_iff]`. Use `hy 0 (Finset.mem_range.mpr hn)` as an intermediate fact. Conclude with `h3 y (by simpa using this)`.

Introduce `y`. Establish `e1` using `Finset.sum_range_succ (fun j => q ((σ ^ j) y)) n`. Establish `e2` using `Finset.sum_range_succ' (fun j => q ((σ ^ j) y)) n`. Establish `e3 : ∑ j ∈ Finset.range n, q ((σ ^ j) (σ y)) = ∑ j ∈ Finset.range n, q ((σ ^ (j + 1)) y)` using `Finset.sum_congr rfl fun j _ => by rw [pow_succ, Module.End.mul_apply]`. Rewrite `e1` using `[hσ]`.

Rewrite `e2` using `[pow_zero]`. Simplify using `only [e3]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_invariant_nat_length_lattice (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y]
    [Module.Finite ℤ Y] (σ : Module.End ℤ Y) (n : ℕ) (hn : 0 < n) (hσ : σ ^ n = 1) :
    ∃ p : Y → ℕ, (∀ x y, p (x - y) ≤ p x + p y) ∧ (∀ (m : ℕ) y, p (m • y) = m * p y) ∧
      (∀ y, p y = 0 → y = 0) ∧ ∀ y, p (σ y) = p y := by
  obtain ⟨q, h1, h2, h3⟩ := exists_nat_length_lattice Y
  refine ⟨fun y => ∑ j ∈ Finset.range n, q ((σ ^ j) y), ?_, ?_, ?_, ?_⟩
  · intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_sub]
    exact h1 _ _
  · intro m y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, h2]
  · intro y hy
    rw [Finset.sum_eq_zero_iff] at hy
    have := hy 0 (Finset.mem_range.mpr hn)
    exact h3 y (by simpa using this)
  · intro y
    have e1 := Finset.sum_range_succ (fun j => q ((σ ^ j) y)) n
    have e2 := Finset.sum_range_succ' (fun j => q ((σ ^ j) y)) n
    have e3 : ∑ j ∈ Finset.range n, q ((σ ^ j) (σ y)) =
        ∑ j ∈ Finset.range n, q ((σ ^ (j + 1)) y) :=
      Finset.sum_congr rfl fun j _ => by rw [pow_succ, Module.End.mul_apply]
    rw [hσ] at e1
    rw [pow_zero] at e2
    simp only [e3]
    omega

/- English proof (translation)
Take `⟨p, h1, h2, h3, h4⟩` from `exists_invariant_nat_length_lattice Y σ n hn hσ`. Establish `key : ∀ (k : ℕ) (y : Y), p y = k → σ y = y`. Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`.

Introduce `y hy`. Take `⟨z, hz⟩` from `h y`. Break down `Nat.eq_zero_or_pos k with hk | hk` into its components or cases. Establish `: y = 0` using `h3 y (hy.trans hk)`. Rewrite using `[this, map_zero]`.

Establish `hle : M * p z ≤ k + k`. Use `h1 (σ y) y` as an intermediate fact. Rewrite `this` using `[h4, hy, hz, add_sub_cancel_left, h2]`. Conclude with `this`. Establish `hlt : p z < k` using `by nlinarith`.

Establish `hzz : σ z = z` using `ih _ hlt z rfl`. Establish `hj : ∀ j : ℕ, (σ ^ j) y = y + (j * M) • z`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`.

Consider the case `succ j ihj`. Rewrite using `[pow_succ', Module.End.mul_apply, ihj, map_add, map_nsmul, hzz, hz, add_mul, one_mul, add_smul]`. Normalize the expressions using the abelian group laws. Establish `h0 : (n * M) • z = 0`. Use `hj n` as an intermediate fact.

Rewrite `this` using `[hσ, Module.End.one_apply]`. Conclude with `left_eq_add.mp this`. Establish `h00 : p z = 0`. Establish `e` using `h2 (n * M) z`. Establish `e0` using `h2 0 z`.

Rewrite `e0` using `[zero_smul, zero_mul]`. Rewrite `e` using `[h0, e0]`. Establish `: 0 < n * M` using `Nat.mul_pos hn (by omega)`. Break down `Nat.mul_eq_zero.mp e.symm with h' | h'` into its components or cases. Use linear arithmetic over natural numbers and integers.

Conclude with `h'`. Rewrite using `[hz, h3 z h00, smul_zero, add_zero]`. Use extensionality with `y`. Conclude with `key _ y rfl`.
-/
theorem end_eq_one_of_pow_eq_one_of_congr (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y]
    [Module.Finite ℤ Y] (σ : Module.End ℤ Y) (n M : ℕ) (hn : 0 < n) (hσ : σ ^ n = 1) (hM : 3 ≤ M)
    (h : ∀ y, ∃ z, σ y = y + M • z) : σ = 1 := by
  obtain ⟨p, h1, h2, h3, h4⟩ := exists_invariant_nat_length_lattice Y σ n hn hσ
  have key : ∀ (k : ℕ) (y : Y), p y = k → σ y = y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro y hy
      obtain ⟨z, hz⟩ := h y
      rcases Nat.eq_zero_or_pos k with hk | hk
      · have : y = 0 := h3 y (hy.trans hk)
        rw [this, map_zero]
      have hle : M * p z ≤ k + k := by
        have := h1 (σ y) y
        rw [h4, hy, hz, add_sub_cancel_left, h2] at this
        exact this
      have hlt : p z < k := by nlinarith
      have hzz : σ z = z := ih _ hlt z rfl
      have hj : ∀ j : ℕ, (σ ^ j) y = y + (j * M) • z := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          rw [pow_succ', Module.End.mul_apply, ihj, map_add, map_nsmul, hzz, hz, add_mul, one_mul,
            add_smul]
          abel
      have h0 : (n * M) • z = 0 := by
        have := hj n
        rw [hσ, Module.End.one_apply] at this
        exact left_eq_add.mp this
      have h00 : p z = 0 := by
        have e := h2 (n * M) z
        have e0 := h2 0 z
        rw [zero_smul, zero_mul] at e0
        rw [h0, e0] at e
        have : 0 < n * M := Nat.mul_pos hn (by omega)
        rcases Nat.mul_eq_zero.mp e.symm with h' | h'
        · omega
        · exact h'
      rw [hz, h3 z h00, smul_zero, add_zero]
  ext y
  exact key _ y rfl

/- English proof (translation)
Introduce `Y _ _ _ σ n M hn hσ hM h`. Establish `hp : (σ : Module.End ℤ Y) ^ n = 1`. Use extensionality with `y`. Establish `: (σ ^ n) y = y` using `by rw [hσ]; rfl`. Rewrite `this` using `[LinearEquiv.pow_apply]`.

Rewrite using `[Module.End.pow_apply]`. Conclude with `this`. Use `end_eq_one_of_pow_eq_one_of_congr Y (σ : Module.End ℤ Y) n M hn hp hM h` as an intermediate fact. Use extensionality with `y`. Conclude with `LinearMap.congr_fun this y`.
-/
theorem latMinkowski : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LatMinkowskiSt := by
  intro Y _ _ _ σ n M hn hσ hM h
  have hp : (σ : Module.End ℤ Y) ^ n = 1 := by
    ext y
    have : (σ ^ n) y = y := by rw [hσ]; rfl
    rw [LinearEquiv.pow_apply] at this
    rw [Module.End.pow_apply]
    exact this
  have := end_eq_one_of_pow_eq_one_of_congr Y (σ : Module.End ℤ Y) n M hn hp hM h
  ext y
  exact LinearMap.congr_fun this y

end GlobalTheory
