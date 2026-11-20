import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff

set_option autoImplicit false

open GlobalTheory.HTLat

namespace GlobalTheory

/- English proof (translation)
Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Set `T : ℕ → Subgroup M` to `fun n => (powMonoidHom (l ^ n)).ker`. Establish `hT : ∀ n, Nat.card (T n) = l ^ (c * n)` using `fun n => by`. Rewrite using `[← hcard n]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [T, MonoidHom.mem_ker])`.

Set `φ : T (k + 1) →* M` to `(powMonoidHom l).comp (T (k + 1)).subtype`. Establish `hker : Nat.card φ.ker = l ^ c`. Rewrite using `[← mul_one c, ← hT 1]`. Use `Nat.card_congr { toFun := fun y => ⟨y.1.1, ?_⟩ invFun := fun z => ⟨⟨z.1, ?_⟩, ?_⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }` and prove the remaining obligations. Use `y.2` as an intermediate fact.

Simplify using `only [T, φ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply, Subgroup.coe_subtype] at this`. Simplify `this` using `[T, MonoidHom.mem_ker]`. Establish `hz : (z : M) ^ l = 1` using `by simpa [T] using MonoidHom.mem_ker.1 z.2`. Simplify using `only [T, MonoidHom.mem_ker, powMonoidHom_apply]`. Rewrite using `[pow_succ' l k, pow_mul, hz, one_pow]`.

Use `z.2` as an intermediate fact. Simplify `this` using `[T, φ, MonoidHom.mem_ker]`. Establish `hrange : Nat.card φ.range = l ^ (c * k)`. Establish `h1` using `Subgroup.card_mul_index φ.ker`. Rewrite `h1` using `[Subgroup.index_ker, hker, hT (k + 1), mul_add, mul_one, pow_add, mul_comm]`.

Conclude with `Nat.eq_of_mul_eq_mul_right (pow_pos hl c) h1`. Establish `hfin : Finite (T k)` using `Nat.finite_of_card_ne_zero (by rw [hT k]; exact (pow_pos hl _).ne')`. Establish `hle : φ.range ≤ T k`. Introduce and unpack `_ ⟨z, rfl⟩`. Use `z.2` as an intermediate fact.

Simplify using `only [T, MonoidHom.mem_ker, powMonoidHom_apply] at this ⊢`. Simplify using `only [φ, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply, Subgroup.coe_subtype]`. Rewrite using `[← pow_mul, ← pow_succ', this]`. Establish `heq : φ.range = T k` using `Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hT k])`. Establish `hyT : y ∈ T k` using `by simpa [T, MonoidHom.mem_ker] using hy`.

Rewrite `hyT` using `[← heq]`. Take `⟨z, hz⟩` from `hyT`. Conclude with `⟨z.1, MonoidHom.mem_ker.1 z.2, hz⟩`.
-/
theorem exists_pow_prime_root_of_card_torsion {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    {c : ℕ} (hcard : ∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) (k : ℕ) (y : M)
    (hy : y ^ (l ^ k) = 1) : ∃ z : M, z ^ (l ^ (k + 1)) = 1 ∧ z ^ l = y := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let T : ℕ → Subgroup M := fun n => (powMonoidHom (l ^ n)).ker
  have hT : ∀ n, Nat.card (T n) = l ^ (c * n) := fun n => by
    rw [← hcard n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [T, MonoidHom.mem_ker])
  let φ : T (k + 1) →* M := (powMonoidHom l).comp (T (k + 1)).subtype
  have hker : Nat.card φ.ker = l ^ c := by
    rw [← mul_one c, ← hT 1]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, ?_⟩
        invFun := fun z => ⟨⟨z.1, ?_⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := y.2
      simp only [T, φ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        powMonoidHom_apply, Subgroup.coe_subtype] at this
      simpa [T, MonoidHom.mem_ker] using this
    · have hz : (z : M) ^ l = 1 := by simpa [T] using MonoidHom.mem_ker.1 z.2
      simp only [T, MonoidHom.mem_ker, powMonoidHom_apply]
      rw [pow_succ' l k, pow_mul, hz, one_pow]
    · have := z.2
      simpa [T, φ, MonoidHom.mem_ker] using this
  have hrange : Nat.card φ.range = l ^ (c * k) := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hker, hT (k + 1), mul_add, mul_one, pow_add, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hl c) h1
  have hfin : Finite (T k) := Nat.finite_of_card_ne_zero (by rw [hT k]; exact (pow_pos hl _).ne')
  have hle : φ.range ≤ T k := by
    rintro _ ⟨z, rfl⟩
    have := z.2
    simp only [T, MonoidHom.mem_ker, powMonoidHom_apply] at this ⊢
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply,
      Subgroup.coe_subtype]
    rw [← pow_mul, ← pow_succ', this]
  have heq : φ.range = T k := Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hT k])
  have hyT : y ∈ T k := by simpa [T, MonoidHom.mem_ker] using hy
  rw [← heq] at hyT
  obtain ⟨z, hz⟩ := hyT
  exact ⟨z.1, MonoidHom.mem_ker.1 z.2, hz⟩

/- English proof (translation)
Introduce `M _ l _ c hcard N x hx`. Establish `h` using `exists_pow_prime_root_of_card_torsion hcard`. Use `choose r hr1 hr2 using h`. Set `g : (n : ℕ) → {y : M // y ^ (l ^ (N + n)) = 1}` to `fun n => Nat.rec ⟨x, hx⟩ (fun n y => ⟨r (N + n) y.1 y.2, hr1 (N + n) y.1 y.2⟩) n`. Establish `hg0 : (g 0).1 = x` using `rfl`.

Establish `hgs : ∀ n, (g (n + 1)).1 ^ l = (g n).1` using `fun n => hr2 (N + n) (g n).1 (g n).2`. Establish `hgk : ∀ n k, (g (n + k)).1 ^ (l ^ k) = (g n).1` using `fun n k => by`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[pow_succ', pow_mul]`. Use `show ((g (n + k + 1)).1 ^ l) ^ (l ^ k) = _`. Rewrite using `[hgs, ih]`. Set `s : ℕ → M` to `fun n => (g n).1 ^ (l ^ N)`. Establish `hs : ∀ n, s n ^ l ^ n = 1 ∧ s (n + 1) ^ l = s n` using `fun n => by`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [s]`. Rewrite using `[← pow_mul, ← pow_add, (g n).2]`. Simplify using `only [s]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hgs]`.

Use `⟨Tate.mk s hs, ?_⟩` and prove the remaining obligations. Rewrite using `[Tate.lev_mk]`. Simplify using `only [s]`. Use `hgk 0 N` as an intermediate fact. Rewrite `this` using `[zero_add]`.

Rewrite using `[this, hg0]`.
-/
theorem exists_tate_lev_eq_of_card_torsion :
    ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ),
      (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) →
      ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  intro M _ l _ c hcard N x hx
  have h := exists_pow_prime_root_of_card_torsion hcard
  choose r hr1 hr2 using h
  let g : (n : ℕ) → {y : M // y ^ (l ^ (N + n)) = 1} := fun n =>
    Nat.rec ⟨x, hx⟩ (fun n y => ⟨r (N + n) y.1 y.2, hr1 (N + n) y.1 y.2⟩) n
  have hg0 : (g 0).1 = x := rfl
  have hgs : ∀ n, (g (n + 1)).1 ^ l = (g n).1 := fun n => hr2 (N + n) (g n).1 (g n).2
  have hgk : ∀ n k, (g (n + k)).1 ^ (l ^ k) = (g n).1 := fun n k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_mul]
      show ((g (n + k + 1)).1 ^ l) ^ (l ^ k) = _
      rw [hgs, ih]
  let s : ℕ → M := fun n => (g n).1 ^ (l ^ N)
  have hs : ∀ n, s n ^ l ^ n = 1 ∧ s (n + 1) ^ l = s n := fun n => by
    refine ⟨?_, ?_⟩
    · simp only [s]
      rw [← pow_mul, ← pow_add, (g n).2]
    · simp only [s]
      rw [← pow_mul, mul_comm, pow_mul, hgs]
  refine ⟨Tate.mk s hs, ?_⟩
  rw [Tate.lev_mk]
  simp only [s]
  have := hgk 0 N
  rw [zero_add] at this
  rw [this, hg0]

end GlobalTheory
