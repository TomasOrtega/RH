import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

open Polynomial

/- English proof (translation)
Establish `h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x)`. Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression. Establish `hd : ((j : ℕ) + 1) ∣ N.factorial` using `Nat.dvd_factorial (Nat.succ_pos _) j.isLt`. Unfold `symTup`.

Rewrite using `[h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]`.
-/
private theorem symTup_mul_left {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (a : R) (j : Fin N) :
    symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j := by
  have h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x) := by
    rw [Multiset.map_map]; rfl
  have hd : ((j : ℕ) + 1) ∣ N.factorial := Nat.dvd_factorial (Nat.succ_pos _) j.isLt
  unfold symTup
  rw [h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]

/- English proof (translation)
Set `A : Fin (N + 1) → Set K` to `fun k => {x | ((k : ℕ) = 0 → x = 1) ∧ ∀ j : Fin N, (j : ℕ) + 1 = k → x ^ (N.factorial / ((j : ℕ) + 1)) = e j}`. Establish `hA : ∀ k, (A k).Finite`. Introduce `k`. Distinguish the cases in `hk : (k : ℕ) = 0`. Conclude with `(Set.finite_singleton (1 : K)).subset fun x hx => hx.1 hk`.

Establish `hk1 : (k : ℕ) - 1 < N` using `by omega`. Set `j : Fin N` to `⟨(k : ℕ) - 1, hk1⟩`. Establish `hj : (j : ℕ) + 1 = k` using `by simp [j]; omega`. Establish `hpos : 0 < N.factorial / ((j : ℕ) + 1)` using `Nat.div_pos ((Nat.succ_le_of_lt j.isLt).trans (Nat.self_le_factorial N)) (Nat.succ_pos _)`. Use `(Polynomial.finite_setOf_isRoot (X_pow_sub_C_ne_zero hpos (e j))).subset ?_` and prove the remaining obligations.

Introduce `x hx`. Simplify using `[IsRoot, hx.2 j hj]`. Set `V : Set (Fin (N + 1) → K)` to `Set.pi Set.univ A`. Establish `hV : V.Finite` using `Set.Finite.pi hA`. Set `poly : (Fin (N + 1) → K) → K[X]` to `fun s => ∑ k : Fin (N + 1), (-1) ^ (k : ℕ) * (C (s k) * X ^ (N - (k : ℕ)))`.

Set `R : Set K` to `⋃ p ∈ poly '' V, {x | x ∈ p.roots}`. Establish `hR : R.Finite` using `(hV.image poly).biUnion fun p _ => Multiset.finite_toSet p.roots`. Use `(Set.Finite.pi (t := fun _ : Fin N => R) fun _ => hR).subset ?_` and prove the remaining obligations. Introduce `c hc`. Simplify using `only [Set.mem_setOf_eq] at hc`.

Set `m : Multiset K` to `Finset.univ.val.map c`. Establish `hm : Multiset.card m = N` using `by simp [m]`. Set `s : Fin (N + 1) → K` to `fun k => m.esymm k`. Establish `hs : s ∈ V`. Introduce `k _`.

Use `⟨fun hk => ?_, fun j hj => ?_⟩` and prove the remaining obligations. Simplify using `[s, hk, Multiset.esymm]`. Use `congrFun hc j` as an intermediate fact. Simplify using `only [symTup] at this`. Simplify using `only [s, ← hj]`.

Conclude with `this`. Establish `hpoly : poly s = (m.map fun t => X - C t).prod`. Rewrite using `[Multiset.prod_X_sub_X_eq_sum_esymm, hm, Finset.sum_range (fun j => (-1) ^ j * (C (m.esymm j) * X ^ (N - j)))]`. Introduce `a _`. Simplify using `only [R, Set.mem_iUnion, Set.mem_image]`.

Use `⟨poly s, ⟨s, hs, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, hpoly, Polynomial.roots_multiset_prod_X_sub_C]`. Conclude with `Multiset.mem_map_of_mem c (Finset.mem_univ a)`.
-/
theorem symTup_eq_finite (K : Type) [Field K] (N : ℕ) (e : Fin N → K) :
    {c : Fin N → K | symTup c = e}.Finite := by
  classical

  let A : Fin (N + 1) → Set K := fun k =>
    {x | ((k : ℕ) = 0 → x = 1) ∧ ∀ j : Fin N, (j : ℕ) + 1 = k → x ^ (N.factorial / ((j : ℕ) + 1)) = e j}
  have hA : ∀ k, (A k).Finite := by
    intro k
    by_cases hk : (k : ℕ) = 0
    · exact (Set.finite_singleton (1 : K)).subset fun x hx => hx.1 hk
    · have hk1 : (k : ℕ) - 1 < N := by omega
      let j : Fin N := ⟨(k : ℕ) - 1, hk1⟩
      have hj : (j : ℕ) + 1 = k := by simp [j]; omega
      have hpos : 0 < N.factorial / ((j : ℕ) + 1) :=
        Nat.div_pos ((Nat.succ_le_of_lt j.isLt).trans (Nat.self_le_factorial N)) (Nat.succ_pos _)
      refine (Polynomial.finite_setOf_isRoot (X_pow_sub_C_ne_zero hpos (e j))).subset ?_
      intro x hx
      simp [IsRoot, hx.2 j hj]
  let V : Set (Fin (N + 1) → K) := Set.pi Set.univ A
  have hV : V.Finite := Set.Finite.pi hA
  let poly : (Fin (N + 1) → K) → K[X] := fun s =>
    ∑ k : Fin (N + 1), (-1) ^ (k : ℕ) * (C (s k) * X ^ (N - (k : ℕ)))
  let R : Set K := ⋃ p ∈ poly '' V, {x | x ∈ p.roots}
  have hR : R.Finite := (hV.image poly).biUnion fun p _ => Multiset.finite_toSet p.roots
  refine (Set.Finite.pi (t := fun _ : Fin N => R) fun _ => hR).subset ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  let m : Multiset K := Finset.univ.val.map c
  have hm : Multiset.card m = N := by simp [m]
  let s : Fin (N + 1) → K := fun k => m.esymm k
  have hs : s ∈ V := by
    intro k _
    refine ⟨fun hk => ?_, fun j hj => ?_⟩
    · simp [s, hk, Multiset.esymm]
    · have := congrFun hc j
      simp only [symTup] at this
      simp only [s, ← hj]
      exact this
  have hpoly : poly s = (m.map fun t => X - C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hm, Finset.sum_range (fun j => (-1) ^ j * (C (m.esymm j) * X ^ (N - j)))]
  intro a _
  simp only [R, Set.mem_iUnion, Set.mem_image]
  refine ⟨poly s, ⟨s, hs, rfl⟩, ?_⟩
  simp only [Set.mem_setOf_eq, hpoly, Polynomial.roots_multiset_prod_X_sub_C]
  exact Multiset.mem_map_of_mem c (Finset.mem_univ a)

/- English proof (translation)
Introduce `K _ _ N e`. Use `⟨(symTup_eq_finite K N e).toFinset, ?_⟩` and prove the remaining obligations. Introduce `c a ha hc`. Take `⟨mu, hmu⟩` from `IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.factorial_pos N)`. Establish `hmu0 : mu ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hmu` using `[zero_pow (Nat.factorial_pos N).ne']`. Conclude with `inv_ne_zero ha hmu.symm`. Use `⟨mu, hmu0, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq]`.

Use function extensionality and compare the values at `j`. Rewrite using `[symTup_mul_left, hmu, hc, ← _root_.mul_assoc, inv_mul_cancel₀ ha, _root_.one_mul]`.
-/
theorem symTup_scale_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : ℕ) (e : Fin N → K), ∃ T : Finset (Fin N → K),
    ∀ (c : Fin N → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) → ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T := by
  intro K _ _ N e
  refine ⟨(symTup_eq_finite K N e).toFinset, ?_⟩
  intro c a ha hc
  obtain ⟨mu, hmu⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.factorial_pos N)
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.factorial_pos N).ne'] at hmu
    exact inv_ne_zero ha hmu.symm
  refine ⟨mu, hmu0, ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  funext j
  rw [symTup_mul_left, hmu, hc, ← _root_.mul_assoc, inv_mul_cancel₀ ha, _root_.one_mul]

end GlobalTheory.UMin
