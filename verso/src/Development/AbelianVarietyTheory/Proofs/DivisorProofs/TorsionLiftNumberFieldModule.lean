import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Set `A : ℕ → AddSubgroup M` to `fun k => (DistribMulAction.toAddMonoidHom M (N ^ k)).ker`. Establish `hA : ∀ k x, x ∈ A k ↔ (N ^ k) • x = 0` using `fun k x => by`. Simplify using `[A, AddMonoidHom.mem_ker]`. Establish `hcard : ∀ k, Nat.card (A k) = (N ^ k) ^ e` using `fun k => by`. Rewrite using `[← h k]`.

Conclude with `Nat.card_congr (Equiv.subtypeEquivRight (hA k))`. Establish `hpos : ∀ k, 0 < (N ^ k) ^ e` using `fun k => by positivity`. Establish `hfin : ∀ k, Finite (A k)` using `fun k => Nat.finite_of_card_ne_zero (by rw [hcard k]; exact (hpos k).ne')`. Set `ψ : A (j + 1) →+ M` to `(DistribMulAction.toAddMonoidHom M N).comp (A (j + 1)).subtype`. Establish `hψ : ∀ z : A (j + 1), ψ z = N • (z : M)` using `fun z => rfl`.

Establish `hN1 : ∀ x : M, x ∈ A 1 ↔ N • x = 0` using `fun x => by rw [hA 1 x, pow_one]`. Establish `hker : Nat.card ψ.ker = Nat.card (A 1)`. Use `Nat.card_congr ?_` and prove the remaining obligations. Use `{ toFun := fun z => ⟨(z.1 : M), (hN1 _).2 (by rw [← hψ]; exact AddMonoidHom.mem_ker.1 z.2)⟩ invFun := fun z => ⟨⟨(z : M), (hA (j+1) _).2 (by` and prove the remaining obligations. Rewrite using `[pow_succ, mul_smul, (hN1 _).1 z.2, smul_zero])⟩,`.

Use the proof step `AddMonoidHom.mem_ker.2 (by rw [hψ]; exact (hN1 _).1 z.2)⟩`. Use `left_inv := fun z => rfl`. Use `right_inv := fun z => rfl }`. Establish `hle : ψ.range ≤ A j`. Introduce and unpack `_ ⟨z, rfl⟩`.

Rewrite using `[hA, hψ, ← mul_smul, ← pow_succ]`. Conclude with `(hA (j+1) _).1 z.2`. Establish `hmul` using `AddSubgroup.card_mul_index ψ.ker`. Rewrite `hmul` using `[AddSubgroup.index_ker]`. Establish `hrange : Nat.card (Set.range ψ) = Nat.card (A j)`.

Establish `e1 : (N ^ (j + 1)) ^ e = (N ^ 1) ^ e * (N ^ j) ^ e`. Rewrite using `[← mul_pow, ← pow_add, add_comm]`. Rewrite `hmul` using `[hker, hcard, hcard, e1]`. Rewrite using `[hcard]`. Conclude with `Nat.eq_of_mul_eq_mul_left (hpos 1) hmul`.

Establish `heq : ψ.range = A j`. Use `AddSubgroup.eq_of_le_of_card_ge hle ?_` and prove the remaining obligations. Rewrite using `[← hrange]`. Conclude with `le_of_eq (Nat.card_congr (Equiv.setCongr (AddMonoidHom.coe_range ψ)).symm)`. Establish `hyr : y ∈ ψ.range` using `by rw [heq]; exact (hA j y).2 hy`.

Take `⟨z, hz⟩` from `hyr`. Conclude with `⟨z, (hA (j+1) _).1 z.2, hz⟩`.
-/
theorem nsmul_surjective_torsion_lift (M : Type) [AddCommGroup M] (N e : ℕ) (hN : 1 ≤ N)
    (h : ∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ e)
    (j : ℕ) (y : M) (hy : (N ^ j) • y = 0) :
    ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  let A : ℕ → AddSubgroup M := fun k => (DistribMulAction.toAddMonoidHom M (N ^ k)).ker
  have hA : ∀ k x, x ∈ A k ↔ (N ^ k) • x = 0 := fun k x => by
    simp [A, AddMonoidHom.mem_ker]
  have hcard : ∀ k, Nat.card (A k) = (N ^ k) ^ e := fun k => by
    rw [← h k]; exact Nat.card_congr (Equiv.subtypeEquivRight (hA k))
  have hpos : ∀ k, 0 < (N ^ k) ^ e := fun k => by positivity
  have hfin : ∀ k, Finite (A k) := fun k =>
    Nat.finite_of_card_ne_zero (by rw [hcard k]; exact (hpos k).ne')
  let ψ : A (j + 1) →+ M := (DistribMulAction.toAddMonoidHom M N).comp (A (j + 1)).subtype
  have hψ : ∀ z : A (j + 1), ψ z = N • (z : M) := fun z => rfl
  have hN1 : ∀ x : M, x ∈ A 1 ↔ N • x = 0 := fun x => by rw [hA 1 x, pow_one]
  have hker : Nat.card ψ.ker = Nat.card (A 1) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun z => ⟨(z.1 : M), (hN1 _).2 (by rw [← hψ]; exact AddMonoidHom.mem_ker.1 z.2)⟩
        invFun := fun z => ⟨⟨(z : M), (hA (j+1) _).2 (by
            rw [pow_succ, mul_smul, (hN1 _).1 z.2, smul_zero])⟩,
            AddMonoidHom.mem_ker.2 (by rw [hψ]; exact (hN1 _).1 z.2)⟩
        left_inv := fun z => rfl
        right_inv := fun z => rfl }
  have hle : ψ.range ≤ A j := by
    rintro _ ⟨z, rfl⟩
    rw [hA, hψ, ← mul_smul, ← pow_succ]
    exact (hA (j+1) _).1 z.2
  have hmul := AddSubgroup.card_mul_index ψ.ker
  rw [AddSubgroup.index_ker] at hmul
  have hrange : Nat.card (Set.range ψ) = Nat.card (A j) := by
    have e1 : (N ^ (j + 1)) ^ e = (N ^ 1) ^ e * (N ^ j) ^ e := by
      rw [← mul_pow, ← pow_add, add_comm]
    rw [hker, hcard, hcard, e1] at hmul
    rw [hcard]
    exact Nat.eq_of_mul_eq_mul_left (hpos 1) hmul
  have heq : ψ.range = A j := by
    refine AddSubgroup.eq_of_le_of_card_ge hle ?_
    rw [← hrange]
    exact le_of_eq (Nat.card_congr (Equiv.setCongr (AddMonoidHom.coe_range ψ)).symm)
  have hyr : y ∈ ψ.range := by rw [heq]; exact (hA j y).2 hy
  obtain ⟨z, hz⟩ := hyr
  exact ⟨z, (hA (j+1) _).1 z.2, hz⟩

/- English proof (translation)
Introduce `F _ _ M _ _ N hN h j y hy`. Conclude with `nsmul_surjective_torsion_lift M N _ hN h j y hy`.
-/
theorem nsmul_surj_of_card_torsion :
    ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F)) →
    ∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  intro F _ _ M _ _ N hN h j y hy
  exact nsmul_surjective_torsion_lift M N _ hN h j y hy

end GlobalTheory
