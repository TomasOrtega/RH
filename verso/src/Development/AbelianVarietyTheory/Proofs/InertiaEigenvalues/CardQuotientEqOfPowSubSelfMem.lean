import Mathlib
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ P _ q ζ hq hζ hprim hall`. Use `letI : Field (R ⧸ P) := Ideal.Quotient.field P`. Establish `hfix : ∀ x : R ⧸ P, x ^ q = x`. Introduce `x`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Rewrite using `[← sub_eq_zero, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hall y`. Use `set f : Polynomial (R ⧸ P) := X ^ q - X with hf`. Establish `hdeg : f.natDegree = q`. Apply the tactic sequence `rw [hf, natDegree_sub_eq_left_of_natDegree_lt] <;> simp <;> omega`.

Establish `hf0 : f ≠ 0`. Introduce `h`. Rewrite `hdeg` using `[h, natDegree_zero]`. Use linear arithmetic over natural numbers and integers. Establish `hmem : ∀ x : R ⧸ P, x ∈ f.roots.toFinset`.

Introduce `x`. Rewrite using `[Multiset.mem_toFinset, mem_roots hf0]`. Simplify using `[hf, hfix x]`. Use `haveI : Finite (R ⧸ P) := by`. Apply `Finite.of_injective (fun x : R ⧸ P => (⟨x, hmem x⟩ : f.roots.toFinset))` to reduce the goal to its premises.

Introduce `a b h`. Simplify using `using congrArg Subtype.val h`. Use `letI : Fintype (R ⧸ P) := Fintype.ofFinite _`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Nat.card_eq_fintype_card]`.

Combine the equalities or inequalities in the displayed calculation. Use `set z : R ⧸ P := Ideal.Quotient.mk P ζ with hz`. Establish `hz1 : z ^ (q - 1) = 1` using `by rw [hz, ← map_pow, hζ, map_one]`. Establish `hz0 : z ≠ 0`. Introduce `h; rw [h, zero_pow (by omega)] at hz1; exact zero_ne_one hz1`.

Establish `hord : orderOf z = q - 1`. Rewrite using `[orderOf_eq_iff (by omega)]`. Use `⟨hz1, fun m hm hm0 h => hprim m hm0 hm ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, ← hz, h, sub_self]`. Establish `hinj` using `pow_injOn_Iio_orderOf (x := z)`.

Rewrite `hinj` using `[hord]`. Set `g : Fin q → R ⧸ P` to `fun i => if (i : ℕ) = 0 then 0 else z ^ ((i : ℕ) - 1)`. Establish `hg : Function.Injective g`. Introduce `a b hab`. Simplify using `only [g] at hab`.

Apply `Fin.ext` to reduce the goal to its premises. Apply the tactic sequence `by_cases ha : (a : ℕ) = 0 <;> by_cases hb : (b : ℕ) = 0 <;> simp only [ha, hb, if_true, if_false] at hab`. Use linear arithmetic over natural numbers and integers. Conclude with `absurd hab.symm (pow_ne_zero _ hz0)`. Conclude with `absurd hab (pow_ne_zero _ hz0)`.

Use `hinj (show (a : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega) (show (b : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega) hab` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `Nat.card_le_card_of_injective g hg` as an intermediate fact. Simplify using `using this`.
-/
theorem card_quotient_eq_of_pow_sub_self_mem : ∀ {R : Type} [CommRing R] (P : Ideal R) [P.IsMaximal] (q : ℕ) (ζ : R), 2 ≤ q → ζ ^ (q - 1) = 1 →
    (∀ j : ℕ, 0 < j → j < q - 1 → ζ ^ j - 1 ∉ P) → (∀ y : R, y ^ q - y ∈ P) → Nat.card (R ⧸ P) = q := by
  intro R _ P _ q ζ hq hζ hprim hall
  classical
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hfix : ∀ x : R ⧸ P, x ^ q = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hall y
  set f : Polynomial (R ⧸ P) := X ^ q - X with hf
  have hdeg : f.natDegree = q := by
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt] <;> simp <;> omega
  have hf0 : f ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; omega
  have hmem : ∀ x : R ⧸ P, x ∈ f.roots.toFinset := by
    intro x
    rw [Multiset.mem_toFinset, mem_roots hf0]
    simp [hf, hfix x]
  haveI : Finite (R ⧸ P) := by
    apply Finite.of_injective (fun x : R ⧸ P => (⟨x, hmem x⟩ : f.roots.toFinset))
    intro a b h; simpa using congrArg Subtype.val h
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    calc Fintype.card (R ⧸ P) = (Finset.univ : Finset (R ⧸ P)).card := rfl
      _ ≤ f.roots.toFinset.card := Finset.card_le_card (fun x _ => hmem x)
      _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := card_roots' f
      _ = q := hdeg
  · set z : R ⧸ P := Ideal.Quotient.mk P ζ with hz
    have hz1 : z ^ (q - 1) = 1 := by rw [hz, ← map_pow, hζ, map_one]
    have hz0 : z ≠ 0 := by
      intro h; rw [h, zero_pow (by omega)] at hz1; exact zero_ne_one hz1
    have hord : orderOf z = q - 1 := by
      rw [orderOf_eq_iff (by omega)]
      refine ⟨hz1, fun m hm hm0 h => hprim m hm0 hm ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, ← hz, h, sub_self]
    have hinj := pow_injOn_Iio_orderOf (x := z)
    rw [hord] at hinj
    let g : Fin q → R ⧸ P := fun i => if (i : ℕ) = 0 then 0 else z ^ ((i : ℕ) - 1)
    have hg : Function.Injective g := by
      intro a b hab
      simp only [g] at hab
      apply Fin.ext
      by_cases ha : (a : ℕ) = 0 <;> by_cases hb : (b : ℕ) = 0 <;> simp only [ha, hb, if_true, if_false] at hab
      · omega
      · exact absurd hab.symm (pow_ne_zero _ hz0)
      · exact absurd hab (pow_ne_zero _ hz0)
      · have := hinj (show (a : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega)
          (show (b : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega) hab
        omega
    have := Nat.card_le_card_of_injective g hg
    simpa using this

end GlobalTheory
