import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

def levMat {g N : ℕ} (S : Finset (Fin N × Fin N)) (f : S → ZMod g) : Matrix (Fin N) (Fin N) (ZMod g) :=
  fun a b => if h : (a, b) ∈ S then f ⟨(a, b), h⟩ else if a = b then 1 else 0

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `a _`. Establish `: (a, a) ∉ S` using `fun h => lt_irrefl _ (hS _ h)`. Simplify using `[levMat, this]`.

Introduce `a b hab`. Establish `hab' : b < a` using `hab`. Establish `: (a, b) ∉ S` using `fun h => lt_asymm hab' (hS _ h)`. Simplify using `[levMat, this, hab'.ne']`.
-/
theorem levMat_det {g N : ℕ} (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 < p.2) (f : S → ZMod g) :
    (levMat S f).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro a _
    have : (a, a) ∉ S := fun h => lt_irrefl _ (hS _ h)
    simp [levMat, this]
  · intro a b hab
    have hab' : b < a := hab
    have : (a, b) ∉ S := fun h => lt_asymm hab' (hS _ h)
    simp [levMat, this, hab'.ne']

/- English proof (translation)
Establish `e : {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} ≃ (S → ZMod g)` using `{ toFun := fun u p => u.1.val p.1.1 p.1.2 invFun := fun f => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (levMat S f) (by rw [levMat_det S hS]; exact one_ne_zero), by`. Use `⟨fun a => ?_, fun a b hab h => ?_⟩` and prove the remaining obligations. Establish `: (a, a) ∉ S` using `fun h => lt_irrefl _ (hS _ h) show levMat S f a a = 1`. Simplify using `[levMat, this]`. Use `show levMat S f a b = 0`.

Simplify using `[levMat, h, hab]⟩`. Use `left_inv := fun u => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`.

Use `show levMat S (fun p => u.1.val p.1.1 p.1.2) a b = u.1.val a b`. Unfold `levMat`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression. Substitute `h2` using the available equality.

Conclude with `(u.2.1 a).symm`. Conclude with `(u.2.2 a b h2 h1).symm`. Use `right_inv := fun f => by`. Use function extensionality and compare the values at `p`. Use `show levMat S f p.1.1 p.1.2 = f p`.

Simplify using `[levMat, p.2] }`. Rewrite using `[Nat.card_congr e, Nat.card_fun, Nat.card_zmod]`. Simplify using the standard rewrite rules.
-/
theorem card_up_supp (g : ℕ) [Fact g.Prime] (N : ℕ) (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 < p.2) :
    Nat.card {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} = g ^ S.card := by
  have e : {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} ≃ (S → ZMod g) :=
    { toFun := fun u p => u.1.val p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (levMat S f) (by rw [levMat_det S hS]; exact one_ne_zero), by
        refine ⟨fun a => ?_, fun a b hab h => ?_⟩
        · have : (a, a) ∉ S := fun h => lt_irrefl _ (hS _ h)
          show levMat S f a a = 1
          simp [levMat, this]
        · show levMat S f a b = 0
          simp [levMat, h, hab]⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        ext a b
        show levMat S (fun p => u.1.val p.1.1 p.1.2) a b = u.1.val a b
        unfold levMat
        split_ifs with h1 h2
        · rfl
        · subst h2; exact (u.2.1 a).symm
        · exact (u.2.2 a b h2 h1).symm
      right_inv := fun f => by
        funext p
        show levMat S f p.1.1 p.1.2 = f p
        simp [levMat, p.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod]
  simp

/- English proof (translation)
Introduce `g _ N L`. Use `set U : Finset (Fin N × Fin N) := (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2) with hU`. Use `set R : Finset (Fin N × Fin N) := Finset.univ.filter (fun p => L.sharp = true ∧ L.s ≤ p.1 ∧ (p.1 : ℕ) < L.s + L.k ∧ (p.2 : ℕ) = L.s + L.k) with hR`. Establish `hUc : U.card = N * (N - 1) / 2`. Rewrite using `[hU, Finset.card_product_filter_lt, Nat.choose_two_right]`.

Simplify using the standard rewrite rules. Establish `hRU : R ⊆ U`. Introduce `p hp`. Simplify using `only [hR, hU, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢`. Rewrite using `[Fin.lt_def]`.

Use linear arithmetic over natural numbers and integers. Establish `hRc : R.card = if L.sharp = true then L.k else 0` using `by split_ifs with h`. Establish `hk` using `L.hk`. Use `symm`. Rewrite using `[← Finset.card_range L.k]`.

Use `Finset.card_bij (fun i hi => (⟨L.s + i, by have := Finset.mem_range.1 hi; omega⟩, ⟨L.s + L.k, hk⟩)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Use `Finset.mem_range.1 hi` as an intermediate fact. Simplify using `only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h]`. Conclude with `⟨by omega, by omega, trivial⟩`.

Introduce `i hi j hj hij`. Use `congrArg (fun p : Fin N × Fin N => (p.1 : ℕ)) hij` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Introduce `p hp`.

Simplify using `only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h] at hp`. Use `⟨p.1 - L.s, Finset.mem_range.2 (by omega), ?_⟩` and prove the remaining obligations. Apply the tactic sequence `apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega`. Simplify using `[hR, h]`. Establish `hM : ∀ u : GG g N, L.Mem u ↔ ((∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ U \ R → u.val a b = 0)`.

Introduce `u`. Simplify using `only [Lev.Mem, IsUp, hU, hR, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, not_and, not_not]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Use `⟨h1, fun a b hab h => ?_⟩` and prove the remaining obligations.

Break down `lt_or_gt_of_ne hab with h' | h'` into its components or cases. Assume the negation of the conclusion as `hne`. Conclude with `h h' (fun x1 x2 x3 x4 => hne (h3 x1 a b x2 x3 x4))`. Conclude with `h2 a b h'`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨⟨h1, fun a b h => h2 a b h.ne' (fun h' => absurd h' (lt_asymm h))⟩, fun x1 a b x2 x3 x4 => ?_⟩` and prove the remaining obligations. Use `h2 a b (fun h => ?_) (fun _ h => h x1 x2 x3 x4)` and prove the remaining obligations. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Rewrite using `[Nat.card_congr (Equiv.subtypeEquivRight hM), card_up_supp g N (U \ R) (fun p hp => by`.

Use `(Finset.mem_sdiff.1 hp).1` as an intermediate fact. Conclude with `(Finset.mem_filter.1 this).2), ← hRc, ← pow_add, Finset.card_sdiff_add_card_eq_card hRU, hUc]`.
-/
theorem lev_card : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N,
    Nat.card {u // L.Mem u} * g ^ (if L.sharp = true then L.k else 0) = g ^ (N * (N - 1) / 2) := by
  intro g _ N L
  set U : Finset (Fin N × Fin N) := (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2) with hU
  set R : Finset (Fin N × Fin N) := Finset.univ.filter
    (fun p => L.sharp = true ∧ L.s ≤ p.1 ∧ (p.1 : ℕ) < L.s + L.k ∧ (p.2 : ℕ) = L.s + L.k) with hR
  have hUc : U.card = N * (N - 1) / 2 := by
    rw [hU, Finset.card_product_filter_lt, Nat.choose_two_right]
    simp
  have hRU : R ⊆ U := by
    intro p hp
    simp only [hR, hU, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
    rw [Fin.lt_def]
    omega
  have hRc : R.card = if L.sharp = true then L.k else 0 := by
    split_ifs with h
    · have hk := L.hk
      symm
      rw [← Finset.card_range L.k]
      refine Finset.card_bij (fun i hi => (⟨L.s + i, by have := Finset.mem_range.1 hi; omega⟩, ⟨L.s + L.k, hk⟩)) ?_ ?_ ?_
      · intro i hi
        have := Finset.mem_range.1 hi
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h]
        exact ⟨by omega, by omega, trivial⟩
      · intro i hi j hj hij
        have := congrArg (fun p : Fin N × Fin N => (p.1 : ℕ)) hij
        simp only at this
        omega
      · intro p hp
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h] at hp
        refine ⟨p.1 - L.s, Finset.mem_range.2 (by omega), ?_⟩
        apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
    · simp [hR, h]
  have hM : ∀ u : GG g N, L.Mem u ↔
      ((∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ U \ R → u.val a b = 0) := by
    intro u
    simp only [Lev.Mem, IsUp, hU, hR, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, not_and, not_not]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun a b hab h => ?_⟩
      rcases lt_or_gt_of_ne hab with h' | h'
      · by_contra hne
        exact h h' (fun x1 x2 x3 x4 => hne (h3 x1 a b x2 x3 x4))
      · exact h2 a b h'
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun a b h => h2 a b h.ne' (fun h' => absurd h' (lt_asymm h))⟩, fun x1 a b x2 x3 x4 => ?_⟩
      refine h2 a b (fun h => ?_) (fun _ h => h x1 x2 x3 x4)
      subst h
      omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight hM), card_up_supp g N (U \ R) (fun p hp => by
    have := (Finset.mem_sdiff.1 hp).1
    exact (Finset.mem_filter.1 this).2), ← hRc, ← pow_add, Finset.card_sdiff_add_card_eq_card hRU, hUc]

end GlobalTheory.BadShare
