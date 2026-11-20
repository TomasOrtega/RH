import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

/- English proof (translation)
Establish `h1` using `hc (a + b) c e`. Establish `h2` using `hc a b c`. Establish `h3` using `hc (a + c) b e`. Establish `h4` using `hc a c b`. Rewrite `h3` using `[add_right_comm a c b]`.

Rewrite `h4` using `[add_comm c b, hs c b]`. Rewrite using `[← sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem symmCocycle_swap {A B : Type} [AddCommGroup A] [AddCommGroup B] (γ : A → A → B)
    (hs : ∀ x y, γ x y = γ y x) (hc : ∀ x y z, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0)
    (a b c e : A) :
    γ (a + b) (c + e) + γ a b + γ c e = γ (a + c) (b + e) + γ a c + γ b e := by
  have h1 := hc (a + b) c e
  have h2 := hc a b c
  have h3 := hc (a + c) b e
  have h4 := hc a c b
  rw [add_right_comm a c b] at h3
  rw [add_comm c b, hs c b] at h4
  rw [← sub_eq_zero]
  calc _ = ((γ c e - γ (a + b + c) e + γ (a + b) (c + e) - γ (a + b) c)
        - (γ b c - γ (a + b) c + γ a (b + c) - γ a b))
        - ((γ b e - γ (a + b + c) e + γ (a + c) (b + e) - γ (a + c) b)
        - (γ b c - γ (a + c) b + γ a (b + c) - γ a c)) := by abel
    _ = 0 := by rw [h1, h2, h3, h4]; simp

/- English proof (translation)
Introduce `A B _ _ γ hs hc h0 d`. Proceed by induction on `d with`. Consider the case `zero => intro x y`. Simplify using `[h0]`. Consider the case `succ d ih`.

Introduce `x y`. Establish `ih'` using `ih (fun j => x (Fin.castSucc j)) (fun j => y (Fin.castSucc j))`. Simplify using `only [Finset.sum_filter] at ih' ⊢`. Simplify using `only [Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, if_true, lt_irrefl, if_false, add_zero] at ih' ⊢`. Establish `hl : ∀ i : Fin d, ¬ (Fin.last d < i.castSucc)` using `fun i => not_lt.mpr (Fin.castSucc_lt_last i).le`.

Simplify using `only [hl, if_false, add_zero] at ih' ⊢`. Establish `k` using `symmCocycle_swap γ hs hc (∑ m : Fin d, x m.castSucc) (x (Fin.last d)) (∑ m : Fin d, y m.castSucc) (y (Fin.last d))`. Rewrite `k` using `[ih']`. Rewrite using `[Finset.sum_add_distrib]`. Rewrite `k`, the goal using `[← sub_eq_zero]`.

Rewrite using `[← k]`. Normalize the expressions using the abelian group laws.
-/
theorem symmCocycle_sum : ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] (γ : A → A → B), (∀ x y, γ x y = γ y x) → (∀ x y z, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0) → γ 0 0 = 0 → ∀ (d : ℕ) (x y : Fin d → A), γ (∑ m, x m) (∑ m, y m) = ∑ m, γ (x m) (y m) + ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) - (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) - ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) := by
  intro A B _ _ γ hs hc h0 d
  induction d with
  | zero => intro x y; simp [h0]
  | succ d ih =>
    intro x y
    have ih' := ih (fun j => x (Fin.castSucc j)) (fun j => y (Fin.castSucc j))
    simp only [Finset.sum_filter] at ih' ⊢
    simp only [Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last,
      if_true, lt_irrefl, if_false, add_zero] at ih' ⊢
    have hl : ∀ i : Fin d, ¬ (Fin.last d < i.castSucc) := fun i => not_lt.mpr (Fin.castSucc_lt_last i).le
    simp only [hl, if_false, add_zero] at ih' ⊢
    have k := symmCocycle_swap γ hs hc (∑ m : Fin d, x m.castSucc) (x (Fin.last d)) (∑ m : Fin d, y m.castSucc) (y (Fin.last d))
    rw [ih'] at k
    rw [Finset.sum_add_distrib]
    rw [← sub_eq_zero] at k ⊢
    rw [← k]
    abel

end GlobalTheory
