import Mathlib
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist

namespace GlobalTheory

open Formalism.L2.G.Pend in
/- English proof (translation)
Establish `hc : wToC p z = wToC p 0`. Rewrite using `[map_zero]`. Apply `eq_of_close` to reduce the goal to its premises. Introduce `N`. Take `⟨b, hb⟩` from `h N`.

Rewrite using `[sub_zero, hb]`. Conclude with `norm_wToC_pow_mul p N b`. Conclude with `wToC_injective p hc`.
-/
theorem wittKbar_eq_zero_of_forall_dvd (p : ℕ) [Fact p.Prime] (z : WW p)
    (h : ∀ N : ℕ, (p : WW p) ^ N ∣ z) : z = 0 := by
  have hc : wToC p z = wToC p 0 := by
    rw [map_zero]
    apply eq_of_close
    intro N
    obtain ⟨b, hb⟩ := h N
    rw [sub_zero, hb]
    exact norm_wToC_pow_mul p N b
  exact wToC_injective p hc

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `e : x ^ (p ^ (n * (j + 1))) = (x ^ (p ^ (n * j))) ^ (p ^ n)`.

Rewrite using `[← pow_mul, ← pow_add, mul_add, mul_one]`. Rewrite using `[e]`. Use `dvd_add (h (x ^ (p ^ (n * j)))) ih` as an intermediate fact. Simplify `this` using `[sub_add_sub_cancel]`.
-/
theorem dvd_pow_pow_sub_self_of_dvd {W : Type} [CommRing W] (p n : ℕ)
    (h : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (x : W) :
    ∀ j : ℕ, (p : W) ∣ x ^ (p ^ (n * j)) - x := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : x ^ (p ^ (n * (j + 1))) = (x ^ (p ^ (n * j))) ^ (p ^ n) := by
      rw [← pow_mul, ← pow_add, mul_add, mul_one]
    rw [e]
    have := dvd_add (h (x ^ (p ^ (n * j)))) ih
    simpa [sub_add_sub_cancel] using this

/- English proof (translation)
Establish `key : ∀ k : ℕ, ∀ x : W, (p : Formalism.L2.G.Pend.WW p) ^ k ∣ f x - g x`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `x`. Take `⟨y, hy⟩` from `dvd_pow_pow_sub_self_of_dvd p n h x k`. Establish `hx : x = x ^ (p ^ (n * k)) - (p : W) * y` using `by rw [← hy]; ring`. Establish `h1 : (p : Formalism.L2.G.Pend.WW p) ^ (n * k + 1) ∣ (f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k))` using `dvd_sub_pow_of_dvd_sub (hfg x) (n * k)`.

Establish `hk : k + 1 ≤ n * k + 1`. Establish `: k ≤ n * k` using `Nat.le_mul_of_pos_left k hn`. Use linear arithmetic over natural numbers and integers. Establish `h1'` using `(pow_dvd_pow (p : Formalism.L2.G.Pend.WW p) hk).trans h1`. Establish `h2 : (p : Formalism.L2.G.Pend.WW p) ^ (k + 1) ∣ (p : Formalism.L2.G.Pend.WW p) * (f y - g y)`.

Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul_left _ (ih y)`. Establish `e : f x - g x = ((f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k))) - (p : Formalism.L2.G.Pend.WW p) * (f y - g y)` using `by conv_lhs => rw [hx]`. Simplify using `only [map_sub, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `dvd_sub h1' h2`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Use `wittKbar_eq_zero_of_forall_dvd p (f x - g x) (fun N => key N x)` as an intermediate fact. Conclude with `sub_eq_zero.mp this`.
-/
theorem ringHom_wittKbar_eq_of_modp (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W] (hn : 0 < n)
    (h : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (f g : W →+* Formalism.L2.G.Pend.WW p)
    (hfg : ∀ x, (p : Formalism.L2.G.Pend.WW p) ∣ f x - g x) : f = g := by
  have key : ∀ k : ℕ, ∀ x : W, (p : Formalism.L2.G.Pend.WW p) ^ k ∣ f x - g x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      obtain ⟨y, hy⟩ := dvd_pow_pow_sub_self_of_dvd p n h x k
      have hx : x = x ^ (p ^ (n * k)) - (p : W) * y := by rw [← hy]; ring
      have h1 : (p : Formalism.L2.G.Pend.WW p) ^ (n * k + 1) ∣ (f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k)) :=
        dvd_sub_pow_of_dvd_sub (hfg x) (n * k)
      have hk : k + 1 ≤ n * k + 1 := by
        have : k ≤ n * k := Nat.le_mul_of_pos_left k hn
        omega
      have h1' := (pow_dvd_pow (p : Formalism.L2.G.Pend.WW p) hk).trans h1
      have h2 : (p : Formalism.L2.G.Pend.WW p) ^ (k + 1) ∣ (p : Formalism.L2.G.Pend.WW p) * (f y - g y) := by
        rw [pow_succ']
        exact mul_dvd_mul_left _ (ih y)
      have e : f x - g x = ((f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k))) - (p : Formalism.L2.G.Pend.WW p) * (f y - g y) := by
        conv_lhs => rw [hx]
        simp only [map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [e]
      exact dvd_sub h1' h2
  refine RingHom.ext fun x => ?_
  have := wittKbar_eq_zero_of_forall_dvd p (f x - g x) (fun N => key N x)
  exact sub_eq_zero.mp this

end GlobalTheory
