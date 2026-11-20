import Mathlib
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist

namespace GlobalTheory

open Formalism.L2.G.Pend in
/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
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
