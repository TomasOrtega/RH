import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcMult

open Polynomial in

noncomputable def linProd {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) : k[X] :=
  ∏ i, (1 - Polynomial.C (a i) * Polynomial.X)

open Polynomial in
/- English proof (translation)
Introduce `h`. Use `congrArg (Polynomial.eval 0) h` as an intermediate fact. Simplify using `[linProd, Polynomial.eval_prod] at this`.
-/
theorem linProd_ne_zero {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) :
    linProd a ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp [linProd, Polynomial.eval_prod] at this

open Polynomial in
/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Establish `: (0 : k) ≠ y` using `fun h => hy h.symm`. Simplify using `[this]`. Establish `e : (1 - Polynomial.C c * Polynomial.X) = Polynomial.C (-c) * (Polynomial.X - Polynomial.C c⁻¹)`.

Rewrite using `[mul_sub, ← Polynomial.C_mul]`. Simplify using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Polynomial.roots_C_mul _ (neg_ne_zero.mpr hc), Polynomial.roots_X_sub_C, Multiset.count_singleton]`. Distinguish the cases in `h : c = y`.

Simplify using `[h]`. Establish `: y⁻¹ ≠ c⁻¹` using `fun h' => h (inv_injective h').symm`. Simplify using `[h, this]`.
-/
theorem count_roots_factor {k : Type} [Field k] [DecidableEq k] (c y : k) (hy : y ≠ 0) :
    Multiset.count y⁻¹ (1 - Polynomial.C c * Polynomial.X).roots = if c = y then 1 else 0 := by
  by_cases hc : c = 0
  · subst hc
    have : (0 : k) ≠ y := fun h => hy h.symm
    simp [this]
  · have e : (1 - Polynomial.C c * Polynomial.X) = Polynomial.C (-c) * (Polynomial.X - Polynomial.C c⁻¹) := by
      rw [mul_sub, ← Polynomial.C_mul]
      simp [hc]
      ring
    rw [e, Polynomial.roots_C_mul _ (neg_ne_zero.mpr hc), Polynomial.roots_X_sub_C,
      Multiset.count_singleton]
    by_cases h : c = y
    · simp [h]
    · have : y⁻¹ ≠ c⁻¹ := fun h' => h (inv_injective h').symm
      simp [h, this]

open Polynomial in
/- English proof (translation)
Establish `h` using `linProd_ne_zero a`. Unfold `linProd at h ⊢`. Rewrite using `[Polynomial.roots_prod _ _ h, Multiset.count_bind]`. Simplify using `only [count_roots_factor _ _ hy]`. Rewrite using `[Finset.card_filter]`.

Both sides reduce to the same expression.
-/
theorem count_roots_linProd {k : Type} [Field k] [DecidableEq k] {ι : Type} [Fintype ι] (a : ι → k) (y : k)
    (hy : y ≠ 0) :
    Multiset.count y⁻¹ (linProd a).roots = (Finset.univ.filter fun i => a i = y).card := by
  classical
  have h := linProd_ne_zero a
  unfold linProd at h ⊢
  rw [Polynomial.roots_prod _ _ h, Multiset.count_bind]
  simp only [count_roots_factor _ _ hy]
  rw [Finset.card_filter]
  rfl

/- English proof (translation)
Rewrite using `[linProd, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]`. Simplify using the standard rewrite rules.
-/
theorem coe_linProd {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) :
    ((linProd a : Polynomial k) : PowerSeries k) = ∏ i, (1 - PowerSeries.C (a i) * PowerSeries.X) := by
  rw [linProd, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp

end GlobalTheory.AlcMult

namespace GlobalTheory.AlcMult

/- English proof (translation)
Use `set d : ZMod p → ℤ := fun x => (m x : ℤ) - m' x with hd`. Establish `step : ∀ y : ZMod p, y + 1 ≠ 0 → d (y + 1) = d y`. Introduce `y hy`. Use `h y hy` as an intermediate fact. Simplify using `only [hd]`.

Use linear arithmetic over natural numbers and integers. Establish `hp` using `(Fact.out : p.Prime)`. Establish `hn : ∀ n : ℕ, n < p → d (n : ZMod p) = d 0`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `hlt`. Establish `hne : ((n : ZMod p) + 1) ≠ 0`.

Introduce `h0`. Establish `: ((n + 1 : ℕ) : ZMod p) = 0` using `by push_cast; exact h0`. Rewrite `this` using `[ZMod.natCast_eq_zero_iff]`. Conclude with `absurd (Nat.le_of_dvd (Nat.succ_pos n) this) (by omega)`. Use `push_cast`.

Rewrite using `[step _ hne, ih (by omega)]`. Establish `hc : ∀ x, d x = d 0`. Introduce `x`. Use `hn x.val (ZMod.val_lt x)` as an intermediate fact. Rewrite `this` using `[ZMod.natCast_zmod_val]`. Then use the resulting hypothesis.

Establish `hsum : ∑ x, d x = 0`. Simplify using `only [hd, Finset.sum_sub_distrib]`. Establish `hs' : (∑ x, (m x : ℤ)) = ∑ x, (m' x : ℤ)` using `by exact_mod_cast hs`. Rewrite using `[hs', sub_self]`. Rewrite `hsum` using `[Finset.sum_congr rfl (fun x _ => hc x), Finset.sum_const, Finset.card_univ, ZMod.card]`.

Establish `h0 : d 0 = 0`. Break down `smul_eq_zero.mp hsum with h | h` into its components or cases. Conclude with `absurd h hp.ne_zero`. Conclude with `h`. Introduce `x`.

Use `hc x` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `only [hd] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem zmod_const_of_step (p : ℕ) [Fact p.Prime] (m m' : ZMod p → ℕ)
    (h : ∀ y : ZMod p, y + 1 ≠ 0 → m y + m' (y + 1) = m' y + m (y + 1))
    (hs : ∑ x, m x = ∑ x, m' x) : ∀ x, m x = m' x := by
  set d : ZMod p → ℤ := fun x => (m x : ℤ) - m' x with hd
  have step : ∀ y : ZMod p, y + 1 ≠ 0 → d (y + 1) = d y := by
    intro y hy
    have := h y hy
    simp only [hd]
    omega
  have hp := (Fact.out : p.Prime)
  have hn : ∀ n : ℕ, n < p → d (n : ZMod p) = d 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hlt
      have hne : ((n : ZMod p) + 1) ≠ 0 := by
        intro h0
        have : ((n + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact h0
        rw [ZMod.natCast_eq_zero_iff] at this
        exact absurd (Nat.le_of_dvd (Nat.succ_pos n) this) (by omega)
      push_cast
      rw [step _ hne, ih (by omega)]
  have hc : ∀ x, d x = d 0 := by
    intro x
    have := hn x.val (ZMod.val_lt x)
    rwa [ZMod.natCast_zmod_val] at this
  have hsum : ∑ x, d x = 0 := by
    simp only [hd, Finset.sum_sub_distrib]
    have hs' : (∑ x, (m x : ℤ)) = ∑ x, (m' x : ℤ) := by exact_mod_cast hs
    rw [hs', sub_self]
  rw [Finset.sum_congr rfl (fun x _ => hc x), Finset.sum_const, Finset.card_univ, ZMod.card] at hsum
  have h0 : d 0 = 0 := by
    rcases smul_eq_zero.mp hsum with h | h
    · exact absurd h hp.ne_zero
    · exact h
  intro x
  have := hc x
  rw [h0] at this
  simp only [hd] at this
  omega

end GlobalTheory.AlcMult

namespace GlobalTheory.AlcMult

/- English proof (translation)
Use `congr 1`. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[← map_natCast (ZMod.castHom (dvd_refl p) k) (l i)]`. Conclude with `(ZMod.castHom_injective k).eq_iff`.
-/
theorem card_cast_eq {p : ℕ} {k : Type} [Field k] [CharP k p] [DecidableEq k] {N : ℕ}
    (l : Fin N → ℕ) (z : ZMod p) :
    (Finset.univ.filter fun i => (l i : k) = ZMod.castHom (dvd_refl p) k z).card =
      (Finset.univ.filter fun i => (l i : ZMod p) = z).card := by
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← map_natCast (ZMod.castHom (dvd_refl p) k) (l i)]
  exact (ZMod.castHom_injective k).eq_iff

/- English proof (translation)
Use `congr 1`. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[← map_natCast (ZMod.castHom (dvd_refl p) k) (l i), ← map_one (ZMod.castHom (dvd_refl p) k), ← map_add, (ZMod.castHom_injective k).eq_iff, eq_sub_iff_add_eq]`.
-/
theorem card_cast_succ_eq {p : ℕ} {k : Type} [Field k] [CharP k p] [DecidableEq k] {N : ℕ}
    (l : Fin N → ℕ) (z : ZMod p) :
    (Finset.univ.filter fun i => (l i : k) + 1 = ZMod.castHom (dvd_refl p) k z).card =
      (Finset.univ.filter fun i => (l i : ZMod p) = z - 1).card := by
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← map_natCast (ZMod.castHom (dvd_refl p) k) (l i), ← map_one (ZMod.castHom (dvd_refl p) k),
    ← map_add, (ZMod.castHom_injective k).eq_iff, eq_sub_iff_add_eq]

/- English proof (translation)
Rewrite using `[← Finset.card_eq_sum_card_fiberwise (f := fun i => (l i : ZMod p)) (s := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]`. Simplify using the standard rewrite rules.
-/
theorem sum_card_fiber {p : ℕ} [NeZero p] {N : ℕ} (l : Fin N → ℕ) :
    ∑ x : ZMod p, (Finset.univ.filter fun i => (l i : ZMod p) = x).card = N := by
  classical
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun i => (l i : ZMod p)) (s := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  simp

end GlobalTheory.AlcMult

open GlobalTheory.AlcMult in
/- English proof (translation)
Introduce `p hp k _ _ N l l' H`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `letI : DecidableEq k := Classical.decEq k`. Establish `HP : linProd (fun i => (l i : k) + 1) * linProd (fun i => (l' i : k)) = linProd (fun i => (l' i : k) + 1) * linProd (fun i => (l i : k))`. Apply `Polynomial.coe_injective` to reduce the goal to its premises.

Rewrite using `[Polynomial.coe_mul, Polynomial.coe_mul, coe_linProd, coe_linProd, coe_linProd, coe_linProd]`. Conclude with `H`. Establish `hcount : ∀ y : k, y ≠ 0 → (Finset.univ.filter fun i => (l i : k) + 1 = y).card + (Finset.univ.filter fun i => (l' i : k) = y).card = (Finset.univ.filter fun i => (l' i : k) + 1 = y).card + (Finset.univ.filter fun i => (l i : k) = y).card`. Introduce `y hy`. Establish `e` using `congrArg (fun q => Multiset.count y⁻¹ q.roots) HP`.

Rewrite `e` using `[Polynomial.roots_mul (mul_ne_zero (linProd_ne_zero _) (linProd_ne_zero _)), Polynomial.roots_mul (mul_ne_zero (linProd_ne_zero _) (linProd_ne_zero _)), Multiset.count_add, Multiset.count_add, count_roots_linProd _ _ hy, count_roots_linProd _ _ hy, count_roots_linProd _ _ hy, cou …`. Conclude with `e`. Apply `zmod_const_of_step p` to reduce the goal to its premises. Introduce `y hy`. Establish `hne : ZMod.castHom (dvd_refl p) k (y + 1) ≠ 0`.

Rewrite using `[← map_zero (ZMod.castHom (dvd_refl p) k)]`. Conclude with `fun h => hy ((ZMod.castHom_injective k) h)`. Use `hcount _ hne` as an intermediate fact. Rewrite `this` using `[card_cast_succ_eq, card_cast_succ_eq, card_cast_eq, card_cast_eq, add_sub_cancel_right]`. Conclude with `this`.

Rewrite using `[sum_card_fiber, sum_card_fiber]`.
-/
theorem GlobalTheory.Alc.multiset_eq_of_series_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (l l' : Fin N → ℕ), (∏ i, (1 - PowerSeries.C ((l i : k) + 1) * PowerSeries.X)) * ∏ i, (1 - PowerSeries.C (l' i : k) * PowerSeries.X) = (∏ i, (1 - PowerSeries.C ((l' i : k) + 1) * PowerSeries.X)) * ∏ i, (1 - PowerSeries.C (l i : k) * PowerSeries.X) → ∀ x : ZMod p, (Finset.univ.filter fun i => (l i : ZMod p) = x).card = (Finset.univ.filter fun i => (l' i : ZMod p) = x).card := by
  intro p hp k _ _ N l l' H
  haveI : Fact p.Prime := ⟨hp⟩
  letI : DecidableEq k := Classical.decEq k
  have HP : linProd (fun i => (l i : k) + 1) * linProd (fun i => (l' i : k)) =
      linProd (fun i => (l' i : k) + 1) * linProd (fun i => (l i : k)) := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_mul, Polynomial.coe_mul, coe_linProd, coe_linProd, coe_linProd, coe_linProd]
    exact H
  have hcount : ∀ y : k, y ≠ 0 →
      (Finset.univ.filter fun i => (l i : k) + 1 = y).card +
        (Finset.univ.filter fun i => (l' i : k) = y).card =
      (Finset.univ.filter fun i => (l' i : k) + 1 = y).card +
        (Finset.univ.filter fun i => (l i : k) = y).card := by
    intro y hy
    have e := congrArg (fun q => Multiset.count y⁻¹ q.roots) HP
    rw [Polynomial.roots_mul (mul_ne_zero (linProd_ne_zero _) (linProd_ne_zero _)),
      Polynomial.roots_mul (mul_ne_zero (linProd_ne_zero _) (linProd_ne_zero _)),
      Multiset.count_add, Multiset.count_add, count_roots_linProd _ _ hy, count_roots_linProd _ _ hy,
      count_roots_linProd _ _ hy, count_roots_linProd _ _ hy] at e
    exact e
  apply zmod_const_of_step p
  · intro y hy
    have hne : ZMod.castHom (dvd_refl p) k (y + 1) ≠ 0 := by
      rw [← map_zero (ZMod.castHom (dvd_refl p) k)]
      exact fun h => hy ((ZMod.castHom_injective k) h)
    have := hcount _ hne
    rw [card_cast_succ_eq, card_cast_succ_eq, card_cast_eq, card_cast_eq, add_sub_cancel_right] at this
    exact this
  · rw [sum_card_fiber, sum_card_fiber]
