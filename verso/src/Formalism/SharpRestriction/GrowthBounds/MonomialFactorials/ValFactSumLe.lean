import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfNumericBound

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.GM Formalism.GM.M
open scoped Nat

section Arith

variable (p : ℕ) [hp : Fact p.Prime]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `@insert a s ha ih`. Rewrite `hL` using `[Finset.sum_insert ha]`. Establish `hL' : Nat.log p (∑ i ∈ s, f i) ≤ L` using `le_trans (Nat.log_mono_right (Nat.le_add_left _ _)) hL`.

Establish `ih'` using `ih hL'`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_eq_ite, if_neg ha]`. Generalize the expression as in `hT : ∑ i ∈ s, f i = T at *`. Establish `hC : (f a + T).choose (f a) * (f a)! * T ! = (f a + T)!`. Establish `h5` using `Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (f a) T)`.

Rewrite `h5` using `[Nat.add_sub_cancel_left]`. Then use the resulting hypothesis. Establish `hv : padicValNat p ((f a + T).choose (f a)) ≤ L`. Establish `h1` using `Nat.factorization_choose_le_log (p := p) (n := f a + T) (k := f a)`. Rewrite `h1` using `[Nat.factorization_def _ hp.out]`. Conclude with `h1.trans hL`.

Establish `hc0 : (f a + T).choose (f a) ≠ 0` using `(Nat.choose_pos (Nat.le_add_right _ _)).ne'`. Establish `hpr : (∏ i ∈ s, (f i)!) ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)`. Rewrite using `[← hC, padicValNat.mul (mul_ne_zero hc0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _), padicValNat.mul hc0 (Nat.factorial_ne_zero _), padicValNat.mul (Nat.factorial_ne_zero _) hpr]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem val_fact_sum_le {ι : Type} (s : Finset ι) (f : ι → ℕ) (L : ℕ) (hL : Nat.log p (∑ i ∈ s, f i) ≤ L) :
    padicValNat p (∑ i ∈ s, f i)! ≤ padicValNat p (∏ i ∈ s, (f i)!) + s.card * L := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha] at hL
    have hL' : Nat.log p (∑ i ∈ s, f i) ≤ L := le_trans (Nat.log_mono_right (Nat.le_add_left _ _)) hL
    have ih' := ih hL'
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_eq_ite, if_neg ha]
    generalize hT : ∑ i ∈ s, f i = T at *
    have hC : (f a + T).choose (f a) * (f a)! * T ! = (f a + T)! := by
      have h5 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (f a) T)
      rwa [Nat.add_sub_cancel_left] at h5
    have hv : padicValNat p ((f a + T).choose (f a)) ≤ L := by
      have h1 := Nat.factorization_choose_le_log (p := p) (n := f a + T) (k := f a)
      rw [Nat.factorization_def _ hp.out] at h1
      exact h1.trans hL
    have hc0 : (f a + T).choose (f a) ≠ 0 := (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    have hpr : (∏ i ∈ s, (f i)!) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)
    rw [← hC, padicValNat.mul (mul_ne_zero hc0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
      padicValNat.mul hc0 (Nat.factorial_ne_zero _), padicValNat.mul (Nat.factorial_ne_zero _) hpr]
    nlinarith

/- English proof (translation)
The claim follows from `(mul_dvd_mul hA hB).trans (Nat.factorial_mul_factorial_dvd_factorial_add x y)`.
-/
theorem fd {A B x y : ℕ} (hA : A ∣ x !) (hB : B ∣ y !) : A * B ∣ (x + y)! := (mul_dvd_mul hA hB).trans (Nat.factorial_mul_factorial_dvd_factorial_add x y)

end Arith

section Block

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def letOf : M.BVar N r G.T.t → Fin (N + 1)
  | Sum.inl (a', _) => a'
  | Sum.inr (i, false) => zLet G i
  | Sum.inr (i, true) => sLet G i

/- English proof (translation)
Apply the tactic sequence `rcases v with ⟨a', c⟩ | ⟨i, _ | _⟩ <;> rfl`.
-/
theorem wL_eq (a : Fin (N + 1)) (v : M.BVar N r G.T.t) : wL (r := r) G a v = if letOf G v = a then 1 else 0 := by
  rcases v with ⟨a', c⟩ | ⟨i, _ | _⟩ <;> rfl

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun v _ => ?_)` and prove the remaining obligations. Rewrite using `[wL_eq]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem weight_eq (a : Fin (N + 1)) (μ : M.BVar N r G.T.t →₀ ℕ) :
    Finsupp.weight (wL (r := r) G a) μ = ∑ v ∈ Finset.univ.filter (fun v => letOf G v = a), μ v := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [wL_eq]
  split_ifs <;> simp

/- English proof (translation)
Establish `hprod : ∀ {α : Type} (s : Finset α) (g : α → ℕ), (∀ i ∈ s, g i ≠ 0) → padicValNat p (∏ i ∈ s, g i) = ∑ i ∈ s, padicValNat p (g i)`. Introduce `α s g hg`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `@insert a s ha ih`.

Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul (hg a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.mpr (fun i hi => hg i (Finset.mem_insert_of_mem hi))), ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]`. Establish `hμ : (μ.prod fun _ k => k !) = ∏ v, (μ v)!` using `Finsupp.prod_fintype _ _ (fun _ => rfl)`. Rewrite using `[hμ, hprod _ _ (fun _ _ => Nat.factorial_ne_zero _), hprod _ _ (fun _ _ => Nat.factorial_ne_zero _)]`. Establish `hfib : ∀ a, padicValNat p (d a)! ≤ ∑ v ∈ Finset.univ.filter (fun v => letOf (r` using `r) G v = a), padicValNat p (μ v)! + (Finset.univ.filter (fun v => letOf (r := r) G v = a)).card * L := by`. Introduce `a`.

Establish `hd : d a = ∑ v ∈ Finset.univ.filter (fun v => letOf (r` using `r) G v = a), μ v := by rw [← hw a, weight_eq]`. Establish `h6` using `val_fact_sum_le p (Finset.univ.filter (fun v => letOf (r := r) G v = a)) μ L (by rw [← hd]; exact hL a)`. Rewrite `h6` using `[hprod _ _ (fun _ _ => Nat.factorial_ne_zero _)]`. Rewrite using `[hd]`. Conclude with `h6`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, Finset.sum_fiberwise, ← Finset.sum_mul, Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (letOf (r := r) G v))]`. Use `_ = _ := by`. Simplify using `only [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]`.
-/
theorem val_letters_le (μ : M.BVar N r G.T.t →₀ ℕ) (d : Fin (N + 1) → ℕ)
    (hw : ∀ a, Finsupp.weight (wL (r := r) G a) μ = d a) (L : ℕ) (hL : ∀ a, Nat.log p (d a) ≤ L) :
    padicValNat p (∏ a, (d a)!) ≤ padicValNat p (μ.prod fun _ k => k !) + ((N + 1) * r + (G.T.t + 1) * 2) * L := by
  classical
  have hprod : ∀ {α : Type} (s : Finset α) (g : α → ℕ), (∀ i ∈ s, g i ≠ 0) →
      padicValNat p (∏ i ∈ s, g i) = ∑ i ∈ s, padicValNat p (g i) := by
    intro α s g hg
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hg i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]
  have hμ : (μ.prod fun _ k => k !) = ∏ v, (μ v)! := Finsupp.prod_fintype _ _ (fun _ => rfl)
  rw [hμ, hprod _ _ (fun _ _ => Nat.factorial_ne_zero _), hprod _ _ (fun _ _ => Nat.factorial_ne_zero _)]
  have hfib : ∀ a, padicValNat p (d a)! ≤ ∑ v ∈ Finset.univ.filter (fun v => letOf (r := r) G v = a), padicValNat p (μ v)! +
      (Finset.univ.filter (fun v => letOf (r := r) G v = a)).card * L := by
    intro a
    have hd : d a = ∑ v ∈ Finset.univ.filter (fun v => letOf (r := r) G v = a), μ v := by rw [← hw a, weight_eq]
    have h6 := val_fact_sum_le p (Finset.univ.filter (fun v => letOf (r := r) G v = a)) μ L (by rw [← hd]; exact hL a)
    rw [hprod _ _ (fun _ _ => Nat.factorial_ne_zero _)] at h6
    rw [hd]
    exact h6
  calc ∑ a, padicValNat p (d a)!
      ≤ ∑ a, (∑ v ∈ Finset.univ.filter (fun v => letOf (r := r) G v = a), padicValNat p (μ v)! +
          (Finset.univ.filter (fun v => letOf (r := r) G v = a)).card * L) := Finset.sum_le_sum (fun a _ => hfib a)
    _ = ∑ v, padicValNat p (μ v)! + (Finset.univ : Finset (M.BVar N r G.T.t)).card * L := by
        rw [Finset.sum_add_distrib, Finset.sum_fiberwise, ← Finset.sum_mul,
          Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (letOf (r := r) G v))]
    _ = _ := by
        simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
