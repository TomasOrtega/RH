import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CasOnLowStatement

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Establish `h` using `Finset.card_filter_add_card_filter_not (s := univ.filter p) q`. Rewrite `h` using `[Finset.filter_filter, Finset.filter_filter]`. Conclude with `h` after adjusting the coercions.
-/
lemma vogDrop_cardSplit {n : ℕ} (p : Fin n → Prop) (q : Fin n → Prop) [DecidablePred p] [DecidablePred q] :
    ((univ.filter fun x => p x ∧ q x).card : ℝ) + ((univ.filter fun x => p x ∧ ¬ q x).card : ℝ)
      = ((univ.filter p).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not (s := univ.filter p) q
  rw [Finset.filter_filter, Finset.filter_filter] at h
  exact_mod_cast h

/- English proof (translation)
Establish `h1` using `vogDrop_cardSplit (fun b => a < b) (fun b => ε b = ε a)`. Establish `h2` using `vogDrop_cardSplit (fun b => b < a) (fun b => ε b = ε a)`. Establish `ha` using `a.isLt`. Establish `e1 : ((univ.filter fun b : Fin n => a < b).card : ℝ) = (n : ℝ) - 1 - (a : ℕ)`. Establish `hI : (univ.filter fun b : Fin n => a < b) = Finset.Ioi a` using `by ext; simp`.

Rewrite using `[hI, Fin.card_Ioi, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]`. Establish `e2 : ((univ.filter fun b : Fin n => b < a).card : ℝ) = (a : ℕ)`. Establish `hI : (univ.filter fun b : Fin n => b < a) = Finset.Iio a` using `by ext; simp`. Rewrite using `[hI, Fin.card_Iio]`. Simplify using `only [rhoC, rhoN, ne_eq] at *`.

Rewrite `h1` using `[e1]`. Rewrite `h2` using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma vogDrop_rhoSum {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    rhoC ε a + rhoN ε a = ((n : ℝ) - 1 - 2 * (a : ℕ)) / 2 := by
  have h1 := vogDrop_cardSplit (fun b => a < b) (fun b => ε b = ε a)
  have h2 := vogDrop_cardSplit (fun b => b < a) (fun b => ε b = ε a)
  have ha := a.isLt
  have e1 : ((univ.filter fun b : Fin n => a < b).card : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    have hI : (univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
    rw [hI, Fin.card_Ioi, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have e2 : ((univ.filter fun b : Fin n => b < a).card : ℝ) = (a : ℕ) := by
    have hI : (univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
    rw [hI, Fin.card_Iio]
  simp only [rhoC, rhoN, ne_eq] at *
  rw [e1] at h1
  rw [e2] at h2
  linarith

/- English proof (translation)
Introduce `ε lam hlam a b hab _`. Establish `hab' : a ≠ b` using `ne_of_lt hab`. Use `set w : Fin n → ℝ := fun i => lam i + rhoN ε i + rhoC ε i with hw`. Establish `key : vogSq ε (lowK ε lam - root a b) - vogSq ε (lowK ε lam) = 2 - 2 * (w a - w b)`. Simplify using `only [vogSq, nsq, dot, lowK, root]`.

Rewrite using `[← Finset.sum_sub_distrib, Fintype.sum_eq_add a b hab']`. Simplify using `[Pi.single_apply, hab', hab'.symm, w]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `x ⟨hxa, hxb⟩`. Simplify using `[Pi.single_apply, hxa, hxb]`.

Establish `hw_ab : w a - w b = (lam a - lam b) + (((b : ℕ) : ℝ) - (a : ℕ))`. Establish `ha` using `vogDrop_rhoSum ε a`. Establish `hb` using `vogDrop_rhoSum ε b`. Simplify using `only [w]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : lam b < lam a` using `hlam hab`. Establish `h2 : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ)`. Establish `: (a : ℕ) < b` using `Fin.lt_iff_val_lt_val.mp hab`. Conclude with `this` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vogDrop (n : ℕ) : VogDropStatement n := by
  intro ε lam hlam a b hab _
  have hab' : a ≠ b := ne_of_lt hab
  set w : Fin n → ℝ := fun i => lam i + rhoN ε i + rhoC ε i with hw
  have key : vogSq ε (lowK ε lam - root a b) - vogSq ε (lowK ε lam) = 2 - 2 * (w a - w b) := by
    simp only [vogSq, nsq, dot, lowK, root]
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add a b hab']
    · simp [Pi.single_apply, hab', hab'.symm, w]
      ring
    · rintro x ⟨hxa, hxb⟩
      simp [Pi.single_apply, hxa, hxb]
  have hw_ab : w a - w b = (lam a - lam b) + (((b : ℕ) : ℝ) - (a : ℕ)) := by
    have ha := vogDrop_rhoSum ε a
    have hb := vogDrop_rhoSum ε b
    simp only [w]
    linarith
  have h1 : lam b < lam a := hlam hab
  have h2 : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by
    have : (a : ℕ) < b := Fin.lt_iff_val_lt_val.mp hab
    exact_mod_cast this
  linarith

end ReciprocityTheory.ChartRestriction.DS.Lap
