import Formalism.RealPlaceAnalysis.StatementA

open Finset

noncomputable section

namespace Formalism.REAL

/- English proof (translation)
Establish `h : (univ.filter p).card ≤ n` using `(Finset.card_filter_le _ _).trans (by simp)`. Conclude with `h` after adjusting the coercions.
-/
lemma rho_card_le {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℝ) ≤ n := by
  have h : (univ.filter p).card ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast h

/- English proof (translation)
Unfold `rhoN`. Establish `h1` using `rho_card_le (fun b => a < b ∧ ε b ≠ ε a)`. Establish `h2` using `rho_card_le (fun b => b < a ∧ ε b ≠ ε a)`. Establish `h3` using `Nat.cast_nonneg (α := ℝ) (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card`. Establish `h4` using `Nat.cast_nonneg (α := ℝ) (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card`.

Apply the tactic sequence `constructor <;> linarith`.
-/
lemma rho_rhoN_bound {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoN ε a ∧ rhoN ε a ≤ (n : ℝ) / 2 := by
  unfold rhoN
  have h1 := rho_card_le (fun b => a < b ∧ ε b ≠ ε a)
  have h2 := rho_card_le (fun b => b < a ∧ ε b ≠ ε a)
  have h3 := Nat.cast_nonneg (α := ℝ) (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card
  have h4 := Nat.cast_nonneg (α := ℝ) (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card
  constructor <;> linarith

/- English proof (translation)
Introduce `n ε a`. Unfold `rhoC rhoN`. Establish `k1 : #{b | a < b ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a} = #{b | a < b}`. Simplify using `only [Finset.card_filter, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `b _`. Apply the tactic sequence `by_cases h1 : a < b <;> by_cases h2 : ε b = ε a <;> simp [h1, h2]`. Establish `k2 : #{b | b < a ∧ ε b = ε a} + #{b | b < a ∧ ε b ≠ ε a} = #{b | b < a}`. Simplify using `only [Finset.card_filter, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `b _`. Apply the tactic sequence `by_cases h1 : b < a <;> by_cases h2 : ε b = ε a <;> simp [h1, h2]`. Establish `k3 : #{b | a < b} = n - 1 - (a : ℕ)`. Rewrite using `[show (univ.filter fun b : Fin n => a < b) = Finset.Ioi a by ext b; simp]`. Conclude with `Fin.card_Ioi a`.

Establish `k4 : #{b | b < a} = (a : ℕ)`. Rewrite using `[show (univ.filter fun b : Fin n => b < a) = Finset.Iio a by ext b; simp]`. Conclude with `Fin.card_Iio a`. Establish `ha` using `a.isLt`. Establish `r1 : ((#{b | a < b ∧ ε b = ε a} : ℕ) : ℝ) + ((#{b | a < b ∧ ε b ≠ ε a} : ℕ) : ℝ) + ((a : ℕ) : ℝ) + 1 = (n : ℝ)`.

Conclude with `(show #{b | a < b ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a} + (a : ℕ) + 1 = n by omega)` after adjusting the coercions. Establish `r2 : ((#{b | b < a ∧ ε b = ε a} : ℕ) : ℝ) + ((#{b | b < a ∧ ε b ≠ ε a} : ℕ) : ℝ) = ((a : ℕ) : ℝ)`. Conclude with `(show #{b | b < a ∧ ε b = ε a} + #{b | b < a ∧ ε b ≠ ε a} = (a : ℕ) by omega)` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem half_sum_roots_standard : RhoStd := by
  intro n ε a
  unfold rhoC rhoN
  have k1 : #{b | a < b ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a} = #{b | a < b} := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h1 : a < b <;> by_cases h2 : ε b = ε a <;> simp [h1, h2]
  have k2 : #{b | b < a ∧ ε b = ε a} + #{b | b < a ∧ ε b ≠ ε a} = #{b | b < a} := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h1 : b < a <;> by_cases h2 : ε b = ε a <;> simp [h1, h2]
  have k3 : #{b | a < b} = n - 1 - (a : ℕ) := by
    rw [show (univ.filter fun b : Fin n => a < b) = Finset.Ioi a by ext b; simp]
    exact Fin.card_Ioi a
  have k4 : #{b | b < a} = (a : ℕ) := by
    rw [show (univ.filter fun b : Fin n => b < a) = Finset.Iio a by ext b; simp]
    exact Fin.card_Iio a
  have ha := a.isLt
  have r1 : ((#{b | a < b ∧ ε b = ε a} : ℕ) : ℝ) + ((#{b | a < b ∧ ε b ≠ ε a} : ℕ) : ℝ)
      + ((a : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast (show #{b | a < b ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a} + (a : ℕ) + 1 = n by omega)
  have r2 : ((#{b | b < a ∧ ε b = ε a} : ℕ) : ℝ) + ((#{b | b < a ∧ ε b ≠ ε a} : ℕ) : ℝ)
      = ((a : ℕ) : ℝ) := by
    exact_mod_cast (show #{b | b < a ∧ ε b = ε a} + #{b | b < a ∧ ε b ≠ ε a} = (a : ℕ) by omega)
  linarith

/- English proof (translation)
Establish `hs : ∀ i, (x + (Pi.single a 1 - Pi.single b 1) : Fin n → ℝ) i * (x + (Pi.single a 1 - Pi.single b 1) : Fin n → ℝ) i = x i * x i + (2 * x i + 1) * (Pi.single a (1 : ℝ) : Fin n → ℝ) i + (1 - 2 * x i) * (Pi.single b (1 : ℝ) : Fin n → ℝ) i`. Introduce `i`. Apply the tactic sequence `by_cases h1 : i = a <;> by_cases h2 : i = b`. Conclude with `absurd (h1.symm.trans h2) hab`. Apply the tactic sequence `all_goals simp [Pi.single_apply, h1, h2, hab, Ne.symm hab] <;> ring`.

Unfold `root nsq dot`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, Finset.sum_add_distrib]`. Apply the tactic sequence `simp [Pi.single_apply] <;> ring`.
-/
lemma rho_nsq_root {n : ℕ} (x : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) :
    nsq (x + root a b) = nsq x + 2 * (x a - x b) + 2 := by
  have hs : ∀ i, (x + (Pi.single a 1 - Pi.single b 1) : Fin n → ℝ) i *
        (x + (Pi.single a 1 - Pi.single b 1) : Fin n → ℝ) i
      = x i * x i + (2 * x i + 1) * (Pi.single a (1 : ℝ) : Fin n → ℝ) i +
        (1 - 2 * x i) * (Pi.single b (1 : ℝ) : Fin n → ℝ) i := by
    intro i
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h1.symm.trans h2) hab
    all_goals simp [Pi.single_apply, h1, h2, hab, Ne.symm hab] <;> ring
  unfold root nsq dot
  rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [Pi.single_apply] <;> ring

/- English proof (translation)
Introduce `n ε lam a b hab`. Establish `e : lam + rhoN ε - rhoC ε + root a b + rhoC ε = (lam + rhoN ε - rhoC ε + rhoC ε) + root a b`. Normalize the expressions using the abelian group laws. Rewrite using `[e, rho_nsq_root _ a b hab]`. Simplify using `only [Pi.add_apply, Pi.sub_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem omega_eigenvalue_holds : OmEigen := by
  intro n ε lam a b hab
  have e : lam + rhoN ε - rhoC ε + root a b + rhoC ε = (lam + rhoN ε - rhoC ε + rhoC ε) + root a b := by
    abel
  rw [e, rho_nsq_root _ a b hab]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/- English proof (translation)
Introduce `n ε lam g a b _ _ hg`. Take `⟨d1, _⟩` from `rho_rhoN_bound ε a`. Take `⟨_, d2⟩` from `rho_rhoN_bound ε b`. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem unitary_spectral_gap : UGap := by
  intro n ε lam g a b _ _ hg
  obtain ⟨d1, _⟩ := rho_rhoN_bound ε a
  obtain ⟨_, d2⟩ := rho_rhoN_bound ε b
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end Formalism.REAL
