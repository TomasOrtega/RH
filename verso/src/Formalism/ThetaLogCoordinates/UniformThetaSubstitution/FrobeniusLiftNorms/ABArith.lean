import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementAB
import Formalism.GrowthSums.FactorialBaseGrowth.PathBasisOfCount
import Formalism.GrowthSums.FactorialBaseGrowth.QuadraticExponentIdentity

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.GrowthSums (gamP rhoP gainG excessGain)

/- English proof (translation)
Unfold `lgN`. Use `split_ifs with h1 h2`. Conclude with `le_rfl`. Conclude with `Nat.zero_le _`. Use linear arithmetic over natural numbers and integers.

Conclude with `Nat.succ_le_succ (Nat.log_mono_right h)`.
-/
theorem lgN_mono (p : ℕ) {x y : ℕ} (h : x ≤ y) : lgN p x ≤ lgN p y := by
  unfold lgN
  split_ifs with h1 h2
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · exact Nat.succ_le_succ (Nat.log_mono_right h)

/- English proof (translation)
Establish `hlen : (Nat.digits p m).length = lgN p m`. Unfold `lgN`. Use `split_ifs with h`. Simplify using `[h]`. Conclude with `Nat.length_digits p m hp h`.

Establish `h` using `List.sum_le_card_nsmul (Nat.digits p m) (p - 1) (fun d hd => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp hd))`. Rewrite `h` using `[hlen, smul_eq_mul, mul_comm]`. Conclude with `h`.
-/
theorem digits_sum_le_lgN (p m : ℕ) (hp : 1 < p) :
    (Nat.digits p m).sum ≤ (p - 1) * lgN p m := by
  have hlen : (Nat.digits p m).length = lgN p m := by
    unfold lgN
    split_ifs with h
    · simp [h]
    · exact Nat.length_digits p m hp h
  have h := List.sum_le_card_nsmul (Nat.digits p m) (p - 1)
    (fun d hd => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp hd))
  rw [hlen, smul_eq_mul, mul_comm] at h
  exact h

/- English proof (translation)
Introduce `p m hp`. Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `h1` using `sub_one_mul_padicValNat_factorial (p := p) m`. Establish `h2` using `Nat.digit_sum_le p m`. Establish `h3` using `digits_sum_le_lgN p m hp.one_lt`.

Establish `h4 : m ≤ (p - 1) * (padicValNat p m.factorial + lgN p m)`. Rewrite using `[mul_add, h1]`. Use linear arithmetic over natural numbers and integers. Establish `hp1 : (0 : ℝ) < (p : ℝ) - 1`. Establish `: (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : (m : ℝ) ≤ ((p : ℝ) - 1) * ((padicValNat p m.factorial : ℝ) + lgN p m)`. Establish `h6 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1`. Rewrite using `[Nat.cast_sub hp.one_lt.le, Nat.cast_one]`. Rewrite using `[← h6]`.

Conclude with `h4` after adjusting the coercions. Rewrite using `[sub_le_iff_le_add, div_le_iff₀ hp1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem factorialValuationLowerBound : FactorialLg := by
  intro p m hp
  have : Fact p.Prime := ⟨hp⟩
  have h1 := sub_one_mul_padicValNat_factorial (p := p) m
  have h2 := Nat.digit_sum_le p m
  have h3 := digits_sum_le_lgN p m hp.one_lt
  have h4 : m ≤ (p - 1) * (padicValNat p m.factorial + lgN p m) := by
    rw [mul_add, h1]
    omega
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have h5 : (m : ℝ) ≤ ((p : ℝ) - 1) * ((padicValNat p m.factorial : ℝ) + lgN p m) := by
    have h6 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    rw [← h6]
    exact_mod_cast h4
  rw [sub_le_iff_le_add, div_le_iff₀ hp1]
  linarith

/- English proof (translation)
Establish `hle : ∀ e', f e' ≤ A` using `fun e' => le_trans (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)) (h e')`. Establish `hsupp : ∀ e' ∈ E, lgN p (f e') ≠ 0 → e' < lgN p A`. Introduce `e' _ hne`. Establish `hf : f e' ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Simplify using `[lgN, h0]`. Establish `h1 : p ^ (2 * e' + 1) ≤ A` using `le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hf)) (h e')`. Establish `hA : A ≠ 0`. Establish `: 0 < p ^ (2 * e' + 1)` using `pow_pos (by omega) _`.

Use linear arithmetic over natural numbers and integers. Establish `h2` using `Nat.le_log_of_pow_le hp h1`. Simplify using `only [lgN, hA, if_false]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.sum_filter_of_ne hsupp]`.

Combine the equalities or inequalities in the displayed calculation. Apply `Nat.mul_le_mul_right` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mem_filter, mem_range] at hx ⊢`. Conclude with `hx.2)`.

Use `_ = lgN p A := card_range _`. Use `_ = lgN p A ^ 2 := (sq _).symm`.
-/
theorem sum_lgN_le (p : ℕ) (hp : 1 < p) (A : ℕ) (f : ℕ → ℕ) (E : Finset ℕ)
    (h : ∀ e', p ^ (2 * e' + 1) * f e' ≤ A) :
    ∑ e' ∈ E, lgN p (f e') ≤ lgN p A ^ 2 := by
  have hle : ∀ e', f e' ≤ A := fun e' =>
    le_trans (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)) (h e')
  have hsupp : ∀ e' ∈ E, lgN p (f e') ≠ 0 → e' < lgN p A := by
    intro e' _ hne
    have hf : f e' ≠ 0 := by
      intro h0
      apply hne
      simp [lgN, h0]
    have h1 : p ^ (2 * e' + 1) ≤ A :=
      le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hf)) (h e')
    have hA : A ≠ 0 := by
      have : 0 < p ^ (2 * e' + 1) := pow_pos (by omega) _
      omega
    have h2 := Nat.le_log_of_pow_le hp h1
    simp only [lgN, hA, if_false]
    omega
  rw [← Finset.sum_filter_of_ne hsupp]
  calc ∑ e' ∈ E.filter (fun e' => e' < lgN p A), lgN p (f e')
      ≤ ∑ _e' ∈ E.filter (fun e' => e' < lgN p A), lgN p A :=
        Finset.sum_le_sum (fun e' _ => lgN_mono p (hle e'))
    _ = (E.filter (fun e' => e' < lgN p A)).card * lgN p A := by rw [sum_const, smul_eq_mul]
    _ ≤ lgN p A * lgN p A := by
        apply Nat.mul_le_mul_right
        calc (E.filter (fun e' => e' < lgN p A)).card ≤ (range (lgN p A)).card :=
              card_le_card (fun x hx => by
                simp only [mem_filter, mem_range] at hx ⊢
                exact hx.2)
          _ = lgN p A := card_range _
    _ = lgN p A ^ 2 := (sq _).symm

/- English proof (translation)
Establish `h1 : ∑ x ∈ T, ((f x : ℝ) / ((p : ℝ) - 1) - lgN p B) ≤ ∑ x ∈ T, (padicValNat p (f x).factorial : ℝ)`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `x hx`. Establish `h` using `factorialValuationLowerBound p (f x) hp`. Establish `h' : (lgN p (f x) : ℝ) ≤ lgN p B` using `by exact_mod_cast lgN_mono p (hB x hx)`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h1` using `[Finset.sum_sub_distrib, ← Finset.sum_div, sum_const, nsmul_eq_mul]`. Rewrite using `[Nat.cast_sum]`. Conclude with `h1`.
-/
theorem sum_factorial_ge {ι : Type} (p : ℕ) (hp : p.Prime) (T : Finset ι) (f : ι → ℕ) (B : ℕ)
    (hB : ∀ x ∈ T, f x ≤ B) :
    ((∑ x ∈ T, f x : ℕ) : ℝ) / ((p : ℝ) - 1) - (T.card : ℝ) * lgN p B ≤
      ∑ x ∈ T, (padicValNat p (f x).factorial : ℝ) := by
  have h1 : ∑ x ∈ T, ((f x : ℝ) / ((p : ℝ) - 1) - lgN p B) ≤
      ∑ x ∈ T, (padicValNat p (f x).factorial : ℝ) := by
    apply Finset.sum_le_sum
    intro x hx
    have h := factorialValuationLowerBound p (f x) hp
    have h' : (lgN p (f x) : ℝ) ≤ lgN p B := by exact_mod_cast lgN_mono p (hB x hx)
    linarith
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_const, nsmul_eq_mul] at h1
  rw [Nat.cast_sum]
  exact h1

/- English proof (translation)
Introduce `S _ p r0 r1 TT al ls e a i E i0 i2 hp halT he ha hiE hiT hpi htot hi2`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Take `⟨-, hgam⟩` from `Formalism.GrowthSums.oddPowerInvSumIdentity (p : ℝ) hp1`. Use `set c : ℝ := 1 / ((p : ℝ) - 1) with hc`.

Establish `H1 : ∀ s, (al s : ℝ) * c - (r1 : ℝ) * lgN p (al s) ≤ ∑ b, (padicValNat p (e s b).factorial : ℝ)`. Introduce `s`. Establish `h` using `sum_factorial_ge p hp univ (e s) (al s) (fun x _ => by rw [← he s]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x))`. Rewrite `h` using `[he s, card_univ, Fintype.card_fin]`. Rewrite using `[hc, mul_one_div]`.

Conclude with `h`. Establish `H3 : ∀ s, ((∑ x, a s x : ℕ) : ℝ) * c - (r0 : ℝ) * r1 * lgN p (ls s) ≤ ∑ x, (padicValNat p (a s x).factorial : ℝ)`. Introduce `s`. Establish `h` using `sum_factorial_ge p hp univ (a s) (ls s) (fun x _ => le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x)) (ha s))`. Rewrite `h` using `[card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]`.

Rewrite using `[hc, mul_one_div]`. Conclude with `h`. Establish `H2 : ∀ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) * c - ((lgN p (al s) : ℝ)) ^ 2 ≤ ∑ e' ∈ E, (padicValNat p (i s e').factorial : ℝ)`. Introduce `s`. Establish `h1 : ∑ e' ∈ E, ((i s e' : ℝ) / ((p : ℝ) - 1) - lgN p (i s e')) ≤ ∑ e' ∈ E, (padicValNat p (i s e').factorial : ℝ)` using `Finset.sum_le_sum (fun e' _ => factorialValuationLowerBound p (i s e') hp)`.

Establish `h2 : ((∑ e' ∈ E, lgN p (i s e') : ℕ) : ℝ) ≤ ((lgN p (al s) : ℝ)) ^ 2`. Conclude with `sum_lgN_le p hp.one_lt (al s) (i s) E (hpi s)` after adjusting the coercions. Rewrite `h1` using `[Finset.sum_sub_distrib, ← Finset.sum_div]`. Rewrite `h2` using `[Nat.cast_sum]`. Rewrite using `[hc, mul_one_div, Nat.cast_sum]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlg0 : ∀ s, s ∉ TT → ((lgN p (al s) : ℝ)) ^ 2 = 0`. Introduce `s hs`. Simplify using `[lgN, halT s hs]`. Establish `hTT_lg : ∑ s ∈ TT, ((lgN p (al s) : ℝ)) ^ 2 = ∑ s, ((lgN p (al s) : ℝ)) ^ 2` using `Finset.sum_subset (subset_univ _) (fun s _ hs => hlg0 s hs)`.

Establish `hTT_al : ∑ s ∈ TT, (al s : ℝ) = ∑ s, (al s : ℝ)` using `Finset.sum_subset (subset_univ _) (fun s _ hs => by rw [halT s hs, Nat.cast_zero])`. Establish `hTT_i : ∑ s ∈ TT, ∑ e' ∈ E, (i s e' : ℝ) = ∑ s, ∑ e' ∈ E, (i s e' : ℝ)` using `Finset.sum_subset (subset_univ _) (fun s _ hs => by simp [hiT s hs])`. Establish `S1` using `Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H1 s)`. Establish `S2` using `Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H2 s)`. Establish `S3` using `Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H3 s)`.

Rewrite `S1`, `S2`, `S3` using `[Finset.sum_sub_distrib, ← Finset.sum_mul]`. Establish `htotR : (∑ s, ((∑ x, a s x : ℕ) : ℝ)) + ∑ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) = ∑ s, (ls s : ℝ)`. Conclude with `htot` after adjusting the coercions. Establish `hiR : ∑ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) = ∑ s, ∑ e' ∈ E, (i s e' : ℝ)`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hi2R : (p : ℝ) * i2 ≤ ∑ s, (ls s : ℝ)` using `by exact_mod_cast hi2`. Establish `hL0 : (0 : ℝ) ≤ ∑ s, (ls s : ℝ)` using `Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)`. Establish `hgp : 1 / (p : ℝ) ≤ gamP p`. Unfold `gamP rhoP`.

Establish `hpp : (0 : ℝ) < (p : ℝ) ^ 2 - 1` using `by nlinarith`. Rewrite using `[mul_one_div, div_le_div_iff₀ hp0 hpp]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hi2g : (i2 : ℝ) ≤ gamP p * ∑ s, (ls s : ℝ)`. Establish `h1 : (i2 : ℝ) ≤ 1 / (p : ℝ) * ∑ s, (ls s : ℝ)`.

Rewrite using `[one_div, inv_mul_eq_div, le_div_iff₀ hp0]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h1.trans (mul_le_mul_of_nonneg_right hgp hL0)`. Establish `hcg : c = gamP p + rhoP p` using `by rw [hgam]; ring`. Unfold `deLoss`.

Rewrite using `[hTT_lg, hTT_al, hTT_i, Finset.sum_add_distrib, Finset.sum_add_distrib]`. Rewrite `S1`, `S2`, `S3` using `[hcg]`. Rewrite `S2`, `htotR` using `[hiR]`. Use `set A : ℝ := ∑ s, (al s : ℝ)`. Use `set L : ℝ := ∑ s, (ls s : ℝ)`.

Use `set I : ℝ := ∑ s, ∑ e' ∈ E, (i s e' : ℝ)`. Use `set Aa : ℝ := ∑ s, ((∑ x, a s x : ℕ) : ℝ)`. Establish `hAa : Aa = L - I` using `by linarith`. Rewrite `S3` using `[hAa]`. Use polynomial arithmetic with `[S1, S2, S3, hi2g]`.
-/
theorem gainFactorialInequality : StarArith := by
  intro S _ p r0 r1 TT al ls e a i E i0 i2 hp halT he ha hiE hiT hpi htot hi2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨-, hgam⟩ := Formalism.GrowthSums.oddPowerInvSumIdentity (p : ℝ) hp1
  set c : ℝ := 1 / ((p : ℝ) - 1) with hc

  have H1 : ∀ s, (al s : ℝ) * c - (r1 : ℝ) * lgN p (al s) ≤
      ∑ b, (padicValNat p (e s b).factorial : ℝ) := by
    intro s
    have h := sum_factorial_ge p hp univ (e s) (al s)
      (fun x _ => by rw [← he s]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x))
    rw [he s, card_univ, Fintype.card_fin] at h
    rw [hc, mul_one_div]
    exact h

  have H3 : ∀ s, ((∑ x, a s x : ℕ) : ℝ) * c - (r0 : ℝ) * r1 * lgN p (ls s) ≤
      ∑ x, (padicValNat p (a s x).factorial : ℝ) := by
    intro s
    have h := sum_factorial_ge p hp univ (a s) (ls s)
      (fun x _ => le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x)) (ha s))
    rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul] at h
    rw [hc, mul_one_div]
    exact h

  have H2 : ∀ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) * c - ((lgN p (al s) : ℝ)) ^ 2 ≤
      ∑ e' ∈ E, (padicValNat p (i s e').factorial : ℝ) := by
    intro s
    have h1 : ∑ e' ∈ E, ((i s e' : ℝ) / ((p : ℝ) - 1) - lgN p (i s e')) ≤
        ∑ e' ∈ E, (padicValNat p (i s e').factorial : ℝ) :=
      Finset.sum_le_sum (fun e' _ => factorialValuationLowerBound p (i s e') hp)
    have h2 : ((∑ e' ∈ E, lgN p (i s e') : ℕ) : ℝ) ≤ ((lgN p (al s) : ℝ)) ^ 2 := by
      exact_mod_cast sum_lgN_le p hp.one_lt (al s) (i s) E (hpi s)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div] at h1
    rw [Nat.cast_sum] at h2
    rw [hc, mul_one_div, Nat.cast_sum]
    linarith
  have hlg0 : ∀ s, s ∉ TT → ((lgN p (al s) : ℝ)) ^ 2 = 0 := by
    intro s hs
    simp [lgN, halT s hs]
  have hTT_lg : ∑ s ∈ TT, ((lgN p (al s) : ℝ)) ^ 2 = ∑ s, ((lgN p (al s) : ℝ)) ^ 2 :=
    Finset.sum_subset (subset_univ _) (fun s _ hs => hlg0 s hs)
  have hTT_al : ∑ s ∈ TT, (al s : ℝ) = ∑ s, (al s : ℝ) :=
    Finset.sum_subset (subset_univ _) (fun s _ hs => by rw [halT s hs, Nat.cast_zero])
  have hTT_i : ∑ s ∈ TT, ∑ e' ∈ E, (i s e' : ℝ) = ∑ s, ∑ e' ∈ E, (i s e' : ℝ) :=
    Finset.sum_subset (subset_univ _) (fun s _ hs => by simp [hiT s hs])
  have S1 := Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H1 s)
  have S2 := Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H2 s)
  have S3 := Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H3 s)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at S1 S2 S3
  have htotR : (∑ s, ((∑ x, a s x : ℕ) : ℝ)) + ∑ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) =
      ∑ s, (ls s : ℝ) := by
    exact_mod_cast htot
  have hiR : ∑ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) = ∑ s, ∑ e' ∈ E, (i s e' : ℝ) := by
    push_cast
    rfl
  have hi2R : (p : ℝ) * i2 ≤ ∑ s, (ls s : ℝ) := by exact_mod_cast hi2
  have hL0 : (0 : ℝ) ≤ ∑ s, (ls s : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

  have hgp : 1 / (p : ℝ) ≤ gamP p := by
    unfold gamP rhoP
    have hpp : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
    rw [mul_one_div, div_le_div_iff₀ hp0 hpp]
    nlinarith
  have hi2g : (i2 : ℝ) ≤ gamP p * ∑ s, (ls s : ℝ) := by
    have h1 : (i2 : ℝ) ≤ 1 / (p : ℝ) * ∑ s, (ls s : ℝ) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp0]
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hgp hL0)
  have hcg : c = gamP p + rhoP p := by rw [hgam]; ring
  unfold deLoss
  rw [hTT_lg, hTT_al, hTT_i, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hcg] at S1 S2 S3
  rw [hiR] at S2 htotR
  set A : ℝ := ∑ s, (al s : ℝ)
  set L : ℝ := ∑ s, (ls s : ℝ)
  set I : ℝ := ∑ s, ∑ e' ∈ E, (i s e' : ℝ)
  set Aa : ℝ := ∑ s, ((∑ x, a s x : ℕ) : ℝ)
  have hAa : Aa = L - I := by linarith
  rw [hAa] at S3
  nlinarith [S1, S2, S3, hi2g]

/- English proof (translation)
Introduce `n s s' a a' d haa h hd`. Establish `hmem : a - a' ∈ {e : ℕ | 1 ≤ e ∧ s + (e : ZMod n) = s'}`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_sub haa.le]`. Take the linear combination `h`.

Conclude with `(hd.2 hmem).trans (Nat.sub_le _ _)`.
-/
theorem cyclicShiftLeast : ChargeLemma := by
  intro n s s' a a' d haa h hd
  have hmem : a - a' ∈ {e : ℕ | 1 ≤ e ∧ s + (e : ZMod n) = s'} := by
    refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub haa.le]
    linear_combination h
  exact (hd.2 hmem).trans (Nat.sub_le _ _)

/- English proof (translation)
Introduce `n p TT D al cap de v i ch E hp hal hcap hi0 hch0 hE hchD hv hD hnD`. Establish `hp0 : 0 < p` using `by linarith`. Take `⟨hgs, -⟩` from `Formalism.GrowthSums.oddPowerInvSumIdentity p hp`. Establish `key : ∀ s ∈ TT, (∑' e : ℕ, (if 2 * e + 1 ∈ D s then 0 else max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0)) ≤ gamP p * al s - ∑ e ∈ E, ch s e - ∑ e ∈ E, i s e`. Introduce `s hs`.

Establish `hA : HasSum (fun e : ℕ => al s / p ^ (2 * e + 1)) (gamP p * al s)`. Establish `h` using `hgs.mul_right (al s)`. Establish `hf : (fun e : ℕ => al s / p ^ (2 * e + 1)) = fun e : ℕ => (p ^ (2 * e + 1))⁻¹ * al s`. Use function extensionality and compare the values at `e`. Rewrite using `[div_eq_mul_inv, mul_comm]`.

Rewrite using `[hf]`. Conclude with `h`. Establish `hC : HasSum (fun e : ℕ => ch s e) (∑ e ∈ E, ch s e)` using `hasSum_sum_of_ne_finset_zero (fun e he => (hE s e he).2)`. Establish `hI : HasSum (fun e : ℕ => i s e) (∑ e ∈ E, i s e)` using `hasSum_sum_of_ne_finset_zero (fun e he => (hE s e he).1)`. Establish `hR` using `(hA.sub hC).sub hI`.

Establish `hpos : ∀ e : ℕ, 0 ≤ al s / p ^ (2 * e + 1)` using `fun e => div_nonneg (hal s) (pow_nonneg hp0.le _)`. Establish `hsum : Summable (fun e : ℕ => (if 2 * e + 1 ∈ D s then (0 : ℝ) else max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0))`. Use `Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hA.summable` and prove the remaining obligations. Use `split_ifs`. Conclude with `le_rfl`.

Conclude with `le_max_right _ _`. Use `split_ifs`. Conclude with `hpos e`. Conclude with `max_le (by linarith [hcap (s + ((2 * e + 1 : ℕ) : ZMod n))]) (hpos e)`. Use `hasSum_le (fun e => ?_) hsum.hasSum hR` and prove the remaining obligations.

Use `split_ifs with h`. Use `hD s hs e h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hnD s hs e h`. Establish `h2` using `hchD s e h`.

Establish `h3` using `le_trans h1 (min_le_left _ _)`. Establish `h4` using `le_trans h1 (min_le_right _ _)`. Rewrite using `[h2]`. Conclude with `max_le (by linarith) (by linarith)`. Establish `hsum` using `Finset.sum_le_sum key`.

Rewrite `hsum` using `[Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]`. Unfold `excessGain`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem excessGainBound : ExcessGainBound := by
  intro n p TT D al cap de v i ch E hp hal hcap hi0 hch0 hE hchD hv hD hnD
  have hp0 : 0 < p := by linarith
  obtain ⟨hgs, -⟩ := Formalism.GrowthSums.oddPowerInvSumIdentity p hp
  have key : ∀ s ∈ TT, (∑' e : ℕ, (if 2 * e + 1 ∈ D s then 0 else
      max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0)) ≤
      gamP p * al s - ∑ e ∈ E, ch s e - ∑ e ∈ E, i s e := by
    intro s hs
    have hA : HasSum (fun e : ℕ => al s / p ^ (2 * e + 1)) (gamP p * al s) := by
      have h := hgs.mul_right (al s)
      have hf : (fun e : ℕ => al s / p ^ (2 * e + 1)) =
          fun e : ℕ => (p ^ (2 * e + 1))⁻¹ * al s := by
        funext e
        rw [div_eq_mul_inv, mul_comm]
      rw [hf]
      exact h
    have hC : HasSum (fun e : ℕ => ch s e) (∑ e ∈ E, ch s e) :=
      hasSum_sum_of_ne_finset_zero (fun e he => (hE s e he).2)
    have hI : HasSum (fun e : ℕ => i s e) (∑ e ∈ E, i s e) :=
      hasSum_sum_of_ne_finset_zero (fun e he => (hE s e he).1)
    have hR := (hA.sub hC).sub hI
    have hpos : ∀ e : ℕ, 0 ≤ al s / p ^ (2 * e + 1) :=
      fun e => div_nonneg (hal s) (pow_nonneg hp0.le _)
    have hsum : Summable (fun e : ℕ => (if 2 * e + 1 ∈ D s then (0 : ℝ) else
        max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0)) := by
      refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hA.summable
      · split_ifs
        · exact le_rfl
        · exact le_max_right _ _
      · split_ifs
        · exact hpos e
        · exact max_le (by linarith [hcap (s + ((2 * e + 1 : ℕ) : ZMod n))]) (hpos e)
    refine hasSum_le (fun e => ?_) hsum.hasSum hR
    split_ifs with h
    · have := hD s hs e h
      linarith
    · have h1 := hnD s hs e h
      have h2 := hchD s e h
      have h3 := le_trans h1 (min_le_left _ _)
      have h4 := le_trans h1 (min_le_right _ _)
      rw [h2]
      exact max_le (by linarith) (by linarith)
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  unfold excessGain
  linarith

/- English proof (translation)
Introduce `n p TT TTodd al cap de v paid i E hp hsub hal hcap hi0 hiE hv hpaid hodd`. Establish `hp0 : 0 < p` using `by linarith`. Establish `hsplit : ∑ s ∈ TT, ∑ e ∈ E, i s e = ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e + ∑ s ∈ TTodd, ∑ e ∈ E, i s e` using `(Finset.sum_sdiff hsub).symm`. Establish `hodd' : ∑ s ∈ TTodd, ∑ e ∈ E, i s e ≤ ∑ s ∈ TTodd, ∑' e : ℕ, min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `s hs`. Establish `hsum` using `Formalism.GrowthSums.summable_min_div_pow_two_mul_add_one p hp (al s) (hal s) cap hcap s`. Combine the equalities or inequalities in the displayed calculation. Unfold `gainG`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cappedGainBound : BCore := by
  intro n p TT TTodd al cap de v paid i E hp hsub hal hcap hi0 hiE hv hpaid hodd
  have hp0 : 0 < p := by linarith
  have hsplit : ∑ s ∈ TT, ∑ e ∈ E, i s e =
      ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e + ∑ s ∈ TTodd, ∑ e ∈ E, i s e :=
    (Finset.sum_sdiff hsub).symm
  have hodd' : ∑ s ∈ TTodd, ∑ e ∈ E, i s e ≤
      ∑ s ∈ TTodd, ∑' e : ℕ,
        min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) := by
    apply Finset.sum_le_sum
    intro s hs
    have hsum := Formalism.GrowthSums.summable_min_div_pow_two_mul_add_one p hp (al s) (hal s) cap hcap s
    calc ∑ e ∈ E, i s e
        ≤ ∑ e ∈ E, min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) :=
          Finset.sum_le_sum (fun e _ => hodd s hs e)
      _ ≤ _ := hsum.sum_le_tsum E
          (fun e _ => le_min (div_nonneg (hal s) (pow_nonneg hp0.le _)) (hcap _))
  unfold gainG
  linarith

end Formalism.InvariantFactorPaths.G7
