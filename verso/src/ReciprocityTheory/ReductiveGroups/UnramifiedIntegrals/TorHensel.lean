import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorRes
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurNewton

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `: CompleteSpace (MaximalUnramifiedExtension l)` using `kur_complete l`. Choose the witnesses or unpack the hypotheses as in `⟨Q, hQ⟩ : ∃ Q : Polynomial (MaximalUnramifiedExtension l), Q.map (MaximalUnramifiedExtension l).subtype = P := by`. Establish `: P ∈ Polynomial.lifts (MaximalUnramifiedExtension l).subtype`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `i`.

Conclude with `⟨⟨P.coeff i, hK i⟩, rfl⟩`. Conclude with `(Polynomial.mem_lifts P).mp this`. Take `⟨ξ, hξ, hd⟩` from `res_full l x hx`. Establish `hξ1 : ‖ξ‖ ≤ 1` using `tch_norm_le l hξ`. Set `a : MaximalUnramifiedExtension l` to `⟨ξ, tch_mem_kur l hξ⟩`.

Establish `hev : ∀ b : MaximalUnramifiedExtension l, ((Q.eval b : MaximalUnramifiedExtension l) : ℂ_[l]) = P.eval (b : ℂ_[l])` using `fun b => by`. Rewrite using `[← hQ]`. Conclude with `(Polynomial.eval_map_apply (MaximalUnramifiedExtension l).subtype b).symm`. Establish `hdev : ∀ b : MaximalUnramifiedExtension l, ((Q.derivative.eval b : MaximalUnramifiedExtension l) : ℂ_[l]) = P.derivative.eval (b : ℂ_[l])` using `fun b => by`. Rewrite using `[← hQ, Polynomial.derivative_map]`.

Conclude with `(Polynomial.eval_map_apply (MaximalUnramifiedExtension l).subtype b).symm`. Establish `hQc : ∀ i, ‖Q.coeff i‖ ≤ 1` using `fun i => by`. Use `hP i` as an intermediate fact. Rewrite `this` using `[← hQ, Polynomial.coeff_map]`. Conclude with `this`.

Establish `e0 : ‖P.eval ξ‖ < 1`. Use `newton_lipschitz P hP ξ x hξ1 hx` as an intermediate fact. Rewrite `this` using `[h0, sub_zero, norm_sub_rev]`. Conclude with `lt_of_le_of_lt this hd`. Establish `e1 : ‖P.derivative.eval ξ‖ = 1`.

Establish `h2` using `newton_lipschitz P.derivative (newton_derivative_coeff P hP) ξ x hξ1 hx`. Rewrite `h2` using `[norm_sub_rev ξ x]`. Establish `h3 : ‖P.derivative.eval ξ - P.derivative.eval x‖ < ‖P.derivative.eval x‖`. Rewrite using `[h1]`. Conclude with `lt_of_le_of_lt h2 hd`.

Establish `h4 : P.derivative.eval ξ = (P.derivative.eval ξ - P.derivative.eval x) + P.derivative.eval x`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h3.ne, max_eq_right h3.le, h1]`. Take `⟨x', hx'0, hx'd⟩` from `newton_root Q hQc a hξ1 (show ‖((Q.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1 by rw [hev]; exact e0) (show ‖((Q.derivative.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1 by rw [hdev]; exact e1)`. Establish `hx'd' : ‖(x' : ℂ_[l]) - ξ‖ < 1`.

Establish `h5 : ‖((x' - a : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ ‖((Q.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖` using `hx'd`. Rewrite `h5` using `[hev]`. Conclude with `lt_of_le_of_lt h5 e0`. Establish `hP0 : P.eval (x' : ℂ_[l]) = 0`. Rewrite using `[← hev, hx'0]`.

Both sides reduce to the same expression. Use `set y : ℂ_[l] := (x' : ℂ_[l]) - x with hy`. Establish `hy1 : ‖y‖ < 1`. Establish `: y = ((x' : ℂ_[l]) - ξ) + (ξ - x)` using `by rw [hy]; ring`. Rewrite using `[this]`.

Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx'd' ?_)` and prove the remaining obligations. Rewrite using `[norm_sub_rev]` and apply the resulting hypothesis. Take `⟨k, hk, hexp⟩` from `newton_expansion P hP x y hx hy1.le`. Establish `hxy : x + y = (x' : ℂ_[l])` using `by rw [hy]; ring`. Rewrite `hexp` using `[hxy, hP0, h0, zero_add]`.

Establish `hfac : y * (P.derivative.eval x + k * y) = 0`. Rewrite using `[hexp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : P.derivative.eval x + k * y ≠ 0`. Introduce `h`.

Establish `h6 : P.derivative.eval x = -(k * y)` using `eq_neg_of_add_eq_zero_left h`. Rewrite `h1` using `[h6, norm_neg, norm_mul]`. Establish `: ‖k‖ * ‖y‖ < 1`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd h1 this.ne`.

Establish `hy0 : y = 0` using `(mul_eq_zero.mp hfac).resolve_right hne`. Establish `: x = (x' : ℂ_[l])` using `by rw [← hxy, hy0, add_zero]`. Rewrite using `[this]`. Conclude with `x'.2`.
-/
theorem hensel_mem (P : Polynomial ℂ_[l]) (hK : ∀ i, P.coeff i ∈ MaximalUnramifiedExtension l) (hP : ∀ i, ‖P.coeff i‖ ≤ 1)
    (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (h0 : P.eval x = 0) (h1 : ‖P.derivative.eval x‖ = 1) : x ∈ MaximalUnramifiedExtension l := by
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial (MaximalUnramifiedExtension l), Q.map (MaximalUnramifiedExtension l).subtype = P := by
    have : P ∈ Polynomial.lifts (MaximalUnramifiedExtension l).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      exact ⟨⟨P.coeff i, hK i⟩, rfl⟩
    exact (Polynomial.mem_lifts P).mp this
  obtain ⟨ξ, hξ, hd⟩ := res_full l x hx
  have hξ1 : ‖ξ‖ ≤ 1 := tch_norm_le l hξ
  let a : MaximalUnramifiedExtension l := ⟨ξ, tch_mem_kur l hξ⟩
  have hev : ∀ b : MaximalUnramifiedExtension l, ((Q.eval b : MaximalUnramifiedExtension l) : ℂ_[l]) = P.eval (b : ℂ_[l]) := fun b => by
    rw [← hQ]
    exact (Polynomial.eval_map_apply (MaximalUnramifiedExtension l).subtype b).symm
  have hdev : ∀ b : MaximalUnramifiedExtension l, ((Q.derivative.eval b : MaximalUnramifiedExtension l) : ℂ_[l]) = P.derivative.eval (b : ℂ_[l]) :=
    fun b => by
      rw [← hQ, Polynomial.derivative_map]
      exact (Polynomial.eval_map_apply (MaximalUnramifiedExtension l).subtype b).symm
  have hQc : ∀ i, ‖Q.coeff i‖ ≤ 1 := fun i => by
    have := hP i
    rw [← hQ, Polynomial.coeff_map] at this
    exact this
  have e0 : ‖P.eval ξ‖ < 1 := by
    have := newton_lipschitz P hP ξ x hξ1 hx
    rw [h0, sub_zero, norm_sub_rev] at this
    exact lt_of_le_of_lt this hd
  have e1 : ‖P.derivative.eval ξ‖ = 1 := by
    have h2 := newton_lipschitz P.derivative (newton_derivative_coeff P hP) ξ x hξ1 hx
    rw [norm_sub_rev ξ x] at h2
    have h3 : ‖P.derivative.eval ξ - P.derivative.eval x‖ < ‖P.derivative.eval x‖ := by
      rw [h1]; exact lt_of_le_of_lt h2 hd
    have h4 : P.derivative.eval ξ = (P.derivative.eval ξ - P.derivative.eval x) + P.derivative.eval x := by
      ring
    rw [h4, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h3.ne, max_eq_right h3.le, h1]
  obtain ⟨x', hx'0, hx'd⟩ := newton_root Q hQc a hξ1
    (show ‖((Q.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1 by rw [hev]; exact e0)
    (show ‖((Q.derivative.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1 by rw [hdev]; exact e1)
  have hx'd' : ‖(x' : ℂ_[l]) - ξ‖ < 1 := by
    have h5 : ‖((x' - a : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ ‖((Q.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ := hx'd
    rw [hev] at h5
    exact lt_of_le_of_lt h5 e0
  have hP0 : P.eval (x' : ℂ_[l]) = 0 := by
    rw [← hev, hx'0]; rfl
  set y : ℂ_[l] := (x' : ℂ_[l]) - x with hy
  have hy1 : ‖y‖ < 1 := by
    have : y = ((x' : ℂ_[l]) - ξ) + (ξ - x) := by rw [hy]; ring
    rw [this]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx'd' ?_)
    rwa [norm_sub_rev]
  obtain ⟨k, hk, hexp⟩ := newton_expansion P hP x y hx hy1.le
  have hxy : x + y = (x' : ℂ_[l]) := by rw [hy]; ring
  rw [hxy, hP0, h0, zero_add] at hexp
  have hfac : y * (P.derivative.eval x + k * y) = 0 := by
    rw [hexp]; ring
  have hne : P.derivative.eval x + k * y ≠ 0 := by
    intro h
    have h6 : P.derivative.eval x = -(k * y) := eq_neg_of_add_eq_zero_left h
    rw [h6, norm_neg, norm_mul] at h1
    have : ‖k‖ * ‖y‖ < 1 := by
      calc ‖k‖ * ‖y‖ ≤ 1 * ‖y‖ := by gcongr
        _ < 1 := by rwa [one_mul]
    exact absurd h1 this.ne
  have hy0 : y = 0 := (mul_eq_zero.mp hfac).resolve_right hne
  have : x = (x' : ℂ_[l]) := by rw [← hxy, hy0, add_zero]
  rw [this]
  exact x'.2

/- English proof (translation)
Establish `h2 : ‖(2 : ℂ_[l])‖ = 1`. Establish `hle : ‖(2 : ℂ_[l])‖ ≤ 1`. Use `IsUltrametricDist.norm_natCast_le_one ℂ_[l] 2` as an intermediate fact. Conclude with `this` after adjusting the coercions. Use `le_antisymm hle ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hcop : Nat.Coprime 2 l` using `(Nat.coprime_primes Nat.prime_two (Fact.out)).2 (Ne.symm hl)`. Establish `hg : Int.gcd 2 (l : ℤ) = 1`. Use `Int.gcd_natCast_natCast 2 l` as an intermediate fact.

Simplify `this` using `[Nat.Coprime.gcd_eq_one hcop]`. Establish `hz' : (1 : ℤ) = 2 * Int.gcdA 2 l + l * Int.gcdB 2 l`. Rewrite using `[← Int.gcd_eq_gcd_ab, hg]`. Both sides reduce to the same expression. Establish `h1` using `congrArg (Int.cast : ℤ → ℂ_[l]) hz'`.

Move the coercions through the operations in `at h1`. Establish `hm` using `IsUltrametricDist.norm_add_le_max (2 * ((Int.gcdA 2 l : ℤ) : ℂ_[l])) ((l : ℂ_[l]) * ((Int.gcdB 2 l : ℤ) : ℂ_[l]))`. Rewrite `hm` using `[← h1, norm_one, norm_mul, norm_mul]`. Establish `ha` using `IsUltrametricDist.norm_intCast_le_one ℂ_[l] (Int.gcdA 2 l)`. Establish `hb` using `IsUltrametricDist.norm_intCast_le_one ℂ_[l] (Int.gcdB 2 l)`.

Establish `hl1` using `norm_prime_lt_one_complexPadic (l := l)`. Break down `le_max_iff.1 hm with h | h` into its components or cases. Use polynomial arithmetic with `[norm_nonneg ((Int.gcdA 2 l : ℤ) : ℂ_[l]), norm_nonneg (2 : ℂ_[l])]`. Use polynomial arithmetic with `[norm_nonneg ((Int.gcdB 2 l : ℤ) : ℂ_[l]), norm_nonneg (l : ℂ_[l])]`. Establish `hc1 : ‖c‖ = 1` using `by rw [← h, norm_pow, hy, one_pow]`.

Use `hensel_mem l (Polynomial.X ^ 2 - Polynomial.C c) (fun i => ?_) (fun i => ?_) y hy.le ?_ ?_` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C] split_ifs`. Conclude with `(MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).one_mem hc`. Conclude with `(MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).one_mem (MaximalUnramifiedExtension l).zero_mem`. Conclude with `(MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).zero_mem hc`.

Conclude with `(MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).zero_mem (MaximalUnramifiedExtension l).zero_mem`. Apply the tactic sequence `rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C] split_ifs <;> first | (exfalso; omega) | simp [hc1]`. Simplify using `[h]`. Simplify using `[Polynomial.derivative_X_pow, norm_mul, hy]`. Rewrite using `[one_add_one_eq_two]`.

Conclude with `h2`.
-/
theorem sqrt_mem (hl : l ≠ 2) (c y : ℂ_[l]) (hc : c ∈ MaximalUnramifiedExtension l) (hy : ‖y‖ = 1) (h : y ^ 2 = c) : y ∈ MaximalUnramifiedExtension l := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hle : ‖(2 : ℂ_[l])‖ ≤ 1 := by
      have := IsUltrametricDist.norm_natCast_le_one ℂ_[l] 2
      exact_mod_cast this
    refine le_antisymm hle ?_
    by_contra hlt
    push_neg at hlt
    have hcop : Nat.Coprime 2 l := (Nat.coprime_primes Nat.prime_two (Fact.out)).2 (Ne.symm hl)
    have hg : Int.gcd 2 (l : ℤ) = 1 := by
      have := Int.gcd_natCast_natCast 2 l
      simpa [Nat.Coprime.gcd_eq_one hcop] using this
    have hz' : (1 : ℤ) = 2 * Int.gcdA 2 l + l * Int.gcdB 2 l := by
      rw [← Int.gcd_eq_gcd_ab, hg]
      rfl
    have h1 := congrArg (Int.cast : ℤ → ℂ_[l]) hz'
    push_cast at h1
    have hm := IsUltrametricDist.norm_add_le_max (2 * ((Int.gcdA 2 l : ℤ) : ℂ_[l]))
      ((l : ℂ_[l]) * ((Int.gcdB 2 l : ℤ) : ℂ_[l]))
    rw [← h1, norm_one, norm_mul, norm_mul] at hm
    have ha := IsUltrametricDist.norm_intCast_le_one ℂ_[l] (Int.gcdA 2 l)
    have hb := IsUltrametricDist.norm_intCast_le_one ℂ_[l] (Int.gcdB 2 l)
    have hl1 := norm_prime_lt_one_complexPadic (l := l)
    rcases le_max_iff.1 hm with h | h
    · nlinarith [norm_nonneg ((Int.gcdA 2 l : ℤ) : ℂ_[l]), norm_nonneg (2 : ℂ_[l])]
    · nlinarith [norm_nonneg ((Int.gcdB 2 l : ℤ) : ℂ_[l]), norm_nonneg (l : ℂ_[l])]
  have hc1 : ‖c‖ = 1 := by rw [← h, norm_pow, hy, one_pow]
  refine hensel_mem l (Polynomial.X ^ 2 - Polynomial.C c) (fun i => ?_) (fun i => ?_) y hy.le ?_ ?_
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).one_mem hc
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).one_mem (MaximalUnramifiedExtension l).zero_mem
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).zero_mem hc
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).zero_mem (MaximalUnramifiedExtension l).zero_mem
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs <;> first | (exfalso; omega) | simp [hc1]
  · simp [h]
  · simp [Polynomial.derivative_X_pow, norm_mul, hy]
    rw [one_add_one_eq_two]
    exact h2

/- English proof (translation)
Take `⟨b, hb⟩` from `IsAlgClosed.exists_pow_nat_eq c two_pos`. Establish `hb1 : ‖b‖ = 1`. Establish `: ‖b‖ ^ 2 = 1` using `by rw [← norm_pow, hb, h1]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg b) two_ne_zero).1 this`. Conclude with `⟨b, sqrt_mem l hl c b hc hb1 hb, hb, hb1⟩`.
-/
theorem exists_sqrt (hl : l ≠ 2) (c : ℂ_[l]) (hc : c ∈ MaximalUnramifiedExtension l) (h1 : ‖c‖ = 1) :
    ∃ b ∈ MaximalUnramifiedExtension l, b ^ 2 = c ∧ ‖b‖ = 1 := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
  have hb1 : ‖b‖ = 1 := by
    have : ‖b‖ ^ 2 = 1 := by rw [← norm_pow, hb, h1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg b) two_ne_zero).1 this
  exact ⟨b, sqrt_mem l hl c b hc hb1 hb, hb, hb1⟩

end ReciprocityTheory.ChartRestriction.L1
