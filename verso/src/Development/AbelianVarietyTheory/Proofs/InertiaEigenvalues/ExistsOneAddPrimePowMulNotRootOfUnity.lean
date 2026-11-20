import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.SmallRootCl

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `h1 : ‖1 + x‖ ≤ 1` using `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hx)`. Establish `e : (1 + x) ^ (m + 1) - 1 = ((1 + x) ^ m - 1) * (1 + x) + x` using `by ring`.

Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_one_add_pow_sub_one_le (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (m : ℕ) :
    ‖(1 + x) ^ m - 1‖ ≤ ‖x‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ‖1 + x‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hx)
    have e : (1 + x) ^ (m + 1) - 1 = ((1 + x) ^ m - 1) * (1 + x) + x := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    calc ‖(1 + x) ^ m - 1‖ * ‖1 + x‖ ≤ ‖x‖ * 1 :=
          mul_le_mul ih h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `h` using `PadicComplex.norm_extends' l (q : ℚ_[l])`. Rewrite `h` using `[map_natCast, PadicComplex.coe_natCast]`. Rewrite using `[h]`. Distinguish the cases in `hql : q = l`.

Substitute `hql` using the available equality. Rewrite using `[Padic.norm_p]`. Establish `hc : Nat.Coprime l q` using `(Nat.coprime_primes hl hq).2 (Ne.symm hql)`. Rewrite using `[(Padic.norm_natCast_eq_one_iff).2 hc]`. Conclude with `inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_lt.le)`.
-/
theorem inv_le_norm_prime (q : ℕ) (hq : q.Prime) : (l : ℝ)⁻¹ ≤ ‖(q : ℂ_[l])‖ := by
  have hl : l.Prime := Fact.out
  have h := PadicComplex.norm_extends' l (q : ℚ_[l])
  rw [map_natCast, PadicComplex.coe_natCast] at h
  rw [h]
  by_cases hql : q = l
  · subst hql; rw [Padic.norm_p]
  · have hc : Nat.Coprime l q := (Nat.coprime_primes hl hq).2 (Ne.symm hql)
    rw [(Padic.norm_natCast_eq_one_iff).2 hc]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_lt.le)

/- English proof (translation)
Introduce `hpow`. Establish `hl : l.Prime` using `Fact.out`. Establish `hx1 : ‖x‖ ≤ 1` using `hx.le.trans (inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_lt.le))`. Use `set ζ := 1 + x with hζ`. Establish `hfin : IsOfFinOrder ζ` using `isOfFinOrder_iff_pow_eq_one.2 ⟨i, by omega, hpow⟩`.

Use `set d := orderOf ζ with hd`. Establish `hdpos : 0 < d` using `hfin.orderOf_pos`. Establish `hd1 : d ≠ 1`. Introduce `h`. Rewrite `h` using `[hd, orderOf_eq_one_iff, hζ]`.

Conclude with `hx0 (by linear_combination h)`. Use `set q := d.minFac with hqdef`. Establish `hq : q.Prime` using `Nat.minFac_prime hd1`. Establish `hqd : q ∣ d` using `Nat.minFac_dvd d`. Use `set η := ζ ^ (d / q) with hη`.

Establish `hηq : η ^ q = 1`. Rewrite using `[hη, ← pow_mul, Nat.div_mul_cancel hqd, hd]`. Conclude with `pow_orderOf_eq_one ζ`. Establish `hη1 : η ≠ 1`. Apply `pow_ne_one_of_lt_orderOf` to reduce the goal to its premises.

Conclude with `(Nat.div_pos (Nat.le_of_dvd hdpos hqd) hq.pos).ne'`. Conclude with `Nat.div_lt_self hdpos hq.one_lt`. Establish `hsum : ∑ j ∈ Finset.range q, η ^ j = 0`. Establish `h` using `geom_sum_mul η q`. Rewrite `h` using `[hηq, sub_self]`.

Conclude with `(mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hη1)`. Establish `hsmall : ∀ j, ‖η ^ j - 1‖ ≤ ‖x‖` using `fun j => by`. Rewrite using `[hη, ← pow_mul]`. Conclude with `norm_one_add_pow_sub_one_le x hx1 _`. Establish `hqeq : (q : ℂ_[l]) = -∑ j ∈ Finset.range q, (η ^ j - 1)`.

Rewrite using `[Finset.sum_sub_distrib, hsum]`. Simplify using the standard rewrite rules. Establish `hle : ‖(q : ℂ_[l])‖ ≤ ‖x‖`. Rewrite using `[hqeq, norm_neg]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => hsmall j`.

Use `inv_le_norm_prime (l := l) q hq` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_root (x : ℂ_[l]) (hx0 : x ≠ 0) (hx : ‖x‖ < (l : ℝ)⁻¹) (i : ℕ) (hi : 1 ≤ i) :
    (1 + x) ^ i ≠ 1 := by
  intro hpow
  have hl : l.Prime := Fact.out
  have hx1 : ‖x‖ ≤ 1 := hx.le.trans (inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_lt.le))
  set ζ := 1 + x with hζ
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨i, by omega, hpow⟩
  set d := orderOf ζ with hd
  have hdpos : 0 < d := hfin.orderOf_pos
  have hd1 : d ≠ 1 := by
    intro h
    rw [hd, orderOf_eq_one_iff, hζ] at h
    exact hx0 (by linear_combination h)
  set q := d.minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime hd1
  have hqd : q ∣ d := Nat.minFac_dvd d
  set η := ζ ^ (d / q) with hη
  have hηq : η ^ q = 1 := by
    rw [hη, ← pow_mul, Nat.div_mul_cancel hqd, hd]; exact pow_orderOf_eq_one ζ
  have hη1 : η ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · exact (Nat.div_pos (Nat.le_of_dvd hdpos hqd) hq.pos).ne'
    · exact Nat.div_lt_self hdpos hq.one_lt
  have hsum : ∑ j ∈ Finset.range q, η ^ j = 0 := by
    have h := geom_sum_mul η q
    rw [hηq, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hη1)
  have hsmall : ∀ j, ‖η ^ j - 1‖ ≤ ‖x‖ := fun j => by
    rw [hη, ← pow_mul]; exact norm_one_add_pow_sub_one_le x hx1 _
  have hqeq : (q : ℂ_[l]) = -∑ j ∈ Finset.range q, (η ^ j - 1) := by
    rw [Finset.sum_sub_distrib, hsum]; simp
  have hle : ‖(q : ℂ_[l])‖ ≤ ‖x‖ := by
    rw [hqeq, norm_neg]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => hsmall j
  have := inv_le_norm_prime (l := l) q hq
  linarith

/- English proof (translation)
Introduce `l _ a ha`. Establish `hl : l.Prime` using `Fact.out`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `hnl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹`.

Establish `h` using `PadicComplex.norm_extends' l (l : ℚ_[l])`. Rewrite `h` using `[Padic.norm_p, map_natCast, PadicComplex.coe_natCast]`. Conclude with `h`. Establish `ha0 : 0 < ‖a‖` using `norm_pos_iff.2 ha`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one (div_pos (inv_pos.2 hl0) ha0) (inv_lt_one_of_one_lt₀ hl1)`.

Use `set x := (l : ℂ_[l]) ^ k * a with hxdef`. Establish `hxn : ‖x‖ < (l : ℝ)⁻¹`. Rewrite using `[hxdef, norm_mul, norm_pow, hnl]`. Conclude with `(lt_div_iff₀ ha0).1 hk`. Establish `hl0' : (l : ℂ_[l]) ≠ 0` using `by exact_mod_cast hl.ne_zero`.

Establish `hx0 : x ≠ 0` using `mul_ne_zero (pow_ne_zero _ hl0') ha`. Use `⟨k, ?_, fun i hi => not_root x hx0 hxn i hi⟩` and prove the remaining obligations. Introduce `h`. Establish `: x = -1` using `by linear_combination h`. Establish `h1 : ‖x‖ = 1` using `by rw [this, norm_neg, norm_one]`.

Establish `: (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_one_add_pow_mul_not_root : ∀ (l : ℕ) [Fact l.Prime] (a : ℂ_[l]), a ≠ 0 → ∃ k : ℕ, 1 + (l : ℂ_[l]) ^ k * a ≠ 0 ∧ ∀ i : ℕ, 1 ≤ i → (1 + (l : ℂ_[l]) ^ k * a) ^ i ≠ 1 := by
  intro l _ a ha
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hnl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p, map_natCast, PadicComplex.coe_natCast] at h
    exact h
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (inv_pos.2 hl0) ha0)
    (inv_lt_one_of_one_lt₀ hl1)
  set x := (l : ℂ_[l]) ^ k * a with hxdef
  have hxn : ‖x‖ < (l : ℝ)⁻¹ := by
    rw [hxdef, norm_mul, norm_pow, hnl]
    exact (lt_div_iff₀ ha0).1 hk
  have hl0' : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hx0 : x ≠ 0 := mul_ne_zero (pow_ne_zero _ hl0') ha
  refine ⟨k, ?_, fun i hi => not_root x hx0 hxn i hi⟩
  intro h
  have : x = -1 := by linear_combination h
  have h1 : ‖x‖ = 1 := by rw [this, norm_neg, norm_one]
  have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  linarith

end GlobalTheory.SmallRootCl
