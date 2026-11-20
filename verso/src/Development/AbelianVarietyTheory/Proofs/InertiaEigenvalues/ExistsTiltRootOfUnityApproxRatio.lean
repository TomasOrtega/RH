import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorRes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open GlobalTheory.PMon.Gauss

open scoped Formalism.Per

namespace GlobalTheory.TiltRootApprox

open Ideal

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[show a + o * (k + 1) = (a + o * k) + o by ring, pow_add, mul_comm, pow_mul, h, ih]`.
-/
theorem pow_pow_add_mul {M : Type*} [Monoid M] {ξ : M} {o : ℕ} (h : ξ ^ (l ^ o) = ξ) (a k : ℕ) :
    ξ ^ (l ^ (a + o * k)) = ξ ^ (l ^ a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + o * (k + 1) = (a + o * k) + o by ring, pow_add, mul_comm, pow_mul, h, ih]

/- English proof (translation)
Establish `hcop : l.Coprime n` using `(Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hl`. Use `⟨n.totient, Nat.totient_pos.2 hn, ?_⟩` and prove the remaining obligations. Establish `hmod : l ^ n.totient % n = 1 % n` using `Nat.ModEq.pow_totient hcop`. Rewrite using `[← Nat.div_add_mod (l ^ n.totient) n, hmod, pow_add, pow_mul, h, one_pow, one_mul]`. Break down `Nat.lt_or_ge 1 n with h1 | h1` into its components or cases.

Rewrite using `[Nat.mod_eq_of_lt h1, pow_one]`. Establish `: n = 1` using `by omega`. Substitute `this` using the available equality. Simplify using `only [pow_one] at h`. Simplify using `[h]`.
-/
theorem exists_pow_pow_eq {M : Type*} [Monoid M] {ξ : M} {n : ℕ} (hn : 0 < n) (hl : ¬ l ∣ n)
    (h : ξ ^ n = 1) : ∃ o : ℕ, 0 < o ∧ ξ ^ (l ^ o) = ξ := by
  have hcop : l.Coprime n := (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hl
  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have hmod : l ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop
  rw [← Nat.div_add_mod (l ^ n.totient) n, hmod, pow_add, pow_mul, h, one_pow, one_mul]
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have : n = 1 := by omega
    subst this
    simp only [pow_one] at h
    simp [h]

/- English proof (translation)
Take `⟨q, rfl⟩ : ∃ q, o = q + 1` from `⟨o - 1, by omega⟩`. Establish `hper` using `pow_pow_add_mul (l := l) hξ`. Set `s : ℕ → ModP (Formalism.Per.OC l) l` to `fun m => Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) (ξ ^ (l ^ (q * m)))`. Establish `hs : ∀ m, s (m + 1) ^ l = s m`. Introduce `m`.

Simplify using `only [s, ← map_pow]`. Use `congr 1`. Rewrite using `[← pow_mul, ← pow_succ, show q * (m + 1) + 1 = q * m + (q + 1) * 1 by ring, hper]`. Set `ζ : Formalism.Per.Fl l` to `⟨s, hs⟩`. Use `⟨ζ, ?_, ?_⟩` and prove the remaining obligations.

Use `Perfection.ext fun m => ?_ erw [map_pow]` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `s m ^ l ^ (q + 1) = s m`. Simplify using `only [s, ← map_pow]`. Use `congr 1`. Rewrite using `[← pow_mul, ← pow_add, show q * m + (q + 1) = q * m + (q + 1) * 1 by ring, hper]`.

Use `Perfection.teichmuller_spec (I := span {((l : ℕ) : Formalism.Per.OC l)}) fun n => ?_` and prove the remaining obligations. Use `⟨ξ ^ (l ^ (q * n)), rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul, ← pow_add, show q * n + n = 0 + (q + 1) * n by ring, hper, pow_zero, pow_one]`.
-/
theorem exists_tilt_lift (ξ : Formalism.Per.OC l) {o : ℕ} (ho : 0 < o) (hξ : ξ ^ (l ^ o) = ξ) :
    ∃ ζ : Formalism.Per.Fl l, ζ ^ (l ^ o) = ζ ∧ ζ.untilt = ξ := by
  obtain ⟨q, rfl⟩ : ∃ q, o = q + 1 := ⟨o - 1, by omega⟩
  have hper := pow_pow_add_mul (l := l) hξ
  let s : ℕ → ModP (Formalism.Per.OC l) l := fun m =>
    Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) (ξ ^ (l ^ (q * m)))
  have hs : ∀ m, s (m + 1) ^ l = s m := by
    intro m
    simp only [s, ← map_pow]
    congr 1
    rw [← pow_mul, ← pow_succ, show q * (m + 1) + 1 = q * m + (q + 1) * 1 by ring, hper]
  let ζ : Formalism.Per.Fl l := ⟨s, hs⟩
  refine ⟨ζ, ?_, ?_⟩
  · refine Perfection.ext fun m => ?_
    erw [map_pow]
    change s m ^ l ^ (q + 1) = s m
    simp only [s, ← map_pow]
    congr 1
    rw [← pow_mul, ← pow_add, show q * m + (q + 1) = q * m + (q + 1) * 1 by ring, hper]
  · refine Perfection.teichmuller_spec (I := span {((l : ℕ) : Formalism.Per.OC l)}) fun n => ?_
    refine ⟨ξ ^ (l ^ (q * n)), rfl, ?_⟩
    rw [← pow_mul, ← pow_add, show q * n + n = 0 + (q + 1) * n by ring, hper, pow_zero, pow_one]

end GlobalTheory.TiltRootApprox

namespace GlobalTheory.TiltRootApprox

open Ideal

/- English proof (translation)
Introduce `l _ y y' hy' hn`. Establish `h0 : ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0` using `fun h => hy' (GlobalTheory.TiltAbs.eq_zero_of_untilt y' (Subtype.ext h))`. Establish `hpos : 0 < ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖` using `norm_pos_iff.2 h0`. Establish `hd : y'.untilt ∣ y.untilt`. Use `⟨⟨((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Rewrite using `[norm_div, hn, div_self hpos.ne']`. Express the relevant statement in the definitionally equal form `_ = ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) * (_ / _)`. Clear the denominators using the available nonvanishing facts. Take `⟨u, rfl⟩` from `GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd hd`. Establish `hmul : ∀ a b : Formalism.Per.Fl l, (((a * b).untilt : Formalism.Per.OC l) : ℂ_[l]) = ((a.untilt : Formalism.Per.OC l) : ℂ_[l]) * ((b.untilt : Formalism.Per.OC l) : ℂ_[l])`.

Introduce `a b`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `hu : ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1`. Rewrite `hn` using `[hmul, norm_mul]`.

Use `hn` as an intermediate fact. Clear denominators, using `at this` for the nonvanishing conditions. Use polynomial arithmetic with `[this]`. Take `⟨ξ, hξ, hclose⟩` from `ReciprocityTheory.ChartRestriction.L1.res_full l _ hu.le`. Establish `hξn : ‖ξ‖ ≤ 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sub_sub_cancel]`. Use `_ ≤ max ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ‖ := by`. Use `IsUltrametricDist.norm_add_le_max (((u.untilt : Formalism.Per.OC l) : ℂ_[l])) (-(((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ))` as an intermediate fact. Rewrite `this` using `[← sub_eq_add_neg, norm_neg]`. Then use the resulting hypothesis.

Use `_ ≤ 1 := max_le hu.le hclose.le`. Establish `hξ0 : ξ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hclose` using `[sub_zero, hu]`. Conclude with `lt_irrefl _ hclose`.

Choose the witnesses or unpack the hypotheses as in `⟨n, hn0, hln, hξpow⟩ : ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ξ ^ n = 1 := by`. Break down `Set.mem_insert_iff.1 hξ with h | h` into its components or cases. Conclude with `absurd h hξ0`. Conclude with `h`. Take `⟨o, ho, hξo⟩` from `exists_pow_pow_eq hn0 hln hξpow`.

Set `ξ' : Formalism.Per.OC l` to `⟨ξ, (GlobalTheory.RingBasics.mem_OC _).2 hξn⟩`. Establish `hξ'o : ξ' ^ (l ^ o) = ξ'` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `ξ ^ (l ^ o) = ξ`. Conclude with `hξo)`. Take `⟨ζ, hζo, hζu⟩` from `exists_tilt_lift ξ' ho hξ'o`.

Use `⟨ζ, o, ho, hζo, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hξ0` to reduce the goal to its premises. Establish `h00 : (0 : Formalism.Per.Fl l).untilt = 0` using `Perfection.teichmuller_zero`. Rewrite `hζu` using `[h00]`.

Use `congrArg Subtype.val hζu` as an intermediate fact. Conclude with `this.symm`. Establish `e : y' * u - ζ * y' = (u - ζ) * y'` using `by ring`. Rewrite using `[e, hmul, norm_mul]`. Establish `hlt : ‖(((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l])‖ < 1`.

Establish `hmk : Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) ((u - ζ).untilt) = Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) (u.untilt - ζ.untilt)`. Rewrite using `[PreTilt.mk_untilt_eq_coeff_zero, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero, PreTilt.mk_untilt_eq_coeff_zero]`. Rewrite `hmk` using `[Ideal.Quotient.eq, ← pow_one (span {((l : ℕ) : Formalism.Per.OC l)}), GlobalTheory.RingBasics.mem_span_pow_OC, pow_one]`. Establish `e2 : (((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l]) = ((((u - ζ).untilt - (u.untilt - ζ.untilt) : Formalism.Per.OC l)) : ℂ_[l]) + (((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ)`. Rewrite using `[hζu]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hclose)` and prove the remaining obligations. Conclude with `lt_of_le_of_lt hmk GlobalTheory.RingBasics.norm_p_lt`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_root_approx : ∀ (l : ℕ) [Fact l.Prime] (y y' : Formalism.Per.Fl l), y' ≠ 0 →
    ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ →
    ∃ (ζ : Formalism.Per.Fl l) (o : ℕ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧
      ‖(((y - ζ * y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ <
        ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  intro l _ y y' hy' hn
  have h0 : ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := fun h =>
    hy' (GlobalTheory.TiltAbs.eq_zero_of_untilt y' (Subtype.ext h))
  have hpos : 0 < ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := norm_pos_iff.2 h0
  have hd : y'.untilt ∣ y.untilt := by
    refine ⟨⟨((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]),
      (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, hn, div_self hpos.ne']
    · change _ = ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) * (_ / _)
      field_simp
  obtain ⟨u, rfl⟩ := GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd hd
  have hmul : ∀ a b : Formalism.Per.Fl l, (((a * b).untilt : Formalism.Per.OC l) : ℂ_[l]) =
      ((a.untilt : Formalism.Per.OC l) : ℂ_[l]) * ((b.untilt : Formalism.Per.OC l) : ℂ_[l]) := by
    intro a b
    rw [map_mul]
    rfl
  have hu : ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 := by
    rw [hmul, norm_mul] at hn
    have := hn
    field_simp at this
    nlinarith [this]
  obtain ⟨ξ, hξ, hclose⟩ := ReciprocityTheory.ChartRestriction.L1.res_full l _ hu.le
  have hξn : ‖ξ‖ ≤ 1 := by
    calc ‖ξ‖ = ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - (((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ)‖ := by
          rw [sub_sub_cancel]
      _ ≤ max ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ‖ := by
          have := IsUltrametricDist.norm_add_le_max (((u.untilt : Formalism.Per.OC l) : ℂ_[l]))
            (-(((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ))
          rwa [← sub_eq_add_neg, norm_neg] at this
      _ ≤ 1 := max_le hu.le hclose.le
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [sub_zero, hu] at hclose
    exact lt_irrefl _ hclose
  obtain ⟨n, hn0, hln, hξpow⟩ : ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ξ ^ n = 1 := by
    rcases Set.mem_insert_iff.1 hξ with h | h
    · exact absurd h hξ0
    · exact h
  obtain ⟨o, ho, hξo⟩ := exists_pow_pow_eq hn0 hln hξpow
  let ξ' : Formalism.Per.OC l := ⟨ξ, (GlobalTheory.RingBasics.mem_OC _).2 hξn⟩
  have hξ'o : ξ' ^ (l ^ o) = ξ' := Subtype.ext (by
    change ξ ^ (l ^ o) = ξ
    exact hξo)
  obtain ⟨ζ, hζo, hζu⟩ := exists_tilt_lift ξ' ho hξ'o
  refine ⟨ζ, o, ho, hζo, ?_, ?_⟩
  · rintro rfl
    apply hξ0
    have h00 : (0 : Formalism.Per.Fl l).untilt = 0 := Perfection.teichmuller_zero
    rw [h00] at hζu
    have := congrArg Subtype.val hζu
    exact this.symm
  · have e : y' * u - ζ * y' = (u - ζ) * y' := by ring
    rw [e, hmul, norm_mul]
    have hlt : ‖(((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l])‖ < 1 := by
      have hmk : Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) ((u - ζ).untilt) =
          Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) (u.untilt - ζ.untilt) := by
        rw [PreTilt.mk_untilt_eq_coeff_zero, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
          PreTilt.mk_untilt_eq_coeff_zero]
      rw [Ideal.Quotient.eq, ← pow_one (span {((l : ℕ) : Formalism.Per.OC l)}),
        GlobalTheory.RingBasics.mem_span_pow_OC, pow_one] at hmk
      have e2 : (((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l]) =
          ((((u - ζ).untilt - (u.untilt - ζ.untilt) : Formalism.Per.OC l)) : ℂ_[l]) +
            (((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ) := by
        rw [hζu]
        push_cast
        ring
      rw [e2]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hclose)
      exact lt_of_le_of_lt hmk GlobalTheory.RingBasics.norm_p_lt
    calc ‖(((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l])‖ * ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖
        < 1 * ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := mul_lt_mul_of_pos_right hlt hpos
      _ = _ := one_mul _

end GlobalTheory.TiltRootApprox
