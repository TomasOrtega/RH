import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomial

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.LogUniq

/- English proof (translation)
Introduce `p _ O E _ _ _ hF d μ hμ R hlin hcob`. Establish `hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : E)`. Introduce `n hn`. Take `⟨a, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one`. Rewrite using `[Nat.cast_mul, Nat.cast_pow]`.

Use `(hF.unit_p.pow a).mul ?_` and prove the remaining obligations. Establish `hc : Nat.Coprime m p` using `Nat.coprime_comm.1 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)`. Use `(hF.unit_coprime m hc).map (algebraMap O E)` as an intermediate fact. Simplify using `using this`. Establish `hL : IsLift (RingHom.id O) μ` using `⟨hμ.const, hμ.unit, hμ.comm, by simpa using hμ⟩`.

Establish `hlow : ∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (up E μ i) = coeff α (addLaw E d i)`. Introduce `i α hα`. Rewrite using `[up, coeff_map, GlobalTheory.CobHom.coeff_lift_low hL i α hα, GlobalTheory.Katz.LowLaw.coeff_addLaw]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hdeg : ∀ a e : Fin d →₀ ℕ, (Finsupp.sumElim a e).degree = (a + e).degree`.

Introduce `a e`. Rewrite using `[Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_sum_type, ← Finset.sum_add_distrib]`. Simplify using the standard rewrite rules. Establish `key : ∀ N : ℕ, ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α R = 0`. Introduce `N`.

Proceed by induction on `N with`. Consider the case `zero => intro α h`. Use linear arithmetic over natural numbers and integers. Consider the case `succ N ih`. Introduce `α hα`.

Break down `lt_or_eq_of_le (Nat.lt_succ_iff.1 hα) with h | h` into its components or cases. Conclude with `ih α h`. Establish `hc` using `(GlobalTheory.CobLead.cob_eq_additive_lead E d (up E μ) N hlow).1 R ih`. Establish `hcoef : ∀ a e : Fin d →₀ ℕ, a + e = α → coeff (Finsupp.sumElim a e) (cob1 (addLaw E d) R) = 0`. Introduce `a e hae`.

Rewrite using `[← (hc _).2 (by rw [hdeg, hae, h]), hcob, map_zero]`. Break down `Nat.lt_or_ge N 2 with hN | hN` into its components or cases. Use `interval_cases N`. Establish `h0 : α = 0` using `(Finsupp.degree_eq_zero_iff α).1 h`. Substitute `h0` using the available equality.

Use `hcoef 0 0 (by simp)` as an intermediate fact. Rewrite `this` using `[GlobalTheory.CobHom.coeff_cob1_additive_law_binomial]`. Simplify using `using this`. Take `⟨j, rfl⟩` from `GlobalTheory.Katz.LowLaw.eq_single_of_degree_eq_one h`. Conclude with `congrFun hlin j`.

Take `⟨i, hi⟩ : ∃ i, α i ≠ 0` from `by by_contra! hc0`. Establish `: α = 0` using `Finsupp.ext hc0`. Rewrite `h` using `[this, map_zero]`. Use linear arithmetic over natural numbers and integers. Use `set a := α - Finsupp.single i 1 with ha`.

Establish `hae : a + Finsupp.single i 1 = α`. Use extensionality with `k`. Simplify using `only [ha, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs with h1 <;> (try subst h1) <;> omega`. Establish `ha0 : a ≠ 0`.

Introduce `h0`. Rewrite `hae` using `[h0, zero_add]`. Rewrite `h` using `[← hae, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers. Establish `hs0 : Finsupp.single i 1 ≠ 0` using `Finsupp.single_ne_zero.2 one_ne_zero`.

Use `hcoef a (Finsupp.single i 1) hae` as an intermediate fact. Rewrite `this` using `[GlobalTheory.CobHom.coeff_cob1_additive_law_binomial, if_neg hs0, if_neg ha0, sub_zero, sub_zero, hae]`. Establish `hpos : (∏ s, (α s).choose (a s)) ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun s _ => (Nat.choose_pos ?_).ne'` and prove the remaining obligations. Rewrite using `[← hae]`.

Simplify using the standard rewrite rules. Conclude with `(hunit _ hpos).mul_right_eq_zero.1 this`. Use extensionality with `α`. Simplify using `using key (α.degree + 1) α (by omega)`.
-/
theorem eq_zero_of_linear_zero_coboundary_zero_fractions : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E]
    [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ R : MvPowerSeries (Fin d) E,
    lin R = 0 → cob1 (up E μ) R = 0 → R = 0 := by
  intro p _ O E _ _ _ hF d μ hμ R hlin hcob
  classical
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : E) := by
    intro n hn
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
    rw [Nat.cast_mul, Nat.cast_pow]
    refine (hF.unit_p.pow a).mul ?_
    have hc : Nat.Coprime m p :=
      Nat.coprime_comm.1 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
    have := (hF.unit_coprime m hc).map (algebraMap O E)
    simpa using this
  have hL : IsLift (RingHom.id O) μ := ⟨hμ.const, hμ.unit, hμ.comm, by simpa using hμ⟩
  have hlow : ∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 →
      coeff α (up E μ i) = coeff α (addLaw E d i) := by
    intro i α hα
    rw [up, coeff_map, GlobalTheory.CobHom.coeff_lift_low hL i α hα, GlobalTheory.Katz.LowLaw.coeff_addLaw]
    split_ifs <;> simp
  have hdeg : ∀ a e : Fin d →₀ ℕ, (Finsupp.sumElim a e).degree = (a + e).degree := by
    intro a e
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_sum_type,
      ← Finset.sum_add_distrib]
    simp
  have key : ∀ N : ℕ, ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α R = 0 := by
    intro N
    induction N with
    | zero => intro α h; omega
    | succ N ih =>
      intro α hα
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hα) with h | h
      · exact ih α h
      have hc := (GlobalTheory.CobLead.cob_eq_additive_lead E d (up E μ) N hlow).1 R ih
      have hcoef : ∀ a e : Fin d →₀ ℕ, a + e = α →
          coeff (Finsupp.sumElim a e) (cob1 (addLaw E d) R) = 0 := by
        intro a e hae
        rw [← (hc _).2 (by rw [hdeg, hae, h]), hcob, map_zero]
      rcases Nat.lt_or_ge N 2 with hN | hN
      · interval_cases N
        · have h0 : α = 0 := (Finsupp.degree_eq_zero_iff α).1 h
          subst h0
          have := hcoef 0 0 (by simp)
          rw [GlobalTheory.CobHom.coeff_cob1_additive_law_binomial] at this
          simpa using this
        · obtain ⟨j, rfl⟩ := GlobalTheory.Katz.LowLaw.eq_single_of_degree_eq_one h
          exact congrFun hlin j
      · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
          by_contra! hc0
          have : α = 0 := Finsupp.ext hc0
          rw [this, map_zero] at h
          omega
        set a := α - Finsupp.single i 1 with ha
        have hae : a + Finsupp.single i 1 = α := by
          ext k
          simp only [ha, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply]
          split_ifs with h1 <;> (try subst h1) <;> omega
        have ha0 : a ≠ 0 := by
          intro h0
          rw [h0, zero_add] at hae
          rw [← hae, Finsupp.degree_single] at h
          omega
        have hs0 : Finsupp.single i 1 ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
        have := hcoef a (Finsupp.single i 1) hae
        rw [GlobalTheory.CobHom.coeff_cob1_additive_law_binomial, if_neg hs0, if_neg ha0, sub_zero, sub_zero, hae] at this
        have hpos : (∏ s, (α s).choose (a s)) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.2 fun s _ => (Nat.choose_pos ?_).ne'
          rw [← hae]; simp
        exact (hunit _ hpos).mul_right_eq_zero.1 this
  ext α
  simpa using key (α.degree + 1) α (by omega)

end GlobalTheory.LogUniq
