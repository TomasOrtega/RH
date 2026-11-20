import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace GlobalTheory.CompanionTheory.Ar.HT

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, p = n + 1` from `⟨p - 1, by have := hp.pos; omega⟩`. Establish `h` using `hζ.prod_one_sub_pow_eq_order`. Establish `h2 : Associated (∏ _k ∈ Finset.range n, (ζ - 1)) (∏ k ∈ Finset.range n, (1 - ζ ^ (k + 1)))`. Use `Associated.prod _ _ _ fun k hk => ?_` and prove the remaining obligations. Establish `hk'` using `Finset.mem_range.1 hk`.

Establish `hc : (k + 1).Coprime (n + 1)` using `(Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm`. Use `hζ.associated_sub_one_pow_sub_one_of_coprime hc` as an intermediate fact. Rewrite using `[← neg_sub (ζ ^ (k + 1)) 1]`. Conclude with `this.neg_right`. Rewrite `h2` using `[h, Finset.prod_const, Finset.card_range]`.

Simplify using `using h2`.
-/
theorem primRoot_sub_one_pow_associated {O : Type*} [CommRing O] [IsDomain O] {p : ℕ}
    (hp : p.Prime) {ζ : O} (hζ : IsPrimitiveRoot ζ p) :
    Associated ((ζ - 1) ^ (p - 1)) (p : O) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h := hζ.prod_one_sub_pow_eq_order
  have h2 : Associated (∏ _k ∈ Finset.range n, (ζ - 1)) (∏ k ∈ Finset.range n, (1 - ζ ^ (k + 1))) := by
    refine Associated.prod _ _ _ fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hc : (k + 1).Coprime (n + 1) :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
    have := hζ.associated_sub_one_pow_sub_one_of_coprime hc
    rw [← neg_sub (ζ ^ (k + 1)) 1]
    exact this.neg_right
  rw [h, Finset.prod_const, Finset.card_range] at h2
  simpa using h2

/- English proof (translation)
Introduce `C _ v O _ _ hv p hp ζ hζ _`. Establish `hp` using `hp.out`. Establish `h2` using `hp.two_le`. Establish `: IsDomain O` using `hv.hom_inj.isDomain (algebraMap O C)`. Establish `hζO : IsPrimitiveRoot ζ p` using `hζ.of_map_of_injective hv.hom_inj`.

Establish `ha` using `primRoot_sub_one_pow_associated hp hζO`. Establish `h1 : v (algebraMap O C (ζ - 1)) ^ (p - 1) = v (p : C)`. Take `⟨u, hu⟩` from `ha`. Use `congrArg (fun x => v (algebraMap O C x)) hu` as an intermediate fact. Simplify using `only [map_mul, map_pow, map_natCast, hv.one_of_isUnit u.isUnit, mul_one] at this`.

Conclude with `this`. Use `⟨h1, (dvd_pow_self _ (by omega)).trans ha.dvd, ?_, fun hvp => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_one, sub_ne_zero]`. Conclude with `hζ.ne_one hp.one_lt`. Rewrite `h1` using `[hvp]`.

Establish `h3` using `congrArg (fun x : NNReal => Real.log (x : ℝ)) h1`. Simplify using `only [NNReal.coe_pow, Real.log_pow, NNReal.coe_inv, Real.log_inv, NNReal.coe_natCast] at h3`. Rewrite `h3` using `[Nat.cast_sub hp.one_le, Nat.cast_one]`. Establish `h4 : (p : ℝ) - 1 ≠ 0`. Establish `: (2 : ℝ) ≤ p` using `by exact_mod_cast h2`.

Combine the linear relations using `[this] |> fun (h : (0:ℝ) < (p:ℝ) - 1) => h.ne'`. Rewrite using `[eq_div_iff h4]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem val_primRoot_sub_one : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (p : ℕ) [Fact p.Prime] (ζ : O), IsPrimitiveRoot (algebraMap O C ζ) p → v (p : C) < 1 → v (algebraMap O C (ζ - 1)) ^ (p - 1) = v (p : C) ∧ (ζ - 1) ∣ (p : O) ∧ algebraMap O C (ζ - 1) ≠ 0 ∧ (v (p : C) = (p : NNReal)⁻¹ → -Real.log (v (algebraMap O C (ζ - 1))) = Real.log p / ((p : ℝ) - 1)) := by
  intro C _ v O _ _ hv p hp ζ hζ _
  have hp := hp.out
  have h2 := hp.two_le
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have hζO : IsPrimitiveRoot ζ p := hζ.of_map_of_injective hv.hom_inj
  have ha := primRoot_sub_one_pow_associated hp hζO
  have h1 : v (algebraMap O C (ζ - 1)) ^ (p - 1) = v (p : C) := by
    obtain ⟨u, hu⟩ := ha
    have := congrArg (fun x => v (algebraMap O C x)) hu
    simp only [map_mul, map_pow, map_natCast, hv.one_of_isUnit u.isUnit, mul_one] at this
    exact this
  refine ⟨h1, (dvd_pow_self _ (by omega)).trans ha.dvd, ?_, fun hvp => ?_⟩
  · rw [map_sub, map_one, sub_ne_zero]
    exact hζ.ne_one hp.one_lt
  · rw [hvp] at h1
    have h3 := congrArg (fun x : NNReal => Real.log (x : ℝ)) h1
    simp only [NNReal.coe_pow, Real.log_pow, NNReal.coe_inv, Real.log_inv, NNReal.coe_natCast] at h3
    rw [Nat.cast_sub hp.one_le, Nat.cast_one] at h3
    have h4 : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast h2
      linarith [this] |> fun (h : (0:ℝ) < (p:ℝ) - 1) => h.ne'
    rw [eq_div_iff h4]
    linarith

end GlobalTheory.CompanionTheory.Ar.HT
