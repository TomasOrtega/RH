import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.QLog.BFrame

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

/- English proof (translation)
Rewrite using `[Sandwich.xi, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, Sandwich.mu, add_sub_cancel]`. Use `congr 2`. Conclude with `(_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply ε`.
-/
theorem frobenius_xi (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.xi ε) = ∑ i ∈ Finset.range p, (1 + Sandwich.mu ε) ^ i := by
  rw [Sandwich.xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, Sandwich.mu,
    add_sub_cancel]
  congr 2
  exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply ε

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih]`. Use `push_cast`.

Take the linear combination `((n : F.B) * (p : F.B) ^ 2) * F.τ_sq`.
-/
theorem one_add_pow {ε : PreTilt O p} (F : BFrame ε) (i : ℕ) :
    (1 + (p : F.B) * F.τ) ^ i = 1 + (i : F.B) * ((p : F.B) * F.τ) := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((n : F.B) * (p : F.B) ^ 2) * F.τ_sq

/- English proof (translation)
Rewrite using `[frobenius_xi, map_sum]`. Establish `h1 : ∀ i ∈ Finset.range p, F.a ((1 + Sandwich.mu ε) ^ i) = 1 + (i : F.B) * ((p : F.B) * F.τ)` using `fun i _ => by rw [map_pow, map_add, map_one, ← F.p_τ, one_add_pow]`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Establish `h2 : (∑ i ∈ Finset.range p, (i : F.B)) = ((p.choose 2 : ℕ) : F.B)`. Rewrite using `[← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]`.

Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem a_frobenius_xi {ε : PreTilt O p} (F : BFrame ε) :
    F.a (WittVector.frobenius (Sandwich.xi ε)) = p * (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) := by
  rw [frobenius_xi, map_sum]
  have h1 : ∀ i ∈ Finset.range p, F.a ((1 + Sandwich.mu ε) ^ i) = 1 + (i : F.B) * ((p : F.B) * F.τ) :=
    fun i _ => by rw [map_pow, map_add, map_one, ← F.p_τ, one_add_pow]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  have h2 : (∑ i ∈ Finset.range p, (i : F.B)) = ((p.choose 2 : ℕ) : F.B) := by
    rw [← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]
  rw [h2]
  ring

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ ε _ F`. Use `⟨1 + ((p.choose 2 : ℕ) : F.B) * F.τ, ?_, ⟨((p.choose 2 : ℕ) : F.B), by ring⟩, a_frobenius_xi F⟩` and prove the remaining obligations. Establish `h : (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) * (1 - ((p.choose 2 : ℕ) : F.B) * F.τ) = 1`. Take the linear combination `(-(((p.choose 2 : ℕ) : F.B)) ^ 2) * F.τ_sq`. Conclude with `⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩`.
-/
theorem frobenius_xi_unit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∃ u : F.B, IsUnit u ∧ F.τ ∣ u - 1 ∧ F.a (WittVector.frobenius (xi ε)) = p * u := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F
  refine ⟨1 + ((p.choose 2 : ℕ) : F.B) * F.τ, ?_, ⟨((p.choose 2 : ℕ) : F.B), by ring⟩,
    a_frobenius_xi F⟩
  have h : (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) * (1 - ((p.choose 2 : ℕ) : F.B) * F.τ) = 1 := by
    linear_combination (-(((p.choose 2 : ℕ) : F.B)) ^ 2) * F.τ_sq
  exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩

end GlobalTheory.QLog.BFrame
