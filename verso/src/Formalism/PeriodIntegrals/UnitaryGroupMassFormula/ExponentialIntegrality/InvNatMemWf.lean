import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatCastMemWittIntegers

noncomputable section

namespace PI.ExpIntWProof

open PI

def Wf (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | InWf x}
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have : (p : ℂ_[p]) ^ (a + b) * (x * y) = ((p : ℂ_[p]) ^ a * x) * ((p : ℂ_[p]) ^ b * y) := by ring
    rw [this]
    exact Subring.mul_mem _ ha hb
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have : (p : ℂ_[p]) ^ (a + b) * (x + y) =
        (p : ℂ_[p]) ^ b * ((p : ℂ_[p]) ^ a * x) + (p : ℂ_[p]) ^ a * ((p : ℂ_[p]) ^ b * y) := by ring
    rw [this]
    exact Subring.add_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (p_mem p) b) ha)
      (Subring.mul_mem _ (Subring.pow_mem _ (p_mem p) a) hb)
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro x ⟨a, ha⟩
    exact ⟨a, by rw [mul_neg]; exact Subring.neg_mem _ ha⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Wf {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} : x ∈ Wf p ↔ InWf x := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_Wf]`. Take `⟨k, u, hu, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hm p hp.out.ne_one`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hpk : (p : ℂ_[p]) ^ k ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)`. Rewrite using `[Nat.cast_mul, Nat.cast_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ hpk, one_mul]`.

Conclude with `inv_natCast_mem_wittIntegers p u hu`.
-/
theorem inv_nat_mem_Wf (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : m ≠ 0) :
    ((m : ℂ_[p]))⁻¹ ∈ Wf p := by
  rw [mem_Wf]
  obtain ⟨k, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.out.ne_one
  refine ⟨k, ?_⟩
  have hpk : (p : ℂ_[p]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  rw [Nat.cast_mul, Nat.cast_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ hpk, one_mul]
  exact inv_natCast_mem_wittIntegers p u hu

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `α`. Rewrite using `[pow_zero, MvPowerSeries.coeff_one]`.

Use `split_ifs`. Conclude with `(Wf p).one_mem`. Conclude with `(Wf p).zero_mem`. Consider the case `succ n ih`. Introduce `α`.

Rewrite using `[pow_succ, MvPowerSeries.coeff_mul]`. Conclude with `(Wf p).sum_mem fun x _ => (Wf p).mul_mem (ih x.1) (mem_Wf.mpr (hf x.2))`.
-/
theorem coeff_pow_mem {σ : Type} (p : ℕ) [Fact p.Prime] (f : MvPowerSeries σ ℂ_[p])
    (hf : CoefWf f) : ∀ n : ℕ, ∀ α, MvPowerSeries.coeff α (f ^ n) ∈ Wf p := by
  classical
  intro n
  induction n with
  | zero =>
    intro α
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs
    · exact (Wf p).one_mem
    · exact (Wf p).zero_mem
  | succ n ih =>
    intro α
    rw [pow_succ, MvPowerSeries.coeff_mul]
    exact (Wf p).sum_mem fun x _ => (Wf p).mul_mem (ih x.1) (mem_Wf.mpr (hf x.2))

/- English proof (translation)
Introduce `p _ σ f hf n`. Rewrite using `[← mem_Wf]`. Use `show (∑ k ∈ Finset.range _, MvPowerSeries.coeff n (f ^ k) / (k.factorial : ℂ_[p])) ∈ Wf p`. Use `(Wf p).sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv]`.

Conclude with `(Wf p).mul_mem (coeff_pow_mem p f hf k n) (inv_nat_mem_Wf p _ (Nat.factorial_ne_zero k))`.
-/
theorem stepI : StepI := by
  intro p _ σ f hf n
  rw [← mem_Wf]
  show (∑ k ∈ Finset.range _, MvPowerSeries.coeff n (f ^ k) / (k.factorial : ℂ_[p])) ∈ Wf p
  refine (Wf p).sum_mem fun k _ => ?_
  rw [div_eq_mul_inv]
  exact (Wf p).mul_mem (coeff_pow_mem p f hf k n) (inv_nat_mem_Wf p _ (Nat.factorial_ne_zero k))

end PI.ExpIntWProof

end
