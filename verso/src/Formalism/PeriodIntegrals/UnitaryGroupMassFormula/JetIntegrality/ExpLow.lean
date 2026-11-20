import Mathlib
import Formalism.PeriodIntegrals.JetsPhW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffSubstOfDegreeEqOne

noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem coeff_truncatedExp_of_degree_eq_one {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (expMv F) = MvPowerSeries.coeff e F := by
  classical
  have he : e ≠ 0 := by
    rintro rfl
    simp at hd
  have h1 : (e.sum fun _ k => k) = 1 := by
    rw [← hd]
    rfl
  change (∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (F ^ n) / (n.factorial : ℂ_[p])) = _
  rw [h1, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, MvPowerSeries.coeff_one, if_neg he]
  simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Rewrite the conclusion using the stated equalities.
-/
theorem norm_two (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp)
  have e : (2 : ℂ_[p]) = ((algebraMap ℚ_[p] (PadicAlgCl p) ((2 : ℕ) : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    rw [map_natCast, PadicComplex.coe_natCast]
    norm_num
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, h]

end PI.JetsPhW.Low
