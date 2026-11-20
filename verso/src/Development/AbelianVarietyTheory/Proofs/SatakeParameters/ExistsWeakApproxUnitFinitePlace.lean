import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalTheory.HkFin

/- English proof (translation)
Take `⟨a, ha0, ha, -⟩` from `PI.FinOrdValD.WA.weakApprox (insert w S) (Function.update (fun v => (1 : v.adicCompletion E)) w (x : w.adicCompletion E)) (Function.update (fun _ => exp (-(n : ℤ))) w (Valued.v (x : w.adicCompletion E) * exp (-(n : ℤ)))) (fun v _ => by`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Simplify using `only [Function.update_self]`. Conclude with `mul_ne_zero ((Valuation.ne_zero_iff _).mpr x.ne_zero) exp_ne_zero`.

Simplify using `only [Function.update_of_ne h]`. Conclude with `exp_ne_zero)`. Use `⟨a, ha0, ?_, fun v hv hvw => ?_⟩` and prove the remaining obligations. Establish `h` using `ha w (Finset.mem_insert_self w S)`. Simplify using `only [Function.update_self] at h`.

Establish `hx0 : Valued.v (x : w.adicCompletion E) ≠ 0` using `(Valuation.ne_zero_iff _).mpr x.ne_zero`. Establish `e1 : (a : w.adicCompletion E) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) - 1 = (algebraMap E (w.adicCompletion E) a - x) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E)`. Rewrite using `[sub_mul, Units.mul_inv]`. Both sides reduce to the same expression. Rewrite using `[e1, map_mul, Units.val_inv_eq_inv_val, map_inv₀]`.

Rewrite `h` using `[mul_comm]`. Conclude with `(mul_inv_lt_of_lt_mul₀ h).le`. Establish `h` using `ha v (Finset.mem_insert_of_mem hv)`. Simplify using `only [Function.update_of_ne hvw] at h`. Rewrite `h` using `[← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, PI.FinOrdValD.WA.val_alg]`.

Conclude with `h.le`.
-/
theorem exists_weak_approx_unit (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℕ) :
    ∃ y : E, y ≠ 0 ∧ Valued.v ((y : w.adicCompletion E) * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1)
      ≤ WithZero.exp (-(n : ℤ)) ∧ ∀ v ∈ S, v ≠ w → v.valuation E (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  obtain ⟨a, ha0, ha, -⟩ := PI.FinOrdValD.WA.weakApprox (insert w S)
    (Function.update (fun v => (1 : v.adicCompletion E)) w (x : w.adicCompletion E))
    (Function.update (fun _ => exp (-(n : ℤ))) w (Valued.v (x : w.adicCompletion E) * exp (-(n : ℤ))))
    (fun v _ => by
      by_cases h : v = w
      · subst h; simp only [Function.update_self]
        exact mul_ne_zero ((Valuation.ne_zero_iff _).mpr x.ne_zero) exp_ne_zero
      · simp only [Function.update_of_ne h]; exact exp_ne_zero)
  refine ⟨a, ha0, ?_, fun v hv hvw => ?_⟩
  · have h := ha w (Finset.mem_insert_self w S)
    simp only [Function.update_self] at h
    have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    have e1 : (a : w.adicCompletion E) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) - 1 =
        (algebraMap E (w.adicCompletion E) a - x) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) := by
      rw [sub_mul, Units.mul_inv]; rfl
    rw [e1, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [mul_comm] at h
    exact (mul_inv_lt_of_lt_mul₀ h).le
  · have h := ha v (Finset.mem_insert_of_mem hv)
    simp only [Function.update_of_ne hvw] at h
    rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h.le

end GlobalTheory.HkFin
