import ReciprocityTheory.Chebotarev.CasimirPowerSurjectiveSymmetric
import ReciprocityTheory.Chebotarev.EulerSum
import ReciprocityTheory.Chebotarev.EulerLim
import ReciprocityTheory.Chebotarev.PrimeSum
import ReciprocityTheory.Chebotarev.PrimeCont
import ReciprocityTheory.Chebotarev.PrimeAsymp

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

/- English proof (translation)
Rewrite using `[Complex.norm_natCast_cpow_of_re_ne_zero n (by simp; linarith)]`. Simplify using the standard rewrite rules.
-/
theorem ehold_norm_cpow (n : ℕ) {s : ℝ} (hs : 1 < s) : ‖((n : ℂ) ^ (-(s : ℂ)))‖ = (n : ℝ) ^ (-s) := by
  rw [Complex.norm_natCast_cpow_of_re_ne_zero n (by simp; linarith)]
  simp

/- English proof (translation)
Use `(summable_absNorm_rpow E hs).of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, ehold_norm_cpow _ hs]`. Conclude with `mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hf a)`.
-/
theorem ehold_summable {E : Type} [Field E] [NumberField E] (f : NZIdeal E → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun a : NZIdeal E => ‖f a * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))‖) := by
  refine (summable_absNorm_rpow E hs).of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_)
  rw [norm_mul, ehold_norm_cpow _ hs]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hf a)

/- English proof (translation)
Use `⟨fun E _ _ f hf s hs => (ehold_summable f hf hs).of_norm, fun E _ _ s hs => dedekindZeta_eq_tsum E hs, fun E _ _ s hs => summable_prm_rpow E hs⟩` and prove the remaining obligations.
-/
theorem chebyshev_first_estimate : E1 := by
  refine ⟨fun E _ _ f hf s hs => (ehold_summable f hf hs).of_norm, fun E _ _ s hs => dedekindZeta_eq_tsum E hs,
    fun E _ _ s hs => summable_prm_rpow E hs⟩

/- English proof (translation)
Introduce `E _ _ l _ χ s hs`. Establish `key` using `euler_exp_log (E := E) (fun a => χ ((Ideal.absNorm a : ℕ) : ZMod l) * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-(s : ℂ))) (by simp) (fun a b => by`. Simplify using `only [map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]`. Use the proof step `ring)`. Use the proof step `(ehold_summable (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l)) (fun a => DirichletCharacter.norm_le_one χ _) hs)`.

Use the proof step `(fun q => by`. Rewrite using `[norm_mul, ehold_norm_cpow _ hs]`. Establish `h2 : (2 : ℝ) ≤ ((Ideal.absNorm q.asIdeal : ℕ) : ℝ)` using `by exact_mod_cast two_le_Nrm q`. Establish `h3 : ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) ^ (-s) < 1` using `Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `key`.
-/
theorem chebyshev_second_estimate : E2 := by
  intro E _ _ l _ χ s hs
  have key := euler_exp_log (E := E)
    (fun a => χ ((Ideal.absNorm a : ℕ) : ZMod l) * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-(s : ℂ)))
    (by simp) (fun a b => by
      simp only [map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]; ring)
    (ehold_summable (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l)) (fun a => DirichletCharacter.norm_le_one χ _) hs)
    (fun q => by
      rw [norm_mul, ehold_norm_cpow _ hs]
      have h2 : (2 : ℝ) ≤ ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
      have h3 : ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) ^ (-s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
      calc _ ≤ 1 * ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) ^ (-s) :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (Real.rpow_nonneg (by positivity) _)
        _ < 1 := by rw [one_mul]; exact h3)
  exact key

/- English proof (translation)
The claim follows from `chebyshev_first_estimate`.
-/
theorem affine_proper_base_change : E1 := chebyshev_first_estimate

/- English proof (translation)
The claim follows from `chebyshev_second_estimate`.
-/
theorem proper_base_change : E2 := chebyshev_second_estimate

/- English proof (translation)
The claim follows from `casimirPower_surjective_symmetric'`.
-/
theorem casimirPower_surjective_symmetric : CasimirPowerSurjectiveSymmetric := casimirPower_surjective_symmetric'

/- English proof (translation)
The claim follows from `pe_log_bdd`.
-/
theorem chebyshev_log_bounded : faceMap_castSucc_comp_eq_succ := pe_log_bdd

/- English proof (translation)
The claim follows from `smoothMap_seminorm_bound'`.
-/
theorem smoothMap_seminorm_bound : SmoothMapSeminormBound := smoothMap_seminorm_bound'

end ReciprocityTheory.Cheb
