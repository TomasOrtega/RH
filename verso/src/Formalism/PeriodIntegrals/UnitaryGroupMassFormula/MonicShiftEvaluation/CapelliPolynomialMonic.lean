import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonicShiftEvaluation.EvalXAddCMul

open Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation

open Formalism.QuantumDeterminants

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_`. Use `⟨by simp [PQ], fun n hn => ?_, fun n _ => by simp [PQ]⟩` and prove the remaining obligations.

Simplify using `[PQ, coeff_one, Nat.pos_iff_ne_zero.mp hn]`. Consider the case `succ i ih`. Introduce `hi`. Establish `h : i < r` using `hi`. Take `⟨h1, h2, h3⟩` from `ih h.le`.

Simplify using `only [PQ, dif_pos h]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_sub, add_mul, coeff_add, coeff_X_mul, coeff_C_mul, coeff_C_mul, h1, h2 (i + 1) (Nat.lt_succ_self i), h3 (i + 1) (Nat.le_succ i)]`. Simplify using the standard rewrite rules. Introduce `n hn`.

Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[coeff_sub, add_mul, coeff_add, coeff_X_mul, coeff_C_mul, coeff_C_mul, h2 m (by omega), h2 (m + 1) (by omega), h3 (m + 1) (by omega)]`. Simplify using the standard rewrite rules. Introduce `n hn`. Rewrite using `[coeff_C_mul, h2 n (by omega), mul_zero]`.
-/
theorem coeff_PQ (r : ℕ) : ∀ i, i ≤ r →
    (PQ r E i).1.coeff i = 1 ∧ (∀ n, i < n → (PQ r E i).1.coeff n = 0) ∧
      (∀ n, i ≤ n → (PQ r E i).2.coeff n = 0) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simp [PQ], fun n hn => ?_, fun n _ => by simp [PQ]⟩
    simp [PQ, coeff_one, Nat.pos_iff_ne_zero.mp hn]
  | succ i ih =>
    intro hi
    have h : i < r := hi
    obtain ⟨h1, h2, h3⟩ := ih h.le
    simp only [PQ, dif_pos h]
    refine ⟨?_, ?_, ?_⟩
    · rw [coeff_sub, add_mul, coeff_add, coeff_X_mul, coeff_C_mul, coeff_C_mul, h1,
        h2 (i + 1) (Nat.lt_succ_self i), h3 (i + 1) (Nat.le_succ i)]
      simp
    · intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [coeff_sub, add_mul, coeff_add, coeff_X_mul, coeff_C_mul, coeff_C_mul,
        h2 m (by omega), h2 (m + 1) (by omega), h3 (m + 1) (by omega)]
      simp
    · intro n hn
      rw [coeff_C_mul, h2 n (by omega), mul_zero]

/- English proof (translation)
Rewrite using `[← map_pow, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, Submodule.coe_smul]`.
-/
theorem term (r : ℕ) (c : R r E) (Y : ℂ) (j : ℕ) (f : WSm r E) :
    (((c * algebraMap ℂ (R r E) Y ^ j) f : WSm r E) : (Fin r → ℂ) → E) =
      Y ^ j • ((c f : WSm r E) : (Fin r → ℂ) → E) := by
  rw [← map_pow, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, Submodule.coe_smul]

/- English proof (translation)
Introduce `E _ _ r i hi`. Take `⟨h1, h2, -⟩` from `coeff_PQ (E := E) r i hi`. Use `⟨fun j g => if hg : g ∈ WSm r E then (((PQ r E i).1.coeff j ⟨g, hg⟩ : WSm r E) : (Fin r → ℂ) → E) else 0, ?_⟩` and prove the remaining obligations. Introduce `Y f hf`. Simplify using `only [dif_pos hf]`.

Establish `hdeg : (PQ r E i).1.natDegree < i + 1` using `Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.2 h2)`. Establish `hv` using `(vAB_eval r Y i ⟨f, hf⟩).1`. Rewrite using `[hv, eval_eq_sum_range' hdeg, Finset.sum_range_succ, LinearMap.add_apply, Submodule.coe_add, LinearMap.sum_apply, Submodule.coe_sum, term, h1, add_comm]`. Use `congr 1`. Apply the tactic sequence `all_goals exact Finset.sum_congr rfl fun j _ => term r _ Y j ⟨f, hf⟩`.
-/
theorem capelli_vMonic : VMonic := by
  intro E _ _ r i hi
  obtain ⟨h1, h2, -⟩ := coeff_PQ (E := E) r i hi
  classical
  refine ⟨fun j g => if hg : g ∈ WSm r E then (((PQ r E i).1.coeff j ⟨g, hg⟩ : WSm r E) : (Fin r → ℂ) → E)
    else 0, ?_⟩
  intro Y f hf
  simp only [dif_pos hf]
  have hdeg : (PQ r E i).1.natDegree < i + 1 :=
    Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.2 h2)
  have hv := (vAB_eval r Y i ⟨f, hf⟩).1
  rw [hv, eval_eq_sum_range' hdeg, Finset.sum_range_succ, LinearMap.add_apply, Submodule.coe_add,
    LinearMap.sum_apply, Submodule.coe_sum, term, h1, add_comm]
  congr 1
  all_goals exact Finset.sum_congr rfl fun j _ => term r _ Y j ⟨f, hf⟩

end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
