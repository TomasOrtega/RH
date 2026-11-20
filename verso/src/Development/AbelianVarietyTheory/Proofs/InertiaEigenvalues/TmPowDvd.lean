import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Replace the chosen expression with an arbitrary variable.

Replace the chosen expression with an arbitrary variable. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem tm_pow_dvd : ∀ (l : ℕ) [Fact l.Prime] (x : Fl l), ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ →
    (l : Acris l) ∣ algebraMap (Ainf l) (Acris l) (tm x) ^ l := by
  intro l _ x hx
  have hmem : x.untilt ∈ (Ideal.span {(l : OC l)}) ^ 1 := by
    rw [GlobalTheory.RingBasics.mem_span_pow_OC, pow_one]
    exact hx
  rw [pow_one] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨z, hz⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l c
  have hk := GlobalTheory.MemLoc.FundOnto.dvd_pow_of_ker l (tm x - (l : Ainf l) * tm z) (by
    rw [map_sub, map_mul, map_natCast, GlobalTheory.MemLoc.FundOnto.theta_tm,
      GlobalTheory.MemLoc.FundOnto.theta_tm, hz, ← hc, mul_comm, sub_self])
  rw [map_sub, map_mul, map_natCast] at hk
  generalize algebraMap (Ainf l) (Acris l) (tm x) = X at hk ⊢
  generalize algebraMap (Ainf l) (Acris l) (tm z) = Z at hk
  have h1 : ((l : ℕ) : Acris l) ∣ X - (X - (l : Acris l) * Z) := ⟨Z, by ring⟩
  have h2 := h1.trans (sub_dvd_pow_sub_pow _ _ l)
  have := dvd_add h2 hk
  simpa using this

end GlobalTheory.PSer
