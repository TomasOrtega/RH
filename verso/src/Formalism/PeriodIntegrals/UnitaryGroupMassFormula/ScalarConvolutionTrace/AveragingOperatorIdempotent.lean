import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.CardUNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.SuperdiagSgnConj

open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Unfold `psiNat`. Distinguish the cases in `hz : IsUni k z`. Rewrite using `[if_pos (isUni_mul hz hu), if_pos hz, psiU_mul ψ₀ hz hu]`. Establish `: ¬ IsUni k (z * u)` using `fun h => hz (by simpa using isUni_mul h (isUni_inv hu))`. Rewrite using `[if_neg this, if_neg hz, zero_mul]`.
-/
theorem psiNat_mul_uni (ψ₀ : AddChar F ℂ) (z : GL (Fin k) F) {u : GL (Fin k) F} (hu : IsUni k u) :
    psiNat ψ₀ (z * u) = psiNat ψ₀ z * psiU ψ₀ u := by
  unfold psiNat
  by_cases hz : IsUni k z
  · rw [if_pos (isUni_mul hz hu), if_pos hz, psiU_mul ψ₀ hz hu]
  · have : ¬ IsUni k (z * u) := fun h => hz (by simpa using isUni_mul h (isUni_inv hu))
    rw [if_neg this, if_neg hz, zero_mul]

/- English proof (translation)
Rewrite using `[Finset.sum_mul, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulRight u) _ _ (fun x => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulRight]`. Rewrite using `[smul_mul_assoc, ← map_mul, psiNat_mul_uni ψ₀ x hu, smul_smul]`. Use `congr 1`.

Clear denominators, using `[psiU_ne_zero ψ₀ u]` for the nonvanishing conditions.
-/
theorem sumPsi_mul_pi (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) {u : GL (Fin k) F}
    (hu : IsUni k u) :
    (∑ x : GL (Fin k) F, psiNat ψ₀ x • π x) * π u = (psiU ψ₀ u)⁻¹ • ∑ x : GL (Fin k) F, psiNat ψ₀ x • π x := by
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight u) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulRight]
  rw [smul_mul_assoc, ← map_mul, psiNat_mul_uni ψ₀ x hu, smul_smul]
  congr 1
  field_simp [psiU_ne_zero ψ₀ u]

/- English proof (translation)
Rewrite using `[← Module.End.mul_eq_comp]`. Unfold `projQ`. Rewrite using `[smul_mul_assoc, sumPsi_mul_pi ψ₀ π hu, smul_comm]`.
-/
theorem projQ_comp_pi (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) {u : GL (Fin k) F}
    (hu : IsUni k u) : projQ ψ₀ π ∘ₗ π u = (psiU ψ₀ u)⁻¹ • projQ ψ₀ π := by
  rw [← Module.End.mul_eq_comp]
  unfold projQ
  rw [smul_mul_assoc, sumPsi_mul_pi ψ₀ π hu, smul_comm]

/- English proof (translation)
Rewrite using `[Finset.sum_boole]`. Unfold `cardU`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`.
-/
theorem sum_boole_uni : (∑ x : GL (Fin k) F, if IsUni k x then (1 : ℂ) else 0) = (cardU F k : ℂ) := by
  rw [Finset.sum_boole]
  unfold cardU
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/- English proof (translation)
Introduce `F _ _ k ψ₀ V _ _ π`. Establish `hterm : ∀ x : GL (Fin k) F, projQ ψ₀ π * (psiNat ψ₀ x • π x) = (if IsUni k x then (1 : ℂ) else 0) • projQ ψ₀ π`. Introduce `x`. Distinguish the cases in `hx : IsUni k x`. Rewrite using `[mul_smul_comm, Module.End.mul_eq_comp, projQ_comp_pi ψ₀ π hx, smul_smul, if_pos hx]`.

Use `congr 1`. Unfold `psiNat`. Rewrite using `[if_pos hx]`. Clear denominators, using `[psiU_ne_zero ψ₀ x]` for the nonvanishing conditions. Unfold `psiNat`.

Rewrite using `[if_neg hx, if_neg hx, zero_smul, zero_smul, mul_zero]`. Rewrite using `[← Module.End.mul_eq_comp]`. Use `conv_lhs => rw [show projQ ψ₀ π * projQ ψ₀ π = projQ ψ₀ π * (((cardU F k : ℂ))⁻¹ • ∑ x : GL (Fin k) F, psiNat ψ₀ x • π x) from rfl]`. Rewrite using `[mul_smul_comm, Finset.mul_sum]`. Repeatedly rewrite using `[hterm]`.

Rewrite using `[← Finset.sum_smul, smul_smul, sum_boole_uni, inv_mul_cancel₀ (cardU_ne_zero F k), one_smul]`.
-/
theorem averaging_operator_idempotent : QIdem := by
  intro F _ _ k ψ₀ V _ _ π
  have hterm : ∀ x : GL (Fin k) F, projQ ψ₀ π * (psiNat ψ₀ x • π x) =
      (if IsUni k x then (1 : ℂ) else 0) • projQ ψ₀ π := by
    intro x
    by_cases hx : IsUni k x
    · rw [mul_smul_comm, Module.End.mul_eq_comp, projQ_comp_pi ψ₀ π hx, smul_smul, if_pos hx]
      congr 1
      unfold psiNat; rw [if_pos hx]; field_simp [psiU_ne_zero ψ₀ x]
    · unfold psiNat; rw [if_neg hx, if_neg hx, zero_smul, zero_smul, mul_zero]
  rw [← Module.End.mul_eq_comp]
  conv_lhs => rw [show projQ ψ₀ π * projQ ψ₀ π =
    projQ ψ₀ π * (((cardU F k : ℂ))⁻¹ • ∑ x : GL (Fin k) F, psiNat ψ₀ x • π x) from rfl]
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [hterm]
  rw [← Finset.sum_smul, smul_smul, sum_boole_uni, inv_mul_cancel₀ (cardU_ne_zero F k), one_smul]

/- English proof (translation)
Introduce `V _ _ _ e he`. Establish `h : IsIdempotentElem e` using `he`. Conclude with `((LinearMap.isProj_range_iff_isIdempotentElem e).2 h).trace`.
-/
theorem idempotent_trace_formula : IdemTrace := by
  intro V _ _ _ e he
  have h : IsIdempotentElem e := he
  exact ((LinearMap.isProj_range_iff_isIdempotentElem e).2 h).trace

end PI.GGConvScalarW
