import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecRankSpecialize.Statement : Prop :=
  ∀ (R K κ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field κ] [Algebra R κ] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Vertical.Par e n → R),
    Function.Surjective (algebraMap R κ) → Module.Finite R (Vertical.SecAlg Q y) →
      Module.finrank K
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) ≤
        Module.finrank κ
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))

/- English proof (translation)
Use `letI : Algebra (PowerSeries ℚ) ℚ := (PowerSeries.constantCoeff (R := ℚ)).toAlgebra`. Use `⟨inferInstance, inferInstance, inferInstance, fun a => ⟨PowerSeries.C a, by simp [RingHom.algebraMap_toAlgebra]⟩, ?_⟩` and prove the remaining obligations. Use `set I := Vertical.secIdeal (⊥ : Ideal (MvPolynomial (Fin 1) (PowerSeries ℚ))) (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))`. Establish `hX : ∀ j : Fin 1, Ideal.Quotient.mk I (X j) = 1`. Introduce `j`.

Rewrite using `[Fin.fin_one_eq_zero j, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Use `Ideal.mem_sup_right (Ideal.subset_span ?_)` and prove the remaining obligations. Simplify using `[Vertical.chartForm, linForm]`. Establish `hrange : ∀ p : MvPolynomial (Fin 1) (PowerSeries ℚ), Ideal.Quotient.mk I p ∈ Set.range (algebraMap (PowerSeries ℚ) (Vertical.SecAlg ⊥ (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))))`. Introduce `p`.

Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨a, rfl⟩`. Consider the case `add p q hp hq`. Take `⟨a, ha⟩` from `hp`. Take `⟨b, hb⟩` from `hq`.

Conclude with `⟨a + b, by rw [map_add, map_add, ha, hb]⟩`. Consider the case `mul_X p j hp`. Take `⟨a, ha⟩` from `hp`. Conclude with `⟨a, by rw [map_mul, hX, mul_one, ha]⟩`. Use `Module.Finite.of_surjective (Algebra.linearMap (PowerSeries ℚ) _) ?_` and prove the remaining obligations.

Introduce `x`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `hrange p`.
-/
theorem SecRankSpecialize.hypotheses_inhabited :
    letI : Algebra (PowerSeries ℚ) ℚ := (PowerSeries.constantCoeff (R := ℚ)).toAlgebra
    IsDomain (PowerSeries ℚ) ∧ IsLocalRing (PowerSeries ℚ) ∧
      IsFractionRing (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) ∧
      Function.Surjective (algebraMap (PowerSeries ℚ) ℚ) ∧
      Module.Finite (PowerSeries ℚ)
        (Vertical.SecAlg (⊥ : Ideal (MvPolynomial (Fin 1) (PowerSeries ℚ)))
          (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))) := by
  letI : Algebra (PowerSeries ℚ) ℚ := (PowerSeries.constantCoeff (R := ℚ)).toAlgebra
  refine ⟨inferInstance, inferInstance, inferInstance,
    fun a => ⟨PowerSeries.C a, by simp [RingHom.algebraMap_toAlgebra]⟩, ?_⟩
  set I := Vertical.secIdeal (⊥ : Ideal (MvPolynomial (Fin 1) (PowerSeries ℚ)))
    (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))
  have hX : ∀ j : Fin 1, Ideal.Quotient.mk I (X j) = 1 := by
    intro j
    rw [Fin.fin_one_eq_zero j, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_sup_right (Ideal.subset_span ?_)
    simp [Vertical.chartForm, linForm]
  have hrange : ∀ p : MvPolynomial (Fin 1) (PowerSeries ℚ),
      Ideal.Quotient.mk I p ∈ Set.range (algebraMap (PowerSeries ℚ) (Vertical.SecAlg ⊥
        (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ)))) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact ⟨a, rfl⟩
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | mul_X p j hp =>
      obtain ⟨a, ha⟩ := hp
      exact ⟨a, by rw [map_mul, hX, mul_one, ha]⟩
  refine Module.Finite.of_surjective (Algebra.linearMap (PowerSeries ℚ) _) ?_
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hrange p

end

end GroundTheory.Heights₂.Heights
