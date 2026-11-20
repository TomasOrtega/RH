import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqPowMulUnit
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit`. Consider the case `exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit`. Consider the case `(apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit ..)`.
-/
theorem unit_mul_pow_of_maximalIdeal_eq_span {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hm : maximalIdeal S = Ideal.span {π}) {x : S} (hx : x ≠ 0) :
    ∃ (k : ℕ) (u : S), IsUnit u ∧ x = π ^ k * u := by
  first
  | exact @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit
  | exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit
  | (apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit ..)

/- English proof (translation)
Establish `hpow : ∀ (k : ℕ) (a : S), π ^ k * a = 0 → a = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro a h`. Simplify using `using h`.

Consider the case `succ k ih => intro a h; exact ih a (hreg _ (by rw [← h, pow_succ]; ring))`. Establish `hnzd : NoZeroDivisors S`. Use `⟨fun {x y} hxy => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Take `⟨a, u, hu, rfl⟩` from `unit_mul_pow_of_maximalIdeal_eq_span hm h.1`. Take `⟨b, v, hv, rfl⟩` from `unit_mul_pow_of_maximalIdeal_eq_span hm h.2`. Establish `: π ^ (a + b) * (u * v) = 0` using `by rw [← hxy, pow_add]; ring`. Conclude with `(hu.mul hv).ne_zero (hpow _ _ this)`. Use `haveI : IsDomain S := NoZeroDivisors.to_isDomain S`.

Establish `hπ0 : π ≠ 0` using `fun h => one_ne_zero (hreg 1 (by rw [h, zero_mul]))`. Establish `hnf : ¬ IsField S`. Rewrite using `[isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]`. Conclude with `hπ0`. Establish `hpr : (maximalIdeal S).IsPrincipal` using `⟨⟨π, hm⟩⟩`.

Establish `hdvr : IsDiscreteValuationRing S` using `((IsDiscreteValuationRing.TFAE S hnf).out 0 4).2 hpr`. Conclude with `⟨inferInstance, hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hm⟩`.
-/
theorem dvr_of_maximalIdeal_eq_span {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hm : maximalIdeal S = Ideal.span {π}) (hreg : ∀ a : S, π * a = 0 → a = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  have hpow : ∀ (k : ℕ) (a : S), π ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a h; simpa using h
    | succ k ih => intro a h; exact ih a (hreg _ (by rw [← h, pow_succ]; ring))
  have hnzd : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨a, u, hu, rfl⟩ := unit_mul_pow_of_maximalIdeal_eq_span hm h.1
    obtain ⟨b, v, hv, rfl⟩ := unit_mul_pow_of_maximalIdeal_eq_span hm h.2
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy, pow_add]; ring
    exact (hu.mul hv).ne_zero (hpow _ _ this)
  haveI : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := fun h => one_ne_zero (hreg 1 (by rw [h, zero_mul]))
  have hnf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]
    exact hπ0
  have hpr : (maximalIdeal S).IsPrincipal := ⟨⟨π, hm⟩⟩
  have hdvr : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnf).out 0 4).2 hpr
  exact ⟨inferInstance, hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hm⟩

end GlobalTheory.Pat
