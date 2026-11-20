import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.IsIntegralAtSuperdiagonalSum

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwChrOne.Pf

/- English proof (translation)
Introduce `E K _ _ _ _ P psi ξ kj N c hpsi`. Establish `memJ : ∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) (1 : Sp E (N + c) ≃ₗ[E] Sp E (N + c)), r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c`. Introduce `r hr`. Unfold `Loc.Cbe at hr`. Establish `h2` using `(Subgroup.mem_inf.mp hr).2`.

Rewrite `h2` using `[Subgroup.mem_comap]`. Simplify using `using h2`. Establish `chi_eq : ∀ r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c, ChiL P psi ξ kj N c 1 r = (LocE.unitV ξ (Ment kj N c r).det)⁻¹`. Introduce `r hr`. Unfold `ChiL`.

Rewrite using `[hpsi _ (isIntegralAt_superdiagonalSum P (hI_of P hr)), inv_one, one_mul, inv_one, one_mul, mul_one]`. Both sides reduce to the same expression. Establish `unit_of : ∀ r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c, IsUnit (redP P (Ment kj N c r).det)`. Introduce `r hr`. Rewrite using `[redP_det_Ment P (hI_of P hr)]`.

Conclude with `isUnit_Mb P hr`. Use `⟨fun r hr => ?_, fun r hr r' hr' r'' hr'' hx => ?_⟩` and prove the remaining obligations. Establish `hJ` using `memJ r hr`. Rewrite using `[chi_eq r hJ]`. Use `inv_ne_zero ?_` and prove the remaining obligations.

Unfold `LocE.unitV`. Rewrite using `[dif_pos (unit_of r hJ)]`. Conclude with `Units.ne_zero _`. Establish `hJ` using `memJ r hr`. Establish `hJ'` using `memJ r' hr'`.

Establish `hJ''` using `memJ r'' hr''`. Rewrite using `[chi_eq r hJ, chi_eq r' hJ', chi_eq r'' hJ'', ← mul_inv]`. Use `congr 1`. Apply `unitV_mul P ξ (unit_of r hJ) (unit_of r' hJ')` to reduce the goal to its premises. Rewrite using `[redP_det_Ment P (hI_of P hJ''), redP_det_Ment P (hI_of P hJ), redP_det_Ment P (hI_of P hJ'), ← Matrix.det_mul]`.

Use `congr 1`. Apply `Mb_mul_of P (fun i hi1 hi2 j hj => red_DA P hJ i hi1 hi2 j hj) (hI_of P hJ) (hI_of P hJ')` to reduce the goal to its premises. Introduce `t`. Establish `ht : kj + t.1 < N` using `by have := t.isLt; omega`. Use `hx (Loc.eN E N (kj + t.1))` as an intermediate fact.

Rewrite `this` using `[inX_eN ht]`. Then use the resulting hypothesis.
-/
theorem twChrOne_main : PI.TwChrOne.TwChrOne := by
  intro E K _ _ _ _ P psi ξ kj N c hpsi

  have memJ : ∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c)
      (1 : Sp E (N + c) ≃ₗ[E] Sp E (N + c)), r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c := by
    intro r hr
    unfold Loc.Cbe at hr
    have h2 := (Subgroup.mem_inf.mp hr).2
    rw [Subgroup.mem_comap] at h2
    simpa using h2

  have chi_eq : ∀ r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c,
      ChiL P psi ξ kj N c 1 r = (LocE.unitV ξ (Ment kj N c r).det)⁻¹ := by
    intro r hr
    unfold ChiL
    rw [hpsi _ (isIntegralAt_superdiagonalSum P (hI_of P hr)), inv_one, one_mul, inv_one, one_mul, mul_one]
    rfl
  have unit_of : ∀ r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c,
      IsUnit (redP P (Ment kj N c r).det) := by
    intro r hr
    rw [redP_det_Ment P (hI_of P hr)]
    exact isUnit_Mb P hr
  refine ⟨fun r hr => ?_, fun r hr r' hr' r'' hr'' hx => ?_⟩
  · have hJ := memJ r hr
    rw [chi_eq r hJ]
    refine inv_ne_zero ?_
    unfold LocE.unitV
    rw [dif_pos (unit_of r hJ)]
    exact Units.ne_zero _
  · have hJ := memJ r hr
    have hJ' := memJ r' hr'
    have hJ'' := memJ r'' hr''
    rw [chi_eq r hJ, chi_eq r' hJ', chi_eq r'' hJ'', ← mul_inv]
    congr 1
    apply unitV_mul P ξ (unit_of r hJ) (unit_of r' hJ')
    rw [redP_det_Ment P (hI_of P hJ''), redP_det_Ment P (hI_of P hJ), redP_det_Ment P (hI_of P hJ'),
      ← Matrix.det_mul]
    congr 1
    apply Mb_mul_of P (fun i hi1 hi2 j hj => red_DA P hJ i hi1 hi2 j hj) (hI_of P hJ) (hI_of P hJ')
    intro t
    have ht : kj + t.1 < N := by have := t.isLt; omega
    have := hx (Loc.eN E N (kj + t.1))
    rwa [inX_eN ht] at this

end PI.TwChrOne.Pf
