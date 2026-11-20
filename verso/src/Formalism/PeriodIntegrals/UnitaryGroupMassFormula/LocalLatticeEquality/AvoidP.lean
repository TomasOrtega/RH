import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Development

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig p A d hd`. Establish `hv1 : p.valuation F (algebraMap (𝓞 F) F d) = 1` using `(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) p).2 hd`. Establish `h1 : A.ιF (algebraMap (𝓞 F) F d) ≤ᵥ A.ιF 1` using `(A.val _ _).2 (by rw [hv1, map_one])`. Establish `h2 : A.ιF 1 ≤ᵥ A.ιF (algebraMap (𝓞 F) F d)` using `(A.val _ _).2 (by rw [hv1, map_one])`. Rewrite `h1`, `h2` using `[map_one]`.

Establish `hcv : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F d)) = 1` using `le_antisymm ((Valuation.vle_one_iff _).1 h1) ((Valuation.one_vle_iff _).1 h2)`. Establish `hc0 : A.ιF (algebraMap (𝓞 F) F d) ≠ 0`. Introduce `h`. Rewrite `hcv` using `[h, map_zero]`. Conclude with `zero_ne_one hcv`.

Establish `hinv : (A.ιF (algebraMap (𝓞 F) F d))⁻¹ ∈ 𝒪[A.Fp]`. Rewrite using `[Valuation.mem_integer_iff, map_inv₀, hcv, inv_one]`. Use `⟨algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[A.O_def]`. Establish `hu : algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹ = algebraMap 𝒪[A.Fp] A.Ep ⟨_, hinv⟩` using `rfl`.

Rewrite using `[hu]`. Conclude with `isIntegral_algebraMap`. Establish `hd' : A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) = algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))`. Rewrite using `[← A.compat]`. Both sides reduce to the same expression.

Rewrite using `[hd', ← map_mul, inv_mul_cancel₀ hc0, map_one]`.
-/
theorem unitP : UnitP := by
  intro F E _ _ _ _ _ sig p A d hd
  have hv1 : p.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) p).2 hd
  have h1 : A.ιF (algebraMap (𝓞 F) F d) ≤ᵥ A.ιF 1 := (A.val _ _).2 (by rw [hv1, map_one])
  have h2 : A.ιF 1 ≤ᵥ A.ιF (algebraMap (𝓞 F) F d) := (A.val _ _).2 (by rw [hv1, map_one])
  rw [map_one] at h1 h2
  have hcv : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F d)) = 1 :=
    le_antisymm ((Valuation.vle_one_iff _).1 h1) ((Valuation.one_vle_iff _).1 h2)
  have hc0 : A.ιF (algebraMap (𝓞 F) F d) ≠ 0 := by
    intro h
    rw [h, map_zero] at hcv
    exact zero_ne_one hcv
  have hinv : (A.ιF (algebraMap (𝓞 F) F d))⁻¹ ∈ 𝒪[A.Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, hcv, inv_one]
  refine ⟨algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹, ?_, ?_⟩
  · rw [A.O_def]
    have hu : algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹ =
        algebraMap 𝒪[A.Fp] A.Ep ⟨_, hinv⟩ := rfl
    rw [hu]
    exact isIntegral_algebraMap
  · have hd' : A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) =
        algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d)) := by
      rw [← A.compat]
      rfl
    rw [hd', ← map_mul, inv_mul_cancel₀ hc0, map_one]

/- English proof (translation)
Introduce `F E _ _ _ _ _ p I hI`. Assume the negation of the conclusion as `hne`. Simplify using `only [not_exists, not_and] at hne`. Establish `hle : I.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ p.asIdeal`. Introduce `d hd`.

Assume the negation of the conclusion as `hdp`. Conclude with `hne d hdp hd`. Take `⟨Q, hIQ, hQ, hQp⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal I hle`. Establish `hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E))`. Introduce `a b hab`.

Establish `hE : algebraMap F E (a : F) = algebraMap F E (b : F)` using `congrArg (fun x : 𝓞 E => (x : E)) hab`. Conclude with `Subtype.ext ((algebraMap F E).injective hE)`. Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Apply `p.ne_bot` to reduce the goal to its premises.

Rewrite using `[← hQp, Ideal.comap_bot_of_injective _ hinj]`. Conclude with `hI ⟨Q, hQ, hQ0⟩ hQp hIQ`.
-/
theorem avoidP : AvoidP := by
  intro F E _ _ _ _ _ p I hI
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hle : I.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ p.asIdeal := by
    intro d hd
    by_contra hdp
    exact hne d hdp hd
  obtain ⟨Q, hIQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal I hle
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := by
    intro a b hab
    have hE : algebraMap F E (a : F) = algebraMap F E (b : F) := congrArg (fun x : 𝓞 E => (x : E)) hab
    exact Subtype.ext ((algebraMap F E).injective hE)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply p.ne_bot
    rw [← hQp, Ideal.comap_bot_of_injective _ hinj]
  exact hI ⟨Q, hQ, hQ0⟩ hQp hIQ

end PI.LocLatEq.W
