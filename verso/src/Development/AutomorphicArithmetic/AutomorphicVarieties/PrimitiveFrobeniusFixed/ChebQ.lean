import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Introduce `Ω _ _ _ V hV hne T hT`. Set `S : Set (HeightOneSpectrum (𝓞 ℚ))` to `{v | v.asIdeal ∣ Ideal.span {(T : 𝓞 ℚ)}}`. Establish `hS : S.Finite` using `Ideal.finite_factors (by`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hT)` after adjusting the coercions.

Establish `hD` using `GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS`. Take `⟨φ, hφV, v, hvS, hv1, B, hB, hF⟩` from `hD.inter_open_nonempty V hV hne`. Establish `hq : normV v = Ideal.absNorm v.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.

Establish `hprime : (normV v).Prime`. Rewrite using `[hq]`. Conclude with `((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified ℚ).1 v).2 hv1`. Establish `hmem : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal`. Rewrite using `[hq]`.

Conclude with `Ideal.absNorm_mem _`. Use `⟨normV v, B, φ, hprime, ?_, ?_, hF, hφV⟩` and prove the remaining obligations. Introduce `hdvd`. Apply `hvS` to reduce the goal to its premises. Use `show v.asIdeal ∣ Ideal.span {(T : 𝓞 ℚ)}`.

Rewrite using `[Ideal.dvd_span_singleton]`. Take `⟨c, hc⟩` from `hdvd`. Rewrite using `[hc, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hmem`. Use `show B.valuation ((normV v : ℕ) : Ω) < 1`.

Use `(hB ((normV v : ℕ) : 𝓞 ℚ)).2 hmem` as an intermediate fact. Simplify using `using this`.
-/
theorem UpperTheory.V.ML.chebQ :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Set (G ℚ Ω)), IsOpen V → V.Nonempty → ∀ T : ℕ, T ≠ 0 → ∃ (q : ℕ) (A : ValuationSubring Ω) (φ : G ℚ Ω), q.Prime ∧ ¬ q ∣ T ∧ Over A q ∧ IsFrob (F := ℚ) A q φ ∧ φ ∈ V := by
  intro Ω _ _ _ V hV hne T hT
  let S : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | v.asIdeal ∣ Ideal.span {(T : 𝓞 ℚ)}}
  have hS : S.Finite := Ideal.finite_factors (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hT)
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  obtain ⟨φ, hφV, v, hvS, hv1, B, hB, hF⟩ := hD.inter_open_nonempty V hV hne
  have hq : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hprime : (normV v).Prime := by
    rw [hq]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified ℚ).1 v).2 hv1
  have hmem : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [hq]
    exact Ideal.absNorm_mem _
  refine ⟨normV v, B, φ, hprime, ?_, ?_, hF, hφV⟩
  · intro hdvd
    apply hvS
    show v.asIdeal ∣ Ideal.span {(T : 𝓞 ℚ)}
    rw [Ideal.dvd_span_singleton]
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  · show B.valuation ((normV v : ℕ) : Ω) < 1
    have := (hB ((normV v : ℕ) : 𝓞 ℚ)).2 hmem
    simpa using this
