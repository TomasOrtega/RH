import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ Matrix

namespace GlobalTheory.KZ

/- English proof (translation)
Introduce `Ω _ _ _ s E0 S`. Establish `: IsGalois ℚ Ω` using `{}`. Set `K : IntermediateField ℚ Ω` to `IntermediateField.adjoin ℚ (E0 : Set Ω)`. Establish `: FiniteDimensional ℚ K` using `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Establish `hKo : IsOpen (K.fixingSubgroup : Set (G ℚ Ω))` using `IntermediateField.fixingSubgroup_isOpen K`.

Set `V : Set (G ℚ Ω)` to `{φ | s⁻¹ * φ ∈ K.fixingSubgroup}`. Establish `hVo : IsOpen V` using `hKo.preimage (continuous_mul_left s⁻¹)`. Establish `hVne : V.Nonempty` using `⟨s, by simp [V, K.fixingSubgroup.one_mem]⟩`. Set `T : ℕ` to `∏ p ∈ S.filter (· ≠ 0), p`. Establish `hT : T ≠ 0` using `Finset.prod_ne_zero_iff.2 fun p hp => (Finset.mem_filter.1 hp).2`.

Establish `hS : {v : HeightOneSpectrum (𝓞 ℚ) | (T : 𝓞 ℚ) ∈ v.asIdeal}.Finite` using `(Ideal.finite_factors (I := Ideal.span {(T : 𝓞 ℚ)}) (by simpa using hT)).subset fun _ hv => Ideal.dvd_span_singleton.2 hv`. Take `⟨φ, hφV, v, hv, hd, B, hB, hφ⟩` from `(GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS).inter_open_nonempty V hVo hVne`. Establish `h2 : Ideal.absNorm v.asIdeal = normV v`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.

Establish `hmem : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal` using `h2 ▸ Ideal.absNorm_mem v.asIdeal`. Establish `hq : (normV v).Prime`. Rewrite using `[← h2]`. Conclude with `((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified ℚ).1 v).2 hd`. Use `⟨s⁻¹ * φ, normV v, ?_, hq, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Conclude with `(mem_fixingSubgroup_iff _).1 hφV x (IntermediateField.subset_adjoin ℚ _ (by simpa using hx))`. Introduce `hqS`. Apply `hv` to reduce the goal to its premises. Use `show (T : 𝓞 ℚ) ∈ v.asIdeal`.

Establish `hdvd : normV v ∣ T` using `Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hqS, hq.ne_zero⟩)`. Take `⟨k, hk⟩` from `hdvd`. Rewrite using `[hk, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hmem`. Rewrite using `[mul_inv_cancel_left]`.

Establish `hqB : B.valuation ((normV v : ℕ) : Ω) < 1`. Use `(hB ((normV v : ℕ) : 𝓞 ℚ)).2 hmem` as an intermediate fact. Simplify using `using this`. Use `⟨B, (ValuationSubring.mem_nonunits_iff _).2 hqB, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx1 : B.valuation x ≤ 1` using `(B.valuation_le_one_iff x).2 hx`.

Establish `hlt` using `hφ.2 x hx1`. Use `⟨?_, hlt⟩` and prove the remaining obligations. Establish `hxq : x ^ normV v ∈ B` using `pow_mem hx _`. Establish `hd' : φ x - x ^ normV v ∈ B` using `(B.valuation_le_one_iff _).1 hlt.le`. Simplify using `using add_mem hd' hxq`.
-/
theorem exists_fixing_mul_frobAt :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (E0 : Finset Ω) (S : Finset ℕ),
      ∃ (s' : Ω ≃ₐ[ℚ] Ω) (q : ℕ), (∀ x ∈ E0, s' x = x) ∧ q.Prime ∧ q ∉ S ∧ FrobAt q (s * s') := by
  intro Ω _ _ _ s E0 S
  have : IsGalois ℚ Ω := {}
  let K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (E0 : Set Ω)
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hKo : IsOpen (K.fixingSubgroup : Set (G ℚ Ω)) := IntermediateField.fixingSubgroup_isOpen K
  let V : Set (G ℚ Ω) := {φ | s⁻¹ * φ ∈ K.fixingSubgroup}
  have hVo : IsOpen V := hKo.preimage (continuous_mul_left s⁻¹)
  have hVne : V.Nonempty := ⟨s, by simp [V, K.fixingSubgroup.one_mem]⟩
  let T : ℕ := ∏ p ∈ S.filter (· ≠ 0), p
  have hT : T ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (Finset.mem_filter.1 hp).2
  have hS : {v : HeightOneSpectrum (𝓞 ℚ) | (T : 𝓞 ℚ) ∈ v.asIdeal}.Finite :=
    (Ideal.finite_factors (I := Ideal.span {(T : 𝓞 ℚ)}) (by simpa using hT)).subset
      fun _ hv => Ideal.dvd_span_singleton.2 hv
  obtain ⟨φ, hφV, v, hv, hd, B, hB, hφ⟩ :=
    (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS).inter_open_nonempty
      V hVo hVne
  have h2 : Ideal.absNorm v.asIdeal = normV v := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmem : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := h2 ▸ Ideal.absNorm_mem v.asIdeal
  have hq : (normV v).Prime := by
    rw [← h2]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified ℚ).1 v).2 hd
  refine ⟨s⁻¹ * φ, normV v, ?_, hq, ?_, ?_⟩
  · intro x hx
    exact (mem_fixingSubgroup_iff _).1 hφV x (IntermediateField.subset_adjoin ℚ _ (by simpa using hx))
  · intro hqS
    apply hv
    show (T : 𝓞 ℚ) ∈ v.asIdeal
    have hdvd : normV v ∣ T := Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hqS, hq.ne_zero⟩)
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  · rw [mul_inv_cancel_left]
    have hqB : B.valuation ((normV v : ℕ) : Ω) < 1 := by
      have := (hB ((normV v : ℕ) : 𝓞 ℚ)).2 hmem
      simpa using this
    refine ⟨B, (ValuationSubring.mem_nonunits_iff _).2 hqB, fun x hx => ?_⟩
    have hx1 : B.valuation x ≤ 1 := (B.valuation_le_one_iff x).2 hx
    have hlt := hφ.2 x hx1
    refine ⟨?_, hlt⟩
    have hxq : x ^ normV v ∈ B := pow_mem hx _
    have hd' : φ x - x ^ normV v ∈ B := (B.valuation_le_one_iff _).1 hlt.le
    simpa using add_mem hd' hxq

end GlobalTheory.KZ

end
