import Mathlib
import Development.EtaleCohomology.EtaleSheaves.BuildCut

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace LateralTheory.E.BuildCut

/- English proof (translation)
Introduce `W _ hW q`. Set `T : Submonoid W` to `{ carrier := {s | IsIdempotentElem s ∧ s ∉ q.asIdeal} one_mem' := ⟨IsIdempotentElem.one, (Ideal.ne_top_iff_one _).mp q.isPrime.ne_top⟩ mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, fun h => (q.isPrime.mem_or_mem h).elim ha.2 hb.2⟩ }`. Use `⟨T, fun s hs => hs, ?_⟩` and prove the remaining obligations. Establish `hT : ∀ s ∈ T, s ∈ q.asIdeal.primeCompl` using `fun s hs => hs.2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨s, hs⟩`. Conclude with `IsLocalization.map_units (Localization.AtPrime q.asIdeal) (⟨s, hT s hs⟩ : q.asIdeal.primeCompl)`. Introduce `z`. Take `⟨⟨x, ⟨s, hs⟩⟩, hz⟩` from `IsLocalization.surj q.asIdeal.primeCompl z`. Take `⟨e, u, he, hu, rfl⟩` from `hW.2 s`.

Establish `he_q : e ∉ q.asIdeal` using `fun h => hs (q.asIdeal.mul_mem_right u h)`. Use `⟨⟨x * ↑hu.unit⁻¹, ⟨e, he, he_q⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only at hz ⊢`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc e, IsUnit.mul_val_inv, mul_one]`.

Use `_ = (z * algebraMap W _ (e * u)) * algebraMap W _ ↑hu.unit⁻¹ := by`. Rewrite using `[map_mul (algebraMap W _) (e * u), mul_assoc]`. Use `_ = algebraMap W _ x * algebraMap W _ ↑hu.unit⁻¹ := by rw [hz]`. Use `_ = algebraMap W _ (x * ↑hu.unit⁻¹) := (map_mul _ _ _).symm`. Introduce `x y hxy`.

Take `⟨⟨c, hc⟩, hcxy⟩` from `(IsLocalization.eq_iff_exists q.asIdeal.primeCompl _).mp hxy`. Take `⟨e, u, he, hu, rfl⟩` from `hW.2 c`. Establish `he_q : e ∉ q.asIdeal` using `fun h => hc (q.asIdeal.mul_mem_right u h)`. Use `⟨⟨e, he, he_q⟩, ?_⟩` and prove the remaining obligations. Simplify using `only at hcxy ⊢`.

Establish `huv : u * ↑hu.unit⁻¹ = 1` using `IsUnit.mul_val_inv hu`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.exists_idempotent_submonoid_isLocalization_atPrime :
    ∀ {W : Type} [CommRing W], ProdACF W → ∀ (q : PrimeSpectrum W),
        ∃ T : Submonoid W, (∀ s ∈ T, IsIdempotentElem s ∧ s ∉ q.asIdeal) ∧ IsLocalization T (Localization.AtPrime q.asIdeal) := by
  intro W _ hW q
  let T : Submonoid W :=
    { carrier := {s | IsIdempotentElem s ∧ s ∉ q.asIdeal}
      one_mem' := ⟨IsIdempotentElem.one, (Ideal.ne_top_iff_one _).mp q.isPrime.ne_top⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨ha.1.mul hb.1, fun h => (q.isPrime.mem_or_mem h).elim ha.2 hb.2⟩ }
  refine ⟨T, fun s hs => hs, ?_⟩
  have hT : ∀ s ∈ T, s ∈ q.asIdeal.primeCompl := fun s hs => hs.2
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact IsLocalization.map_units (Localization.AtPrime q.asIdeal)
      (⟨s, hT s hs⟩ : q.asIdeal.primeCompl)
  · intro z
    obtain ⟨⟨x, ⟨s, hs⟩⟩, hz⟩ := IsLocalization.surj q.asIdeal.primeCompl z
    obtain ⟨e, u, he, hu, rfl⟩ := hW.2 s
    have he_q : e ∉ q.asIdeal := fun h => hs (q.asIdeal.mul_mem_right u h)
    refine ⟨⟨x * ↑hu.unit⁻¹, ⟨e, he, he_q⟩⟩, ?_⟩
    simp only at hz ⊢
    calc z * algebraMap W _ e = z * algebraMap W _ (e * u * ↑hu.unit⁻¹) := by
          rw [mul_assoc e, IsUnit.mul_val_inv, mul_one]
      _ = (z * algebraMap W _ (e * u)) * algebraMap W _ ↑hu.unit⁻¹ := by
          rw [map_mul (algebraMap W _) (e * u), mul_assoc]
      _ = algebraMap W _ x * algebraMap W _ ↑hu.unit⁻¹ := by rw [hz]
      _ = algebraMap W _ (x * ↑hu.unit⁻¹) := (map_mul _ _ _).symm
  · intro x y hxy
    obtain ⟨⟨c, hc⟩, hcxy⟩ := (IsLocalization.eq_iff_exists q.asIdeal.primeCompl _).mp hxy
    obtain ⟨e, u, he, hu, rfl⟩ := hW.2 c
    have he_q : e ∉ q.asIdeal := fun h => hc (q.asIdeal.mul_mem_right u h)
    refine ⟨⟨e, he, he_q⟩, ?_⟩
    simp only at hcxy ⊢
    have huv : u * ↑hu.unit⁻¹ = 1 := IsUnit.mul_val_inv hu
    calc e * x = e * u * x * ↑hu.unit⁻¹ := by linear_combination (-(e * x)) * huv
      _ = e * u * y * ↑hu.unit⁻¹ := by rw [hcxy]
      _ = e * y := by linear_combination (e * y) * huv
