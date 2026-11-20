import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open scoped Pointwise

/- English proof (translation)
Establish `hm : ∀ x, g x ∈ g • A ↔ x ∈ A` using `fun x => ValuationSubring.smul_mem_pointwise_smul_iff`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : σ • g • A = g • A` using `hσ.1 show (g⁻¹ * σ * g) • A = A`. Rewrite using `[mul_smul, mul_smul, h1, inv_smul_smul]`. Establish `h1` using `hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm, ← ValuationSubring.valuation_le_one_iff])`.

Establish `e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q)`. Rewrite using `[map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]`. Rewrite `h1` using `[e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective, ← valuation_lt_one_iff']`. Then use the resulting hypothesis.
-/
private theorem frob_of_smul {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {q : ℕ} {g σ : G E Ω} (hσ : IsFrob (F := E) (g • A) q σ) :
    IsFrob (F := E) A q (g⁻¹ * σ * g) := by
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h1 := hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
      ← ValuationSubring.valuation_le_one_iff])
    have e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q) := by
      rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
      ← valuation_lt_one_iff'] at h1

/- English proof (translation)
Establish `: w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal` using `⟨rfl⟩`. Use `w.isMaximal` as an intermediate fact. Use `(w.under (𝓞 K)).isMaximal` as an intermediate fact. Use `show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)`. Rewrite using `[← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]`.
-/
private theorem normV_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

/- English proof (translation)
The claim follows from `NumberField.HeightOneSpectrum.one_lt_absNorm w`.
-/
private theorem one_lt_normV' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : 1 < normV w :=
  NumberField.HeightOneSpectrum.one_lt_absNorm w

/- English proof (translation)
Use `w.isMaximal` as an intermediate fact. Use `letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _`. Establish `: Finite (𝓞 K ⧸ w.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot`. Use `letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)`. Establish `e : normV w = Fintype.card (𝓞 K ⧸ w.asIdeal)` using `by show Ideal.absNorm w.asIdeal = _`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]`. Rewrite using `[e]`. Assume the negation of the conclusion as `hlt`. Use `FiniteField.X_pow_card_sub_X_ne_zero (𝓞 K ⧸ w.asIdeal) hq (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Use `Ideal.Quotient.eq.2 (h x)` as an intermediate fact. Rewrite `this` using `[map_pow]`. Rewrite using `[eval_sub, eval_pow, eval_X, ← this, sub_self]`. Rewrite using `[FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, Finset.card_univ]`. Conclude with `not_le.1 hlt`.
-/
private theorem normV_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : 1 < q)
    (h : ∀ x : 𝓞 K, x - x ^ q ∈ w.asIdeal) : normV w ≤ q := by
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  have e : normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) := by
    show Ideal.absNorm w.asIdeal = _
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [e]
  by_contra hlt
  refine FiniteField.X_pow_card_sub_X_ne_zero (𝓞 K ⧸ w.asIdeal) hq
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := Ideal.Quotient.eq.2 (h x)
    rw [map_pow] at this
    rw [eval_sub, eval_pow, eval_X, ← this, sub_self]
  · rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, Finset.card_univ]
    exact not_le.1 hlt

/- English proof (translation)
Introduce `F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι δ hδ w hur A' hA'`. Use `⟨hur A' hA', fun σ' hσ' => ?_⟩` and prove the remaining obligations. Establish `: IsAlgClosure F Ω` using `⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Establish `hv : IsPlaceOver A (w.under (𝓞 F))` using `fun x => by`.

Rewrite using `[IsScalarTower.algebraMap_apply F E Ω]`. Conclude with `hA (algebraMap (𝓞 F) (𝓞 E) x)`. Take `⟨g, rfl⟩` from `exists_smul_eq_of_isPlaceOver (F := F) hv hA'`. Establish `hσ` using `frob_of_smul hσ'`. Establish `e : δ σ' = δ (g⁻¹ * σ' * g)`.

Rewrite using `[map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]`. Rewrite using `[map_inv, e]`. Generalize the expression as in `g⁻¹ * σ' * g = σ at hσ`. Use `split_ifs with hq`. Take `⟨φ, hφ⟩` from `exists_isFrob hA`.

Establish `hφ' : IsFrob (F` using `F) A (normV (w.under (𝓞 F))) (res F Ω E φ) := by`. Rewrite using `[← hq]`. Conclude with `⟨hφ.1, hφ.2⟩`. Establish `h1` using `hur A hv _ (inv_mul_mem_Ine_of_isFrob hσ hφ')`. Rewrite `h1` using `[map_mul, (hδ.1 _).2 ⟨φ, rfl⟩, mul_one, map_inv]`.

Rewrite using `[h1]`. Simplify using the standard rewrite rules. Break down `hδ.2 σ with h1 | h1` into its components or cases. It suffices to derive a contradiction. Take `⟨ψ, rfl⟩` from `(hδ.1 σ).1 h1`.

Establish `hle : normV w ≤ normV (w.under (𝓞 F))`. Use `normV_le w (one_lt_normV' _) fun x => ?_` and prove the remaining obligations. Rewrite using `[← hA]`. Establish `hx : A.valuation (algebraMap E Ω x) ≤ 1`. Rewrite using `[A.valuation_le_one_iff]`.

Establish `hi : IsIntegral ℤ (algebraMap E Ω x)` using `x.isIntegral_coe.algebraMap`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))`. Rewrite using `[← hy]`. Conclude with `y.2`. Establish `h2` using `hσ.2 _ hx`.

Establish `h3 : res F Ω E ψ (algebraMap E Ω x) = algebraMap E Ω x` using `ψ.commutes x`. Rewrite `h2` using `[h3]`. Simplify using `using h2`. Use `hq (le_antisymm hle ?_)` and prove the remaining obligations. Establish `h4` using `one_lt_normV' w`.

Rewrite `h4`, the goal using `[normV_under' (K := F) w]`. Use `Nat.le_self_pow (fun h0 => ?_) _` and prove the remaining obligations. Rewrite `h4` using `[h0]`. Simplify using `at h4`. Rewrite using `[h1]`.

Simplify using the standard rewrite rules.
-/
theorem UpperTheory.frobenius_sign_compatibility :
    UpperTheory.V.Af.Bc.SignFrob := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι δ hδ w hur A' hA'
  refine ⟨hur A' hA', fun σ' hσ' => ?_⟩
  have : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  have hv : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hv hA'
  have hσ := frob_of_smul hσ'
  have e : δ σ' = δ (g⁻¹ * σ' * g) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  rw [map_inv, e]
  generalize g⁻¹ * σ' * g = σ at hσ
  split_ifs with hq
  · obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have hφ' : IsFrob (F := F) A (normV (w.under (𝓞 F))) (res F Ω E φ) := by
      rw [← hq]
      exact ⟨hφ.1, hφ.2⟩
    have h1 := hur A hv _ (inv_mul_mem_Ine_of_isFrob hσ hφ')
    rw [map_mul, (hδ.1 _).2 ⟨φ, rfl⟩, mul_one, map_inv] at h1
    rw [h1]; simp
  · rcases hδ.2 σ with h1 | h1
    · exfalso
      obtain ⟨ψ, rfl⟩ := (hδ.1 σ).1 h1
      have hle : normV w ≤ normV (w.under (𝓞 F)) := by
        refine normV_le w (one_lt_normV' _) fun x => ?_
        rw [← hA]
        have hx : A.valuation (algebraMap E Ω x) ≤ 1 := by
          rw [A.valuation_le_one_iff]
          have hi : IsIntegral ℤ (algebraMap E Ω x) := x.isIntegral_coe.algebraMap
          obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))
          rw [← hy]
          exact y.2
        have h2 := hσ.2 _ hx
        have h3 : res F Ω E ψ (algebraMap E Ω x) = algebraMap E Ω x := ψ.commutes x
        rw [h3] at h2
        simpa using h2
      refine hq (le_antisymm hle ?_)
      have h4 := one_lt_normV' w
      rw [normV_under' (K := F) w] at h4 ⊢
      refine Nat.le_self_pow (fun h0 => ?_) _
      rw [h0] at h4
      simp at h4
    · rw [h1]; simp
