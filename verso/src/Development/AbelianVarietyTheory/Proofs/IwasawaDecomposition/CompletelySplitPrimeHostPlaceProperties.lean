import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped Pointwise

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hm : (Ideal.span {(p : ℤ)}).IsMaximal` using `Int.ideal_span_isMaximal_of_prime p`. Use `⟨hm.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Use `show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P`.

Simplify using `using h`.
-/
theorem liesOver_span_of_natCast_mem {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime] (h : ((p : ℕ) : 𝓞 L) ∈ P) :
    P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  refine ⟨hm.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P
  simpa using h

/- English proof (translation)
Rewrite using `[← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h : Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 L)))]`. Use `congr 1`. Use extensionality with `P`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`.

Conclude with `⟨v.isPrime, liesOver_span_of_natCast_mem hp _ hv⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `hm : ((p : ℕ) : 𝓞 L) ∈ P`. Establish `: (p : ℤ) ∈ P.under ℤ` using `by rw [← h2.over]; exact Ideal.mem_span_singleton_self _`. Simplify using `using (show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P from this)`.

Use `⟨⟨P, h1, ?_⟩, hm, rfl⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))`.
-/
theorem ncard_places_eq_primesOver {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}.ncard =
      ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard := by
  rw [← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 L)))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_span_of_natCast_mem hp _ hv⟩
  · rintro ⟨h1, h2⟩
    have hm : ((p : ℕ) : 𝓞 L) ∈ P := by
      have : (p : ℤ) ∈ P.under ℤ := by rw [← h2.over]; exact Ideal.mem_span_singleton_self _
      simpa using (show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P from this)
    refine ⟨⟨P, h1, ?_⟩, hm, rfl⟩
    rintro rfl
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Use `v.isPrime` as an intermediate fact. Use `liesOver_span_of_natCast_mem hp _ hv` as an intermediate fact. Establish `hm : (Ideal.span {(p : ℤ)}).IsMaximal` using `Int.ideal_span_isMaximal_of_prime p`. Establish `h0 : (Ideal.span {(p : ℤ)}) ≠ ⊥` using `by simpa using hp.ne_zero`.

Establish `h1` using `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) (L ≃ₐ[ℚ] L)`. Unfold `SplitsC at hs`. Rewrite `h1` using `[← ncard_places_eq_primesOver hp, hs, IsGalois.card_aut_eq_finrank]`. Establish `h2 : (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 L) * (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 L) = 1` using `(mul_eq_left₀ Module.finrank_pos.ne').1 h1`. Establish `h3` using `Ideal.card_stabilizer_eq (G := L ≃ₐ[ℚ] L) (Ideal.span {(p : ℤ)}) v.asIdeal`.

Rewrite `h3` using `[h2]`. Establish `he` using `Nat.eq_one_of_mul_eq_one_right h2`. Establish `hf` using `Nat.eq_one_of_mul_eq_one_left h2`. Rewrite `he` using `[Ideal.ramificationIdxIn_eq_ramificationIdx _ v.asIdeal (L ≃ₐ[ℚ] L), ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal h0]`. Rewrite `hf` using `[Ideal.inertiaDegIn_eq_inertiaDeg _ v.asIdeal (L ≃ₐ[ℚ] L)]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.pow_inertiaDeg p v.asIdeal, hf, pow_one]`. Introduce `h`. Use `(Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he` and prove the remaining obligations. Simplify `hv` using `[Ideal.map_span]`.

Simplify `h` using `[Ideal.map_span]`. Introduce `σ hσ`. Establish `: (MulAction.stabilizer (L ≃ₐ[ℚ] L) v.asIdeal) = ⊥` using `Subgroup.card_eq_one.1 h3`. Conclude with `Subgroup.mem_bot.1 (this ▸ hσ)`.
-/
theorem splitsC_place [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (hs : SplitsC L p) (v : HeightOneSpectrum (𝓞 L))
    (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 L) ∉ v.asIdeal ^ 2 ∧
      ∀ σ : L ≃ₐ[ℚ] L, σ • v.asIdeal = v.asIdeal → σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have := v.isPrime
  have := liesOver_span_of_natCast_mem hp _ hv
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) (L ≃ₐ[ℚ] L)
  unfold SplitsC at hs
  rw [← ncard_places_eq_primesOver hp, hs, IsGalois.card_aut_eq_finrank] at h1
  have h2 : (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 L) * (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 L) = 1 :=
    (mul_eq_left₀ Module.finrank_pos.ne').1 h1
  have h3 := Ideal.card_stabilizer_eq (G := L ≃ₐ[ℚ] L) (Ideal.span {(p : ℤ)}) v.asIdeal
  rw [h2] at h3
  have he := Nat.eq_one_of_mul_eq_one_right h2
  have hf := Nat.eq_one_of_mul_eq_one_left h2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ v.asIdeal (L ≃ₐ[ℚ] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal h0] at he
  rw [Ideal.inertiaDegIn_eq_inertiaDeg _ v.asIdeal (L ≃ₐ[ℚ] L)] at hf
  refine ⟨?_, ?_, ?_⟩
  · rw [← Ideal.pow_inertiaDeg p v.asIdeal, hf, pow_one]
  · intro h
    refine (Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he
    · simpa [Ideal.map_span] using hv
    · simpa [Ideal.map_span] using h
  · intro σ hσ
    have : (MulAction.stabilizer (L ≃ₐ[ℚ] L) v.asIdeal) = ⊥ := Subgroup.card_eq_one.1 h3
    exact Subgroup.mem_bot.1 (this ▸ hσ)

/- English proof (translation)
Rewrite using `[conjPl_iff_mem]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `y`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`.

Conclude with `h _ _ (σ.apply_symm_apply (y : L)).symm`. Introduce `h x y hxy`. Establish `e : y = σ • x` using `RingOfIntegers.ext hxy`. Rewrite using `[e, ← h, Ideal.smul_mem_pointwise_smul_iff]`.
-/
theorem conjPl_iff_smul (σ : L ≃ₐ[ℚ] L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl σ.toRingEquiv v v' ↔ σ • v.asIdeal = v'.asIdeal := by
  rw [conjPl_iff_mem]
  constructor
  · intro h
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact h _ _ (σ.apply_symm_apply (y : L)).symm
  · intro h x y hxy
    have e : y = σ • x := RingOfIntegers.ext hxy
    rw [e, ← h, Ideal.smul_mem_pointwise_smul_iff]

/- English proof (translation)
Establish `hfix : ∀ x ∈ IntermediateField.adjoin ℚ {b}, σ x = x`. Introduce `x hx`. Establish `: IntermediateField.adjoin ℚ {b} ≤ IntermediateField.fixedField (Subgroup.zpowers σ)`. Rewrite using `[IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]`. Introduce and unpack `_ hτ`.

Establish `: Subgroup.zpowers σ ≤ MulAction.stabilizer _ b` using `(Subgroup.zpowers_le).2 h`. Conclude with `this hτ`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 (this hx) σ (Subgroup.mem_zpowers σ)`. Use extensionality with `a`. Establish `e : σ • algebraMap _ (𝓞 L) a = algebraMap _ (𝓞 L) a` using `RingOfIntegers.ext (hfix _ (a : IntermediateField.adjoin ℚ {b}).2)`.

Rewrite using `[Ideal.mem_under, Ideal.mem_under]`. Use `conv_lhs => rw [← e]`. Rewrite using `[Ideal.smul_mem_pointwise_smul_iff]`.
-/
theorem under_smul_of_fix (b : L) (σ : L ≃ₐ[ℚ] L) (h : σ b = b) (P : Ideal (𝓞 L)) :
    (σ • P).under (𝓞 (IntermediateField.adjoin ℚ {b})) = P.under (𝓞 (IntermediateField.adjoin ℚ {b})) := by
  have hfix : ∀ x ∈ IntermediateField.adjoin ℚ {b}, σ x = x := by
    intro x hx
    have : IntermediateField.adjoin ℚ {b} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      rintro _ hτ
      have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ b := (Subgroup.zpowers_le).2 h
      exact this hτ
    exact (IntermediateField.mem_fixedField_iff _ _).1 (this hx) σ (Subgroup.mem_zpowers σ)
  ext a
  have e : σ • algebraMap _ (𝓞 L) a = algebraMap _ (𝓞 L) a := RingOfIntegers.ext (hfix _ (a : IntermediateField.adjoin ℚ {b}).2)
  rw [Ideal.mem_under, Ideal.mem_under]
  conv_lhs => rw [← e]
  rw [Ideal.smul_mem_pointwise_smul_iff]

/- English proof (translation)
Use `set K := IntermediateField.adjoin ℚ {b} with hK`. Establish `: P'.LiesOver (P.under (𝓞 K))` using `⟨h⟩`. Take `⟨τ, hτ⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup (P.under (𝓞 K)) P P' (L ≃ₐ[K] L)`. Use `⟨τ.restrictScalars ℚ, τ.commutes (⟨b, IntermediateField.mem_adjoin_simple_self ℚ b⟩ : K), ?_⟩` and prove the remaining obligations. Rewrite using `[← hτ]`.

Use extensionality with `y`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Both sides reduce to the same expression.
-/
theorem exists_smul_fix_of_under_eq [IsGalois ℚ L] (b : L) (P P' : Ideal (𝓞 L)) [P.IsPrime] [P'.IsPrime]
    (h : P.under (𝓞 (IntermediateField.adjoin ℚ {b})) = P'.under (𝓞 (IntermediateField.adjoin ℚ {b}))) :
    ∃ σ : L ≃ₐ[ℚ] L, σ b = b ∧ σ • P = P' := by
  set K := IntermediateField.adjoin ℚ {b} with hK
  have : P'.LiesOver (P.under (𝓞 K)) := ⟨h⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.under (𝓞 K)) P P' (L ≃ₐ[K] L)
  refine ⟨τ.restrictScalars ℚ, τ.commutes (⟨b, IntermediateField.mem_adjoin_simple_self ℚ b⟩ : K), ?_⟩
  rw [← hτ]
  ext y
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

/- English proof (translation)
Use `v.isPrime` as an intermediate fact. Use `v'.isPrime` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl h`. Take `⟨σ, hσb, hσ⟩` from `exists_smul_fix_of_under_eq b v.asIdeal v'.asIdeal (congrArg HeightOneSpectrum.asIdeal h).symm`.

Establish `h1 : σ⁻¹ * c = 1` using `(splitsC_place hp hs v hv).2.2 _ (by rw [mul_smul, hvv, ← hσ, inv_smul_smul])`. Rewrite `h1` using `[inv_mul_eq_one]`. Rewrite `hσb` using `[h1, hc]`. Conclude with `hb0 (by linear_combination (-1 / 2 : L) * hσb)`. Introduce `h`.

Use `Q.isPrime` as an intermediate fact. Take `⟨⟨W, hW, hWQ⟩⟩` from `(inferInstance : Nonempty (Q.asIdeal.primesOver (𝓞 L)))`. Establish `hpW : ((p : ℕ) : 𝓞 L) ∈ W`. Rewrite `hQ` using `[hWQ.over, Ideal.mem_under]`. Simplify using `using hQ`.

Use `liesOver_span_of_natCast_mem hp _ hv` as an intermediate fact. Use `liesOver_span_of_natCast_mem hp _ hpW` as an intermediate fact. Take `⟨σ, hσ⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v.asIdeal W (L ≃ₐ[ℚ] L)`. Break down `hb σ with h1 | h1` into its components or cases. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises.

Rewrite using `[hWQ.over, ← hσ, under_smul_of_fix b σ h1]`. Both sides reduce to the same expression. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises.

Establish `h2 : (σ * c⁻¹) b = b`. Establish `: c⁻¹ b = -b`. Establish `h3 : c⁻¹ (c b) = b` using `c.symm_apply_apply b`. Rewrite `h3` using `[hc, map_neg]`. Conclude with `neg_eq_iff_eq_neg.1 h3`.

Rewrite using `[AlgEquiv.mul_apply, this, map_neg, h1, neg_neg]`. Establish `h4 : (σ * c⁻¹) • v'.asIdeal = W` using `by rw [← hvv, mul_smul, inv_smul_smul, hσ]`. Rewrite using `[hWQ.over, ← h4, under_smul_of_fix b _ h2]`. Both sides reduce to the same expression.
-/
theorem under_eq_iff_under_ne [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (hs : SplitsC L p) (b : L) (hb0 : b ≠ 0)
    (hb : ∀ σ : L ≃ₐ[ℚ] L, σ b = b ∨ σ b = -b) (c : L ≃ₐ[ℚ] L) (hc : c b = -b)
    (v v' : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) (hvv : c • v.asIdeal = v'.asIdeal)
    (Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin ℚ {b})))
    (hQ : ((p : ℕ) : 𝓞 (IntermediateField.adjoin ℚ {b})) ∈ Q.asIdeal) :
    v.under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q ↔ v'.under (𝓞 (IntermediateField.adjoin ℚ {b})) ≠ Q := by
  have := v.isPrime
  have := v'.isPrime
  constructor
  · rintro rfl h
    obtain ⟨σ, hσb, hσ⟩ := exists_smul_fix_of_under_eq b v.asIdeal v'.asIdeal
      (congrArg HeightOneSpectrum.asIdeal h).symm
    have h1 : σ⁻¹ * c = 1 := (splitsC_place hp hs v hv).2.2 _ (by rw [mul_smul, hvv, ← hσ, inv_smul_smul])
    rw [inv_mul_eq_one] at h1
    rw [h1, hc] at hσb
    exact hb0 (by linear_combination (-1 / 2 : L) * hσb)
  · intro h
    have := Q.isPrime
    obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty (Q.asIdeal.primesOver (𝓞 L)))
    have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
      rw [hWQ.over, Ideal.mem_under] at hQ
      simpa using hQ
    have := liesOver_span_of_natCast_mem hp _ hv
    have := liesOver_span_of_natCast_mem hp _ hpW
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v.asIdeal W (L ≃ₐ[ℚ] L)
    rcases hb σ with h1 | h1
    · apply HeightOneSpectrum.ext
      rw [hWQ.over, ← hσ, under_smul_of_fix b σ h1]
      rfl
    · exfalso
      apply h
      apply HeightOneSpectrum.ext
      have h2 : (σ * c⁻¹) b = b := by
        have : c⁻¹ b = -b := by
          have h3 : c⁻¹ (c b) = b := c.symm_apply_apply b
          rw [hc, map_neg] at h3
          exact neg_eq_iff_eq_neg.1 h3
        rw [AlgEquiv.mul_apply, this, map_neg, h1, neg_neg]
      have h4 : (σ * c⁻¹) • v'.asIdeal = W := by rw [← hvv, mul_smul, inv_smul_smul, hσ]
      rw [hWQ.over, ← h4, under_smul_of_fix b _ h2]
      rfl

end General

open Classical in

/- English proof (translation)
Introduce `R H p hp hs v hv`. Establish `hG : IsGalois ℚ H.E` using `H.hostE_isGalois`. Establish `hsq` using `H.sqrtMinusD_sq`. Establish `hc` using `H.conj_sqrtMinusD`. Establish `hb0 : H.sqrtMinusD ≠ 0`.

Introduce `h`. Rewrite `hsq` using `[h]`. Establish `: (H.d : H.E) = 0` using `by linear_combination hsq`. Establish `h1 : H.d = 0` using `by exact_mod_cast this`. Use `H.qd_big.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hb : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD`. Introduce `σ`. Apply `sq_eq_sq_iff_eq_or_eq_neg.1` to reduce the goal to its premises. Rewrite using `[← map_pow, hsq, map_neg, map_natCast]`.

Take `⟨h1, h2, h3⟩` from `splitsC_place hp hs v hv`. Use `⟨h1, h2, ?_, fun Q hQ v' hvv => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Unfold `IsSplitPl at hn`. Use `push Not at hn`.

Establish `hle : H.conj • v.asIdeal ≤ v.asIdeal`. Introduce `y hy`. Rewrite `hy` using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Take `⟨z, hz, hzv⟩` from `hn _ hy`. Establish `e : z = y` using `RingOfIntegers.ext (hz.trans (H.conj.apply_symm_apply (y : H.E)))`.

Conclude with `e ▸ hzv`. Take `⟨w, hw, -⟩` from `existsUnique_conjPl H.conj.toRingEquiv v`. Establish `hw'` using `(conjPl_iff_smul H.conj v w).1 hw`. Establish `heq : H.conj • v.asIdeal = v.asIdeal`. Rewrite `hle`, the goal using `[hw']`.

Conclude with `w.isMaximal.eq_of_le v.isPrime.ne_top hle`. Rewrite `hc` using `[h3 _ heq]`. Establish `hc' : H.sqrtMinusD = -H.sqrtMinusD` using `hc`. Conclude with `hb0 (by linear_combination (1 / 2 : H.E) * hc')`. Conclude with `((conjPl_iff_mem _ v v').1 hvv _ _ (by simp)).1 hv`.

Conclude with `under_eq_iff_under_ne hp hs H.sqrtMinusD hb0 hb H.conj hc v v' hv ((conjPl_iff_smul H.conj v v').1 hvv) Q hQ`.
-/
theorem splitsC_main : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → SplitsC H.E p → ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H p v → Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ IsSplitPl H v ∧ ∀ (Q : HeightOneSpectrum (𝓞 H.K)), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal → ∀ v', ConjPl H.conj.toRingEquiv v v' → OverP H p v' ∧ (v.under (𝓞 H.K) = Q ↔ v'.under (𝓞 H.K) ≠ Q) := by
  intro R H p hp hs v hv
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  have hsq := H.sqrtMinusD_sq
  have hc := H.conj_sqrtMinusD
  have hb0 : H.sqrtMinusD ≠ 0 := by
    intro h
    rw [h] at hsq
    have : (H.d : H.E) = 0 := by linear_combination hsq
    have h1 : H.d = 0 := by exact_mod_cast this
    have := H.qd_big.2
    omega
  have hb : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  obtain ⟨h1, h2, h3⟩ := splitsC_place hp hs v hv
  refine ⟨h1, h2, ?_, fun Q hQ v' hvv => ⟨?_, ?_⟩⟩
  · by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    have hle : H.conj • v.asIdeal ≤ v.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hn _ hy
      have e : z = y := RingOfIntegers.ext (hz.trans (H.conj.apply_symm_apply (y : H.E)))
      exact e ▸ hzv
    obtain ⟨w, hw, -⟩ := existsUnique_conjPl H.conj.toRingEquiv v
    have hw' := (conjPl_iff_smul H.conj v w).1 hw
    have heq : H.conj • v.asIdeal = v.asIdeal := by
      rw [hw'] at hle ⊢
      exact w.isMaximal.eq_of_le v.isPrime.ne_top hle
    rw [h3 _ heq] at hc
    have hc' : H.sqrtMinusD = -H.sqrtMinusD := hc
    exact hb0 (by linear_combination (1 / 2 : H.E) * hc')
  · exact ((conjPl_iff_mem _ v v').1 hvv _ _ (by simp)).1 hv
  · exact under_eq_iff_under_ne hp hs H.sqrtMinusD hb0 hb H.conj hc v v' hv ((conjPl_iff_smul H.conj v v').1 hvv) Q hQ

end GlobalTheory.Mem.Chr
