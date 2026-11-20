import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsRationalUnitaryDeterminantMap
import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuNotdvdmuWofunramified
import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuIsRteqoneofsubmem
import Development.AutomorphicArithmetic.FrobeniusLocalisation.splitComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties

open UpperTheory.HF

open NumberField IsDedekindDomain Formalism.HC Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory
open scoped Pointwise

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `hm : (Ideal.span {(p : ℤ)}).IsMaximal` using `Int.ideal_span_isMaximal_of_prime p`. Establish `h1` using `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) (L ≃ₐ[ℚ] L)`. Unfold `SplitsC at hs`.

Rewrite `h1` using `[← ncard_places_eq_primesOver hp, hs, IsGalois.card_aut_eq_finrank]`. Establish `he` using `Nat.eq_one_of_mul_eq_one_right ((mul_eq_left₀ Module.finrank_pos.ne').1 h1)`. Rewrite using `[NumberField.not_dvd_discr_iff_isUnramifiedIn L (𝓞 L) hpZ, Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]`. Introduce `P _ hlo`. Rewrite `he` using `[Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P (L ≃ₐ[ℚ] L)]`. Then use the resulting hypothesis.
-/
private theorem not_dvd_discr_of_splitsC {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] {p : ℕ} (hp : p.Prime)
    (hs : SplitsC L p) : ¬ (p : ℤ) ∣ discr L := by
  have : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) (L ≃ₐ[ℚ] L)
  unfold SplitsC at hs
  rw [← ncard_places_eq_primesOver hp, hs, IsGalois.card_aut_eq_finrank] at h1
  have he := Nat.eq_one_of_mul_eq_one_right ((mul_eq_left₀ Module.finrank_pos.ne').1 h1)
  rw [NumberField.not_dvd_discr_iff_isUnramifiedIn L (𝓞 L) hpZ,
    Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro P _ hlo
  rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P (L ≃ₐ[ℚ] L)] at he

/- English proof (translation)
Unfold `SplitsC at hs`. Conclude with `Set.nonempty_of_ncard_ne_zero (hs ▸ Module.finrank_pos.ne')`.
-/
private theorem exists_place {L : Type} [Field L] [NumberField L] {p : ℕ} (hs : SplitsC L p) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  unfold SplitsC at hs
  exact Set.nonempty_of_ncard_ne_zero (hs ▸ Module.finrank_pos.ne')

/- English proof (translation)
Use `v.isMaximal` as an intermediate fact. Set `` to `Ideal.Quotient.field v.asIdeal`. Establish `: Finite (𝓞 L ⧸ v.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot`. Set `` to `Fintype.ofFinite (𝓞 L ⧸ v.asIdeal)`. Establish `hc : Fintype.card (𝓞 L ⧸ v.asIdeal) = p`.

Rewrite using `[← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]`. Establish `h0 : Ideal.Quotient.mk v.asIdeal x ≠ 0`. Introduce `h`. Establish `h1` using `congrArg (Ideal.Quotient.mk v.asIdeal) hx`. Rewrite `h1` using `[map_pow, h, zero_pow hm, map_one]`.

Conclude with `zero_ne_one h1`. Rewrite using `[← Ideal.Quotient.eq, map_pow, map_one, ← hc]`. Conclude with `FiniteField.pow_card_sub_one_eq_one _ h0`.
-/
private theorem pow_sub_one_mem {L : Type} [Field L] [NumberField L] {p : ℕ} (v : HeightOneSpectrum (𝓞 L))
    (hN : Ideal.absNorm v.asIdeal = p) {x : 𝓞 L} {m : ℕ} (hm : m ≠ 0) (hx : x ^ m = 1) :
    x ^ (p - 1) - 1 ∈ v.asIdeal := by
  have := v.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  have : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  let := Fintype.ofFinite (𝓞 L ⧸ v.asIdeal)
  have hc : Fintype.card (𝓞 L ⧸ v.asIdeal) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have h0 : Ideal.Quotient.mk v.asIdeal x ≠ 0 := by
    intro h
    have h1 := congrArg (Ideal.Quotient.mk v.asIdeal) hx
    rw [map_pow, h, zero_pow hm, map_one] at h1
    exact zero_ne_one h1
  rw [← Ideal.Quotient.eq, map_pow, map_one, ← hc]
  exact FiniteField.pow_card_sub_one_eq_one _ h0

/- English proof (translation)
Introduce `φ H p hp`. Establish `hG : IsGalois ℚ H.E` using `H.galois`. Use `⟨fun h => ?_, fun hs => ?_⟩` and prove the remaining obligations. Unfold `SplitsC`. Rewrite using `[ncard_places_eq_primesOver hp, (UpperTheory.HF.split_complete φ H p hp h).2.2.2.2.2, H.finrank_cmField]`.

Establish `hp2 : p ≠ 2`. Introduce and unpack `rfl`. Conclude with `not_dvd_discr_of_splitsC hp hs (by exact_mod_cast H.der.discr_primes.2.1)`. Take `⟨v₀, hv₀⟩` from `exists_place hs`. Take `⟨hN₀, hu₀, -⟩` from `splitsC_place hp hs v₀ hv₀`.

Establish `hpw : ¬ p ∣ H.w` using `H.not_dvd_muW_of_unramified p hp hp2 v₀.asIdeal v₀.isPrime hv₀ hu₀`. Use `⟨hpw, ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hζ` using `H.muGen_prim`. Set `x : 𝓞 H.E` to `hζ.toInteger`. Establish `hx : (x : H.E) = H.muGen` using `rfl`.

Establish `hxw : x ^ H.w = 1` using `hζ.toInteger_isPrimitiveRoot.pow_eq_one`. Establish `h1 : x ^ (p - 1) = 1`. Use `H.isRt_eq_one_of_sub_mem p hp hpw v₀.asIdeal v₀.isPrime hv₀ _ _ ?_ ?_ (pow_sub_one_mem v₀ hN₀ H.w_pos.ne' hxw)` and prove the remaining obligations. Conclude with `(H.isRt_iff_pow _).2 ⟨p - 1, by rw [← hx]; rfl⟩`. Conclude with `⟨1, one_pos, by simp⟩`.

Conclude with `hζ.toInteger_isPrimitiveRoot.dvd_of_pow_eq_one _ h1`. Establish `hsq` using `H.sqd_sq`. Establish `hc` using `H.conj_sqd`. Establish `hb0` using `H.sqd_ne_zero`. Establish `hb : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ H.sqd = H.sqd ∨ σ H.sqd = -H.sqd`.

Introduce `σ`. Apply `sq_eq_sq_iff_eq_or_eq_neg.1` to reduce the goal to its premises. Rewrite using `[← map_pow, hsq, map_neg, map_natCast]`. Take `⟨h1, h2, h3⟩` from `splitsC_place hp hs v hv`. Establish `hne : H.conj • v.asIdeal ≠ v.asIdeal` using `fun heq => H.conj_ne_one (h3 _ heq)`.

Use `⟨h1, h2, fun h => hne ((conjPl_iff_smul H.conj v v).1 h), ?_, fun Q hQ v' hvv => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn push Not at hn`. Establish `hle : H.conj • v.asIdeal ≤ v.asIdeal`. Introduce `y hy`. Rewrite `hy` using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`.

Take `⟨z, hz, hzv⟩` from `hn _ hy`. Establish `e : z = y` using `RingOfIntegers.ext (hz.trans (H.conj.apply_symm_apply (y : H.E)))`. Conclude with `e ▸ hzv`. Take `⟨w, hw, -⟩` from `existsUnique_conjPl H.conj.toRingEquiv v`. Establish `hw'` using `(conjPl_iff_smul H.conj v w).1 hw`.

Apply `hne` to reduce the goal to its premises. Rewrite `hle`, the goal using `[hw']`. Conclude with `w.isMaximal.eq_of_le v.isPrime.ne_top hle`. Conclude with `((conjPl_iff_mem _ v v').1 hvv _ _ (by simp)).1 hv`. Conclude with `under_eq_iff_under_ne hp hs H.sqd hb0 hb H.conj hc v v' hv ((conjPl_iff_smul H.conj v v').1 hvv) Q hQ`.
-/
theorem UpperTheory.HF.Formalism.HC.HostAx.splitsC_facts :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → (p ≡ 1 [MOD H.condN] → SplitsC H.E p) ∧
      (SplitsC H.E p → ¬ p ∣ H.w ∧ H.w ∣ p - 1 ∧ ∀ v : HeightOneSpectrum (𝓞 H.E), ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal →
        Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ ¬ ConjPl H.conj.toRingEquiv v v ∧
        (∃ x : 𝓞 H.E, x ∈ v.asIdeal ∧ ∀ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y ∉ v.asIdeal) ∧
        ∀ Q : HeightOneSpectrum (𝓞 H.K), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal → ∀ v', ConjPl H.conj.toRingEquiv v v' →
          ((p : ℕ) : 𝓞 H.E) ∈ v'.asIdeal ∧ (v.under (𝓞 H.K) = Q ↔ v'.under (𝓞 H.K) ≠ Q)) := by
  intro φ H p hp
  have hG : IsGalois ℚ H.E := H.galois
  refine ⟨fun h => ?_, fun hs => ?_⟩
  · unfold SplitsC
    rw [ncard_places_eq_primesOver hp, (UpperTheory.HF.split_complete φ H p hp h).2.2.2.2.2, H.finrank_cmField]
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact not_dvd_discr_of_splitsC hp hs (by exact_mod_cast H.der.discr_primes.2.1)
  obtain ⟨v₀, hv₀⟩ := exists_place hs
  obtain ⟨hN₀, hu₀, -⟩ := splitsC_place hp hs v₀ hv₀
  have hpw : ¬ p ∣ H.w := H.not_dvd_muW_of_unramified p hp hp2 v₀.asIdeal v₀.isPrime hv₀ hu₀
  refine ⟨hpw, ?_, fun v hv => ?_⟩
  · have hζ := H.muGen_prim
    let x : 𝓞 H.E := hζ.toInteger
    have hx : (x : H.E) = H.muGen := rfl
    have hxw : x ^ H.w = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
    have h1 : x ^ (p - 1) = 1 := by
      refine H.isRt_eq_one_of_sub_mem p hp hpw v₀.asIdeal v₀.isPrime hv₀ _ _ ?_ ?_
        (pow_sub_one_mem v₀ hN₀ H.w_pos.ne' hxw)
      · exact (H.isRt_iff_pow _).2 ⟨p - 1, by rw [← hx]; rfl⟩
      · exact ⟨1, one_pos, by simp⟩
    exact hζ.toInteger_isPrimitiveRoot.dvd_of_pow_eq_one _ h1
  have hsq := H.sqd_sq
  have hc := H.conj_sqd
  have hb0 := H.sqd_ne_zero
  have hb : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ H.sqd = H.sqd ∨ σ H.sqd = -H.sqd := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  obtain ⟨h1, h2, h3⟩ := splitsC_place hp hs v hv
  have hne : H.conj • v.asIdeal ≠ v.asIdeal := fun heq => H.conj_ne_one (h3 _ heq)
  refine ⟨h1, h2, fun h => hne ((conjPl_iff_smul H.conj v v).1 h), ?_, fun Q hQ v' hvv => ⟨?_, ?_⟩⟩
  · by_contra hn
    push Not at hn
    have hle : H.conj • v.asIdeal ≤ v.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hn _ hy
      have e : z = y := RingOfIntegers.ext (hz.trans (H.conj.apply_symm_apply (y : H.E)))
      exact e ▸ hzv
    obtain ⟨w, hw, -⟩ := existsUnique_conjPl H.conj.toRingEquiv v
    have hw' := (conjPl_iff_smul H.conj v w).1 hw
    apply hne
    rw [hw'] at hle ⊢
    exact w.isMaximal.eq_of_le v.isPrime.ne_top hle
  · exact ((conjPl_iff_mem _ v v').1 hvv _ _ (by simp)).1 hv
  · exact under_eq_iff_under_ne hp hs H.sqd hb0 hb H.conj hc v v' hv ((conjPl_iff_smul H.conj v v').1 hvv) Q hQ
