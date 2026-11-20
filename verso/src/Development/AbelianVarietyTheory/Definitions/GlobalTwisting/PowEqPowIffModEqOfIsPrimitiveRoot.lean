import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers

noncomputable section
namespace GlobalTheory.NT.Model
open NumberField IsDedekindDomain GlobalTheory.NT

/- English proof (translation)
Use `⟨p.asIdeal, p.isPrime, ⟨(Ideal.comap_id p.asIdeal).symm⟩, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul, ← Ideal.Quotient.eq, map_pow]`. Use `p.isMaximal` as an intermediate fact. Establish `: Finite (𝓞 K ⧸ p.asIdeal)` using `Ring.HasFiniteQuotients.finiteQuotient p.ne_bot`. Use `letI := Fintype.ofFinite (𝓞 K ⧸ p.asIdeal)`.

Use `letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _`. Establish `hN : Ideal.absNorm p.asIdeal = Fintype.card (𝓞 K ⧸ p.asIdeal)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]`. Rewrite using `[hN, FiniteField.pow_card]`.
-/
theorem isFrob_one {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) : IsFrob K p 1 := by
  refine ⟨p.asIdeal, p.isPrime, ⟨(Ideal.comap_id p.asIdeal).symm⟩, fun x => ?_⟩
  rw [one_smul, ← Ideal.Quotient.eq, map_pow]
  have := p.isMaximal
  have : Finite (𝓞 K ⧸ p.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ p.asIdeal)
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  have hN : Ideal.absNorm p.asIdeal = Fintype.card (𝓞 K ⧸ p.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [hN, FiniteField.pow_card]

/- English proof (translation)
Unfold `heckeVal`. Rewrite using `[dif_pos ⟨fun _ _ => rfl, ⟨1, isFrob_one p⟩⟩]`. Simplify using the standard rewrite rules.
-/
theorem heckeVal_one {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) :
    heckeVal K (1 : (K ≃ₐ[K] K) →* ℂˣ) p = 1 := by
  unfold heckeVal
  rw [dif_pos ⟨fun _ _ => rfl, ⟨1, isFrob_one p⟩⟩]
  simp

/- English proof (translation)
Establish `h1 : p.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator p : ℕ) : 𝓞 ℚ)}`. Establish `h2` using `congrArg (Ideal.comap (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))) (Rat.HeightOneSpectrum.span_natGenerator p)`. Rewrite `h2` using `[Ideal.comap_map_of_bijective _ (RingEquiv.bijective _)]`. Rewrite using `[← h2, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]`. Simplify using the standard rewrite rules.

Rewrite using `[h1, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]`. Both sides reduce to the same expression.
-/
theorem absNorm_eq (p : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm p.asIdeal = (Rat.HeightOneSpectrum.primesEquiv p : ℕ) := by
  have h1 : p.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator p : ℕ) : 𝓞 ℚ)} := by
    have h2 := congrArg (Ideal.comap (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)))
      (Rat.HeightOneSpectrum.span_natGenerator p)
    rw [Ideal.comap_map_of_bijective _ (RingEquiv.bijective _)] at h2
    rw [← h2, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
    simp
  rw [h1, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  rfl

/- English proof (translation)
Establish `h` using `riemannZeta_eulerProduct_hasProd hs`. Rewrite `h` using `[← (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).hasProd_iff]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `𝔭`. Simplify using `only [Function.comp_apply, heckeVal_one, one_mul, absNorm_eq]`.
-/
theorem zeta_prod (s : ℂ) (hs : 1 < s.re) : HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 ℚ) =>
      (1 - heckeVal ℚ (1 : (ℚ ≃ₐ[ℚ] ℚ) →* ℂˣ) 𝔭 * ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (riemannZeta s) := by
  have h := riemannZeta_eulerProduct_hasProd hs
  rw [← (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).hasProd_iff] at h
  convert h using 1
  funext 𝔭
  simp only [Function.comp_apply, heckeVal_one, one_mul, absNorm_eq]

/- English proof (translation)
The claim follows from `AlgEquiv.ext fun x => by simpa using σ.commutes x`.
-/
private theorem algEquiv_self_eq_one {K : Type} [Field K] (σ : K ≃ₐ[K] K) : σ = 1 :=
  AlgEquiv.ext fun x => by simpa using σ.commutes x

/- English proof (translation)
Establish `hχ : χ = 1` using `MonoidHom.ext fun σ => by rw [algEquiv_self_eq_one σ, map_one, MonoidHom.one_apply]`. Substitute `hχ` using the available equality. Conclude with `heckeVal_one p`.
-/
private theorem heckeVal_self_eq_one {K : Type} [Field K] [NumberField K] (χ : (K ≃ₐ[K] K) →* ℂˣ)
    (p : HeightOneSpectrum (𝓞 K)) : heckeVal K χ p = 1 := by
  have hχ : χ = 1 := MonoidHom.ext fun σ => by rw [algEquiv_self_eq_one σ, map_one, MonoidHom.one_apply]
  subst hχ
  exact heckeVal_one p

/- English proof (translation)
Unfold `heckeIdeal`. Simplify using `[heckeVal_self_eq_one]`.
-/
private theorem heckeIdeal_self_eq_one {K : Type} [Field K] [NumberField K] (χ : (K ≃ₐ[K] K) →* ℂˣ)
    (I : Ideal (𝓞 K)) : heckeIdeal K χ I = 1 := by
  unfold heckeIdeal
  simp [heckeVal_self_eq_one]

/- English proof (translation)
Establish `hmod : IsModulus K χ ⊤`. Unfold `IsModulus`. Use `⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β _ => ?_⟩` and prove the remaining obligations. Rewrite using `[heckeVal_self_eq_one]`. Conclude with `one_ne_zero`.

Rewrite using `[heckeIdeal_self_eq_one, heckeIdeal_self_eq_one]`. Unfold `condNorm`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Nat.sInf_le ⟨⊤, hmod, Ideal.absNorm_top⟩`. Use `le_csInf ⟨1, ⊤, hmod, Ideal.absNorm_top⟩ ?_` and prove the remaining obligations.

Introduce and unpack `n ⟨𝔪, h𝔪, rfl⟩`. Unfold `IsModulus at h𝔪`. Conclude with `Nat.one_le_iff_ne_zero.mpr fun h0 => h𝔪.1 (Ideal.absNorm_eq_zero_iff.mp h0)`.
-/
theorem condNorm_one {K : Type} [Field K] [NumberField K] (χ : (K ≃ₐ[K] K) →* ℂˣ) : condNorm K χ = 1 := by
  have hmod : IsModulus K χ ⊤ := by
    unfold IsModulus
    refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β _ => ?_⟩
    · rw [heckeVal_self_eq_one]
      exact one_ne_zero
    · rw [heckeIdeal_self_eq_one, heckeIdeal_self_eq_one]
  unfold condNorm
  apply le_antisymm
  · exact Nat.sInf_le ⟨⊤, hmod, Ideal.absNorm_top⟩
  · refine le_csInf ⟨1, ⊤, hmod, Ideal.absNorm_top⟩ ?_
    rintro n ⟨𝔪, h𝔪, rfl⟩
    unfold IsModulus at h𝔪
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => h𝔪.1 (Ideal.absNorm_eq_zero_iff.mp h0)

/- English proof (translation)
Unfold `bigQ`. Simplify using `[condNorm_one]`.
-/
theorem bigQ_rat : bigQ ℚ ℚ = 1 := by
  unfold bigQ
  simp [condNorm_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨-1, 1, by norm_num⟩`.
-/
example : NormOne 7 1 2 := ⟨-1, 1, by norm_num⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨-1, 1, by norm_num⟩`.
-/
example : NormOne 7 2 7 := ⟨-1, 1, by norm_num⟩

/- English proof (translation)
Establish `hfin : IsOfFinOrder ζ` using `isOfFinOrder_iff_pow_eq_one.2 ⟨m, NeZero.pos m, h.pow_eq_one⟩`. Rewrite using `[h.eq_orderOf]`. Conclude with `hfin.pow_eq_pow_iff_modEq`.
-/
theorem pow_eq_pow_iff_modEq_of_isPrimitiveRoot {R : Type} [CommRing R] [IsDomain R] {ζ : R} {m : ℕ} [NeZero m] (h : IsPrimitiveRoot ζ m)
    {a b : ℕ} : ζ ^ a = ζ ^ b ↔ a ≡ b [MOD m] := by
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨m, NeZero.pos m, h.pow_eq_one⟩
  rw [h.eq_orderOf]
  exact hfin.pow_eq_pow_iff_modEq

/- English proof (translation)
Use `(Ideal.finite_factors hI).subset fun 𝔭 h => ?_` and prove the remaining obligations. Simplify using `only [Function.mem_mulSupport] at h`. Establish `h0 : (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors ≠ 0` using `fun h0 => h (by rw [h0, pow_zero])`. Conclude with `(Associates.count_ne_zero_iff_dvd hI 𝔭.irreducible).mp h0`.
-/
private theorem mulSupport_heckeVal_pow_count_finite {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : (L ≃ₐ[K] L) →* ℂˣ) {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    (Function.mulSupport fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
      heckeVal L χ 𝔭 ^ (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors).Finite := by
  refine (Ideal.finite_factors hI).subset fun 𝔭 h => ?_
  simp only [Function.mem_mulSupport] at h
  have h0 : (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors ≠ 0 := fun h0 => h (by rw [h0, pow_zero])
  exact (Associates.count_ne_zero_iff_dvd hI 𝔭.irreducible).mp h0

section Cyc
open IsCyclotomicExtension.Rat

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Unfold `heckeIdeal`. Rewrite using `[← finprod_mul_distrib (mulSupport_heckeVal_pow_count_finite L χ hI) (mulSupport_heckeVal_pow_count_finite L χ hJ)]`. Use `finprod_congr fun 𝔭 => ?_` and prove the remaining obligations. Rewrite using `[← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.mpr hI) (Associates.mk_ne_zero.mpr hJ) (Associates.irreducible_mk.mpr 𝔭.irreducible), pow_add]`.
-/
theorem heckeIdeal_mul (χ : (L ≃ₐ[K] L) →* ℂˣ) {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) :
    heckeIdeal L χ (I * J) = heckeIdeal L χ I * heckeIdeal L χ J := by
  unfold heckeIdeal
  rw [← finprod_mul_distrib (mulSupport_heckeVal_pow_count_finite L χ hI) (mulSupport_heckeVal_pow_count_finite L χ hJ)]
  refine finprod_congr fun 𝔭 => ?_
  rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.mpr hI)
    (Associates.mk_ne_zero.mpr hJ) (Associates.irreducible_mk.mpr 𝔭.irreducible), pow_add]

/- English proof (translation)
Unfold `heckeIdeal`. Rewrite using `[finprod_eq_single _ 𝔮 fun 𝔭 h => ?_]`. Rewrite using `[Associates.count_self (Associates.irreducible_mk.mpr 𝔮.irreducible), pow_one]`. Establish `hne : Associates.mk 𝔭.asIdeal ≠ Associates.mk 𝔮.asIdeal` using `fun heq => h (IsDedekindDomain.HeightOneSpectrum.ext (associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp heq)))`. Rewrite using `[Associates.count_eq_zero_of_ne (Associates.irreducible_mk.mpr 𝔭.irreducible) (Associates.irreducible_mk.mpr 𝔮.irreducible) hne, pow_zero]`.
-/
theorem heckeIdeal_prime (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 K)) :
    heckeIdeal L χ 𝔮.asIdeal = heckeVal L χ 𝔮 := by
  unfold heckeIdeal
  rw [finprod_eq_single _ 𝔮 fun 𝔭 h => ?_]
  · rw [Associates.count_self (Associates.irreducible_mk.mpr 𝔮.irreducible), pow_one]
  · have hne : Associates.mk 𝔭.asIdeal ≠ Associates.mk 𝔮.asIdeal := fun heq =>
      h (IsDedekindDomain.HeightOneSpectrum.ext
        (associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp heq)))
    rw [Associates.count_eq_zero_of_ne (Associates.irreducible_mk.mpr 𝔭.irreducible)
      (Associates.irreducible_mk.mpr 𝔮.irreducible) hne, pow_zero]

/- English proof (translation)
Unfold `heckeIdeal`. Rewrite using `[Associates.mk_one, Associates.factors_one]`. Use `finprod_eq_one_of_forall_eq_one fun 𝔭 => ?_` and prove the remaining obligations. Rewrite using `[Associates.count_zero (Associates.irreducible_mk.mpr 𝔭.irreducible), pow_zero]`.
-/
theorem heckeIdeal_top (χ : (L ≃ₐ[K] L) →* ℂˣ) : heckeIdeal L χ 1 = 1 := by
  unfold heckeIdeal
  rw [Associates.mk_one, Associates.factors_one]
  refine finprod_eq_one_of_forall_eq_one fun 𝔭 => ?_
  rw [Associates.count_zero (Associates.irreducible_mk.mpr 𝔭.irreducible), pow_zero]

/- English proof (translation)
Establish `hζ` using `(IsCyclotomicExtension.zeta_spec m ℚ F).toInteger_isPrimitiveRoot`. Establish `hpP : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 F) ∈ P`. Establish `h1 : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 ℚ) ∈ 𝔭.asIdeal` using `Ideal.absNorm_mem _`. Establish `h3 : algebraMap (𝓞 ℚ) (𝓞 F) ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 ℚ) ∈ P` using `(le_of_eq hLies.over : 𝔭.asIdeal ≤ P.under (𝓞 ℚ)) h1`. Rewrite `h3` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `hcopP : (Ideal.absNorm P).Coprime m`. Establish `hd : Ideal.absNorm P ∣ Ideal.absNorm 𝔭.asIdeal ^ Module.finrank ℤ (𝓞 F)`. Rewrite using `[← Ideal.absNorm_span_natCast]`. Conclude with `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hpP)`. Conclude with `Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.pow_left _ hp)`.

Establish `h₀` using `hζ.idealQuotient_mk (fun h1 => hPp.ne_top (Ideal.absNorm_eq_one_iff.mp h1)) hcopP`. Rewrite `hmem` using `[IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq m F σ hζ.pow_eq_one, ← Ideal.Quotient.eq, map_pow, map_pow]`. Establish `hmod` using `(pow_eq_pow_iff_modEq_of_isPrimitiveRoot h₀).mp hmem`. Rewrite `hmod` using `[← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]`. Then use the resulting hypothesis.
-/
private theorem galEquivZMod_eq_of_sub_zeta_pow_mem (m : ℕ) [NeZero m] (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {m} ℚ F] (𝔭 : HeightOneSpectrum (𝓞 ℚ))
    (hp : (Ideal.absNorm 𝔭.asIdeal).Coprime m) (P : Ideal (𝓞 F)) (hPp : P.IsPrime)
    (hLies : P.LiesOver 𝔭.asIdeal) (σ : F ≃ₐ[ℚ] F) (e : ℕ)
    (hmem : σ • (IsCyclotomicExtension.zeta_spec m ℚ F).toInteger -
      (IsCyclotomicExtension.zeta_spec m ℚ F).toInteger ^ e ∈ P) :
    ((IsCyclotomicExtension.Rat.galEquivZMod m F σ : (ZMod m)ˣ) : ZMod m) = e := by
  have hζ := (IsCyclotomicExtension.zeta_spec m ℚ F).toInteger_isPrimitiveRoot

  have hpP : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 F) ∈ P := by
    have h1 : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 ℚ) ∈ 𝔭.asIdeal := Ideal.absNorm_mem _
    have h3 : algebraMap (𝓞 ℚ) (𝓞 F) ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 ℚ) ∈ P :=
      (le_of_eq hLies.over : 𝔭.asIdeal ≤ P.under (𝓞 ℚ)) h1
    rwa [map_natCast] at h3
  have hcopP : (Ideal.absNorm P).Coprime m := by
    have hd : Ideal.absNorm P ∣ Ideal.absNorm 𝔭.asIdeal ^ Module.finrank ℤ (𝓞 F) := by
      rw [← Ideal.absNorm_span_natCast]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hpP)
    exact Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.pow_left _ hp)

  have h₀ := hζ.idealQuotient_mk (fun h1 => hPp.ne_top (Ideal.absNorm_eq_one_iff.mp h1)) hcopP
  rw [IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq m F σ hζ.pow_eq_one, ← Ideal.Quotient.eq,
    map_pow, map_pow] at hmem
  have hmod := (pow_eq_pow_iff_modEq_of_isPrimitiveRoot h₀).mp hmem
  rwa [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hmod

variable (m : ℕ) [NeZero m] (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F]

/- English proof (translation)
Unfold `IsFrob at h`. Take `⟨P, hPp, hLies, hP⟩` from `h`. Conclude with `galEquivZMod_eq_of_sub_zeta_pow_mem m F 𝔭 hp P hPp hLies σ _ (hP _)`.
-/
theorem gal_of_isFrob (𝔭 : HeightOneSpectrum (𝓞 ℚ)) (hp : (Ideal.absNorm 𝔭.asIdeal).Coprime m) {σ : F ≃ₐ[ℚ] F}
    (h : IsFrob F 𝔭 σ) : ((galEquivZMod m F σ : (ZMod m)ˣ) : ZMod m) = (Ideal.absNorm 𝔭.asIdeal : ℕ) := by
  unfold IsFrob at h
  obtain ⟨P, hPp, hLies, hP⟩ := h
  exact galEquivZMod_eq_of_sub_zeta_pow_mem m F 𝔭 hp P hPp hLies σ _ (hP _)
end Cyc

section Cyc2
open IsCyclotomicExtension.Rat
variable (m : ℕ) [NeZero m] (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F]

/- English proof (translation)
Unfold `UnramIn`. Introduce `σ hσ`. Unfold `InInertia at hσ`. Take `⟨P, hPp, hLies, hP⟩` from `hσ`. Establish `h1` using `galEquivZMod_eq_of_sub_zeta_pow_mem m F 𝔭 hp P hPp hLies σ 1 (by rw [pow_one]; exact hP _)`.

Establish `h2 : galEquivZMod m F σ = 1` using `Units.ext (by rw [h1]; simp)`. Conclude with `(MulEquiv.map_eq_one_iff _).mp h2`.
-/
theorem unramIn_cyc (𝔭 : HeightOneSpectrum (𝓞 ℚ)) (hp : (Ideal.absNorm 𝔭.asIdeal).Coprime m) : UnramIn F 𝔭 := by
  unfold UnramIn
  intro σ hσ
  unfold InInertia at hσ
  obtain ⟨P, hPp, hLies, hP⟩ := hσ
  have h1 := galEquivZMod_eq_of_sub_zeta_pow_mem m F 𝔭 hp P hPp hLies σ 1 (by rw [pow_one]; exact hP _)
  have h2 : galEquivZMod m F σ = 1 := Units.ext (by rw [h1]; simp)
  exact (MulEquiv.map_eq_one_iff _).mp h2

def galChar (ψ : DirichletCharacter ℂ m) : (F ≃ₐ[ℚ] F) →* ℂˣ :=
  (MulChar.toUnitHom ψ).comp (galEquivZMod m F).toMonoidHom

/- English proof (translation)
Establish `hex : ∃ σ, IsFrob F 𝔭 σ`. Use `𝔭.isMaximal` as an intermediate fact. Take `⟨Q, hQm, hQ⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) 𝔭.asIdeal`. Establish `: Finite (𝓞 F ⧸ Q)` using `Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)`. Use `IsCyclotomicExtension.isGalois {m} ℚ F` as an intermediate fact.

Establish `hact : ∀ (τ : F ≃ₐ[ℚ] F) (y : 𝓞 F), galRestrict (𝓞 ℚ) ℚ F (𝓞 F) τ y = τ • y` using `fun τ y => NumberField.RingOfIntegers.ext (by exact algebraMap_galRestrict_apply (A := 𝓞 ℚ) (K := ℚ) (L := F) (B := 𝓞 F) τ y)`. Use `letI := IsIntegralClosure.MulSemiringAction (𝓞 ℚ) ℚ F (𝓞 F)`. Establish `: SMulCommClass (F ≃ₐ[ℚ] F) (𝓞 ℚ) (𝓞 F)` using `⟨fun σ a x => map_smul (galRestrict (𝓞 ℚ) ℚ F (𝓞 F) σ) a x⟩`. Establish `: Algebra.IsInvariant (𝓞 ℚ) (𝓞 F) (F ≃ₐ[ℚ] F)` using `Algebra.isInvariant_of_isGalois (𝓞 ℚ) ℚ F (𝓞 F)`. Take `⟨σ, hσ⟩` from `IsArithFrobAt.exists_of_isInvariant (𝓞 ℚ) (F ≃ₐ[ℚ] F) Q`.

Use `⟨σ, Q, hQm.isPrime, hQ, fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `hσ x`. Rewrite `h1` using `[← hQ.over, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, MulSemiringAction.toAlgHom_apply]`. Establish `h2 : galRestrict (𝓞 ℚ) ℚ F (𝓞 F) σ x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q` using `h1`. Rewrite `h2` using `[hact]`. Then use the resulting hypothesis.

Establish `hin : ∀ σ, InInertia F 𝔭 σ → galChar m F ψ σ = 1` using `fun σ hσ => by`. Rewrite using `[unramIn_cyc m F 𝔭 hp σ hσ, map_one]`. Establish `hcond : (∀ σ, InInertia F 𝔭 σ → galChar m F ψ σ = 1) ∧ ∃ σ, IsFrob F 𝔭 σ` using `⟨hin, hex⟩`. Unfold `heckeVal`. Rewrite using `[dif_pos hcond]`.

Establish `hs` using `gal_of_isFrob m F 𝔭 hp hcond.2.choose_spec`. Simplify using `only [galChar, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulChar.coe_toUnitHom]`. Rewrite using `[hs]`.
-/
theorem heckeVal_galChar (ψ : DirichletCharacter ℂ m) (𝔭 : HeightOneSpectrum (𝓞 ℚ))
    (hp : (Ideal.absNorm 𝔭.asIdeal).Coprime m) :
    heckeVal F (galChar m F ψ) 𝔭 = ψ (Ideal.absNorm 𝔭.asIdeal : ℕ) := by

  have hex : ∃ σ, IsFrob F 𝔭 σ := by
    have := 𝔭.isMaximal
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) 𝔭.asIdeal
    have : Finite (𝓞 F ⧸ Q) :=
      Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)
    have := IsCyclotomicExtension.isGalois {m} ℚ F
    have hact : ∀ (τ : F ≃ₐ[ℚ] F) (y : 𝓞 F), galRestrict (𝓞 ℚ) ℚ F (𝓞 F) τ y = τ • y := fun τ y =>
      NumberField.RingOfIntegers.ext (by exact algebraMap_galRestrict_apply (A := 𝓞 ℚ) (K := ℚ) (L := F) (B := 𝓞 F) τ y)
    letI := IsIntegralClosure.MulSemiringAction (𝓞 ℚ) ℚ F (𝓞 F)
    have : SMulCommClass (F ≃ₐ[ℚ] F) (𝓞 ℚ) (𝓞 F) :=
      ⟨fun σ a x => map_smul (galRestrict (𝓞 ℚ) ℚ F (𝓞 F) σ) a x⟩
    have : Algebra.IsInvariant (𝓞 ℚ) (𝓞 F) (F ≃ₐ[ℚ] F) := Algebra.isInvariant_of_isGalois (𝓞 ℚ) ℚ F (𝓞 F)
    obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 ℚ) (F ≃ₐ[ℚ] F) Q
    refine ⟨σ, Q, hQm.isPrime, hQ, fun x => ?_⟩
    have h1 := hσ x
    rw [← hQ.over, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, MulSemiringAction.toAlgHom_apply] at h1
    have h2 : galRestrict (𝓞 ℚ) ℚ F (𝓞 F) σ x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q := h1
    rwa [hact] at h2
  have hin : ∀ σ, InInertia F 𝔭 σ → galChar m F ψ σ = 1 := fun σ hσ => by
    rw [unramIn_cyc m F 𝔭 hp σ hσ, map_one]
  have hcond : (∀ σ, InInertia F 𝔭 σ → galChar m F ψ σ = 1) ∧ ∃ σ, IsFrob F 𝔭 σ := ⟨hin, hex⟩
  unfold heckeVal
  rw [dif_pos hcond]
  have hs := gal_of_isFrob m F 𝔭 hp hcond.2.choose_spec
  simp only [galChar, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulChar.coe_toUnitHom]
  rw [hs]

/- English proof (translation)
Set `g : Ideal (𝓞 ℚ) →* ℂ` to `ψ.toMonoidHom.comp ((Nat.castRingHom (ZMod m)).toMonoidHom.comp (Ideal.absNorm (S := 𝓞 ℚ)).toMonoidHom)`. Establish `hg : ∀ J, g J = ψ (Ideal.absNorm J : ℕ)` using `fun J => rfl`. Establish `hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) => v.maxPowDividing I).Finite`. Use `(Ideal.finite_factors hI).subset fun v hv => ?_` and prove the remaining obligations. Simplify using `only [Function.mem_mulSupport] at hv`.

Establish `h0 : (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0` using `fun h0 => hv (by rw [HeightOneSpectrum.maxPowDividing, h0, pow_zero])`. Conclude with `(Associates.count_ne_zero_iff_dvd hI v.irreducible).mp h0`. Establish `hterm : ∀ v : HeightOneSpectrum (𝓞 ℚ), heckeVal F (galChar m F ψ) v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = g (v.maxPowDividing I)` using `fun v => by`. Rewrite using `[HeightOneSpectrum.maxPowDividing, map_pow, hg]`. Distinguish the cases in `hk : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0`.

Rewrite using `[hk, pow_zero, pow_zero]`. Establish `hdvd : v.asIdeal ∣ I` using `(Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hk`. Establish `hcop : (Ideal.absNorm v.asIdeal).Coprime m` using `Nat.Coprime.coprime_dvd_left (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)) hp`. Rewrite using `[heckeVal_galChar m F ψ v hcop]`. Unfold `heckeIdeal`.

Rewrite using `[finprod_congr hterm, ← g.map_finprod hfin, Ideal.finprod_heightOneSpectrum_factorization hI, hg]`.
-/
theorem heckeIdeal_galChar (ψ : DirichletCharacter ℂ m) (I : Ideal (𝓞 ℚ)) (hI : I ≠ 0)
    (hp : (Ideal.absNorm I).Coprime m) : heckeIdeal F (galChar m F ψ) I = ψ (Ideal.absNorm I : ℕ) := by

  let g : Ideal (𝓞 ℚ) →* ℂ := ψ.toMonoidHom.comp
    ((Nat.castRingHom (ZMod m)).toMonoidHom.comp (Ideal.absNorm (S := 𝓞 ℚ)).toMonoidHom)
  have hg : ∀ J, g J = ψ (Ideal.absNorm J : ℕ) := fun J => rfl
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) => v.maxPowDividing I).Finite := by
    refine (Ideal.finite_factors hI).subset fun v hv => ?_
    simp only [Function.mem_mulSupport] at hv
    have h0 : (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 := fun h0 =>
      hv (by rw [HeightOneSpectrum.maxPowDividing, h0, pow_zero])
    exact (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp h0
  have hterm : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      heckeVal F (galChar m F ψ) v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors =
        g (v.maxPowDividing I) := fun v => by
    rw [HeightOneSpectrum.maxPowDividing, map_pow, hg]
    by_cases hk : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
    · rw [hk, pow_zero, pow_zero]
    · have hdvd : v.asIdeal ∣ I := (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hk
      have hcop : (Ideal.absNorm v.asIdeal).Coprime m :=
        Nat.Coprime.coprime_dvd_left (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)) hp
      rw [heckeVal_galChar m F ψ v hcop]
  unfold heckeIdeal
  rw [finprod_congr hterm, ← g.map_finprod hfin, Ideal.finprod_heightOneSpectrum_factorization hI, hg]

/- English proof (translation)
Rewrite using `[Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)), Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]`.
-/
theorem absNorm_span_int (a : ℤ) : Ideal.absNorm (Ideal.span {(a : 𝓞 ℚ)}) = a.natAbs := by
  rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)), Algebra.norm_algebraMap,
    NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]

/- English proof (translation)
Take `⟨a, ha⟩` from `Rat.int_algebraMap_surjective (𝓞 ℚ) α`. Conclude with `⟨a, by rw [← ha, eq_intCast]⟩`.
-/
theorem exists_int (α : 𝓞 ℚ) : ∃ a : ℤ, α = a := by
  obtain ⟨a, ha⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) α
  exact ⟨a, by rw [← ha, eq_intCast]⟩

/- English proof (translation)
Simplify using `using map_dvd (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h`.
-/
theorem int_dvd_of {a b : ℤ} (h : (a : 𝓞 ℚ) ∣ b) : a ∣ b := by
  simpa using map_dvd (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h

/- English proof (translation)
Establish `hm0 : ((m : ℤ) : 𝓞 ℚ) ≠ 0` using `by simpa using NeZero.ne m`. Unfold `IsModulus`. Use `⟨?_, fun 𝔭 h𝔭 => ?_, fun α β hab => ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hm0`.

Establish `hpr : (Ideal.absNorm 𝔭.asIdeal).Prime`. Rewrite using `[absNorm_eq]`. Conclude with `(Rat.HeightOneSpectrum.primesEquiv 𝔭).2`. Establish `hcop : (Ideal.absNorm 𝔭.asIdeal).Coprime m`. Rewrite using `[Nat.Prime.coprime_iff_not_dvd hpr]`.

Introduce and unpack `⟨k, hk⟩`. Apply `h𝔭` to reduce the goal to its premises. Rewrite using `[Ideal.dvd_span_singleton]`. Establish `hmk : ((m : ℤ) : 𝓞 ℚ) = ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 ℚ) * (k : 𝓞 ℚ)`. Rewrite using `[Int.cast_natCast, hk, Nat.cast_mul]`.

Rewrite using `[hmk]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)`. Rewrite using `[heckeVal_galChar m F ψ 𝔭 hcop]`. Establish `hu : IsUnit ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod m)`. Rewrite using `[← ZMod.coe_unitOfCoprime _ hcop]`.

Conclude with `Units.isUnit _`. Conclude with `(hu.map ψ).ne_zero`. Unfold `RayPair at hab`. Take `⟨hα, hβ, hcα, hcβ, hd, hpos⟩` from `hab`. Take `⟨a, rfl⟩` from `exists_int α`.

Take `⟨b, rfl⟩` from `exists_int β`. Establish `hcopZ : ∀ c : ℤ, IsCoprime (Ideal.span {(c : 𝓞 ℚ)}) (Ideal.span {((m : ℤ) : 𝓞 ℚ)}) → (c.natAbs).Coprime m`. Introduce `c hc`. Rewrite `hc` using `[Ideal.isCoprime_span_singleton_iff]`. Take `⟨u, v, huv⟩` from `hc`.

Take `⟨u', rfl⟩` from `exists_int u`. Take `⟨v', rfl⟩` from `exists_int v`. Establish `h1 : u' * c + v' * m = 1` using `by exact_mod_cast huv`. Conclude with `Int.isCoprime_iff_gcd_eq_one.mp ⟨u', v', h1⟩`. Establish `hne : ∀ c : ℤ, (c : 𝓞 ℚ) ≠ 0 → Ideal.span {(c : 𝓞 ℚ)} ≠ 0` using `fun c hc => by`.

Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hc`. Rewrite using `[heckeIdeal_galChar m F ψ _ (hne a hα) (by rw [absNorm_span_int]; exact hcopZ a hcα), heckeIdeal_galChar m F ψ _ (hne b hβ) (by rw [absNorm_span_int]; exact hcopZ b hcβ), absNorm_span_int, absNorm_span_int]`. Establish `hdvd : (m : ℤ) ∣ a - b` using `int_dvd_of (by push_cast; exact Ideal.mem_span_singleton.mp hd)`. Establish `hab : 0 < a * b`.

Establish `h` using `hpos (Rat.castHom ℝ)`. Establish `e1 : (Rat.castHom ℝ) ((a : 𝓞 ℚ) : ℚ) = (a : ℝ)` using `by simp`. Establish `e2 : (Rat.castHom ℝ) ((b : 𝓞 ℚ) : ℚ) = (b : ℝ)` using `by simp`. Rewrite `h` using `[e1, e2]`. Conclude with `h` after adjusting the coercions.

Establish `key : ((a.natAbs : ℤ) : ZMod m) = ((b.natAbs : ℤ) : ZMod m)`. Rewrite using `[ZMod.intCast_eq_intCast_iff_dvd_sub]`. Break down `mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩` into its components or cases. Rewrite using `[Int.natAbs_of_nonneg ha.le, Int.natAbs_of_nonneg hb.le, ← neg_sub]`. Conclude with `dvd_neg.mpr hdvd`.

Rewrite using `[Int.ofNat_natAbs_of_nonpos ha.le, Int.ofNat_natAbs_of_nonpos hb.le, neg_sub_neg]`. Conclude with `hdvd`. Establish `key' : ((a.natAbs : ℕ) : ZMod m) = ((b.natAbs : ℕ) : ZMod m)`. Rewrite `key` using `[Int.cast_natCast, Int.cast_natCast]`. Then use the resulting hypothesis. Rewrite using `[key']`.
-/
theorem isModulus_galChar (ψ : DirichletCharacter ℂ m) :
    IsModulus F (galChar m F ψ) (Ideal.span {((m : ℤ) : 𝓞 ℚ)}) := by
  have hm0 : ((m : ℤ) : 𝓞 ℚ) ≠ 0 := by simpa using NeZero.ne m
  unfold IsModulus
  refine ⟨?_, fun 𝔭 h𝔭 => ?_, fun α β hab => ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact hm0
  ·
    have hpr : (Ideal.absNorm 𝔭.asIdeal).Prime := by
      rw [absNorm_eq]
      exact (Rat.HeightOneSpectrum.primesEquiv 𝔭).2
    have hcop : (Ideal.absNorm 𝔭.asIdeal).Coprime m := by
      rw [Nat.Prime.coprime_iff_not_dvd hpr]
      rintro ⟨k, hk⟩
      apply h𝔭
      rw [Ideal.dvd_span_singleton]
      have hmk : ((m : ℤ) : 𝓞 ℚ) = ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 ℚ) * (k : 𝓞 ℚ) := by
        rw [Int.cast_natCast, hk, Nat.cast_mul]
      rw [hmk]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    rw [heckeVal_galChar m F ψ 𝔭 hcop]
    have hu : IsUnit ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod m) := by
      rw [← ZMod.coe_unitOfCoprime _ hcop]
      exact Units.isUnit _
    exact (hu.map ψ).ne_zero
  ·
    unfold RayPair at hab
    obtain ⟨hα, hβ, hcα, hcβ, hd, hpos⟩ := hab
    obtain ⟨a, rfl⟩ := exists_int α
    obtain ⟨b, rfl⟩ := exists_int β
    have hcopZ : ∀ c : ℤ, IsCoprime (Ideal.span {(c : 𝓞 ℚ)}) (Ideal.span {((m : ℤ) : 𝓞 ℚ)}) →
        (c.natAbs).Coprime m := by
      intro c hc
      rw [Ideal.isCoprime_span_singleton_iff] at hc
      obtain ⟨u, v, huv⟩ := hc
      obtain ⟨u', rfl⟩ := exists_int u
      obtain ⟨v', rfl⟩ := exists_int v
      have h1 : u' * c + v' * m = 1 := by exact_mod_cast huv
      exact Int.isCoprime_iff_gcd_eq_one.mp ⟨u', v', h1⟩
    have hne : ∀ c : ℤ, (c : 𝓞 ℚ) ≠ 0 → Ideal.span {(c : 𝓞 ℚ)} ≠ 0 := fun c hc => by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hc
    rw [heckeIdeal_galChar m F ψ _ (hne a hα) (by rw [absNorm_span_int]; exact hcopZ a hcα),
      heckeIdeal_galChar m F ψ _ (hne b hβ) (by rw [absNorm_span_int]; exact hcopZ b hcβ),
      absNorm_span_int, absNorm_span_int]
    have hdvd : (m : ℤ) ∣ a - b := int_dvd_of (by push_cast; exact Ideal.mem_span_singleton.mp hd)
    have hab : 0 < a * b := by
      have h := hpos (Rat.castHom ℝ)
      have e1 : (Rat.castHom ℝ) ((a : 𝓞 ℚ) : ℚ) = (a : ℝ) := by simp
      have e2 : (Rat.castHom ℝ) ((b : 𝓞 ℚ) : ℚ) = (b : ℝ) := by simp
      rw [e1, e2] at h
      exact_mod_cast h
    have key : ((a.natAbs : ℤ) : ZMod m) = ((b.natAbs : ℤ) : ZMod m) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [Int.natAbs_of_nonneg ha.le, Int.natAbs_of_nonneg hb.le, ← neg_sub]
        exact dvd_neg.mpr hdvd
      · rw [Int.ofNat_natAbs_of_nonpos ha.le, Int.ofNat_natAbs_of_nonpos hb.le, neg_sub_neg]
        exact hdvd
    have key' : ((a.natAbs : ℕ) : ZMod m) = ((b.natAbs : ℕ) : ZMod m) := by
      rwa [Int.cast_natCast, Int.cast_natCast] at key
    rw [key']

/- English proof (translation)
Unfold `condNorm`. Establish `hmem : Ideal.absNorm (Ideal.span {((m : ℤ) : 𝓞 ℚ)}) ∈ {n | ∃ 𝔪, IsModulus F (galChar m F ψ) 𝔪 ∧ Ideal.absNorm 𝔪 = n}` using `⟨_, isModulus_galChar m F ψ, rfl⟩`. Use `(Nat.sInf_le hmem).trans ?_` and prove the remaining obligations. Rewrite using `[absNorm_span_int]`. Simplify using the standard rewrite rules.
-/
theorem condNorm_galChar_le (ψ : DirichletCharacter ℂ m) : condNorm F (galChar m F ψ) ≤ m := by
  unfold condNorm
  have hmem : Ideal.absNorm (Ideal.span {((m : ℤ) : 𝓞 ℚ)}) ∈
      {n | ∃ 𝔪, IsModulus F (galChar m F ψ) 𝔪 ∧ Ideal.absNorm 𝔪 = n} :=
    ⟨_, isModulus_galChar m F ψ, rfl⟩
  refine (Nat.sInf_le hmem).trans ?_
  rw [absNorm_span_int]
  simp

/- English proof (translation)
Take `⟨a, ha⟩ : ∃ a : ℕ, a = 1 + Ideal.absNorm 𝔪 * c` from `⟨_, rfl⟩`. Rewrite `hc`, the goal using `[← ha]`. Establish `hmem : ((Ideal.absNorm 𝔪 * c : ℕ) : 𝓞 ℚ) ∈ 𝔪`. Rewrite using `[Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.absNorm_mem 𝔪)`.

Establish `hα0 : ((a : ℕ) : 𝓞 ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr (by rw [ha]; omega)`. Establish `hsub : ((a : ℕ) : 𝓞 ℚ) - 1 = ((Ideal.absNorm 𝔪 * c : ℕ) : 𝓞 ℚ)`. Rewrite using `[ha]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcop : IsCoprime (Ideal.span {((a : ℕ) : 𝓞 ℚ)}) 𝔪`. Rewrite using `[Ideal.isCoprime_iff_exists]`. Use `⟨(a : 𝓞 ℚ), Ideal.mem_span_singleton_self _, -((Ideal.absNorm 𝔪 * c : ℕ) : 𝓞 ℚ), 𝔪.neg_mem hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[← hsub]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hray : RayPair 𝔪 ((a : ℕ) : 𝓞 ℚ) 1`. Unfold `RayPair`. Use `⟨hα0, one_ne_zero, hcop, ?_, ?_, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq, top_sup_eq]`. Rewrite using `[hsub]`.

Conclude with `hmem`. Establish `hpos : 0 < a` using `by omega`. Simplify using `using hpos`. Unfold `IsModulus at h`. Establish `heq` using `h.2.2 _ _ hray`.

Establish `hN : Ideal.absNorm (Ideal.span {((a : ℕ) : 𝓞 ℚ)}) = a`. Rewrite using `[Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]`. Establish `hI : Ideal.span {((a : ℕ) : 𝓞 ℚ)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hα0`.

Establish `key` using `heckeIdeal_galChar m F ψ _ hI (by rw [hN]; exact hc)`. Rewrite `key` using `[hN]`. Rewrite using `[← key, heq, Ideal.span_singleton_one, ← Ideal.one_eq_top, heckeIdeal_top]`.
-/
theorem eq_one_of_isModulus (ψ : DirichletCharacter ℂ m) {𝔪 : Ideal (𝓞 ℚ)} (h : IsModulus F (galChar m F ψ) 𝔪)
    (c : ℕ) (hc : (1 + Ideal.absNorm 𝔪 * c).Coprime m) : ψ ((1 + Ideal.absNorm 𝔪 * c : ℕ) : ZMod m) = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = 1 + Ideal.absNorm 𝔪 * c := ⟨_, rfl⟩
  rw [← ha] at hc ⊢
  have hmem : ((Ideal.absNorm 𝔪 * c : ℕ) : 𝓞 ℚ) ∈ 𝔪 := by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem 𝔪)
  have hα0 : ((a : ℕ) : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by rw [ha]; omega)
  have hsub : ((a : ℕ) : 𝓞 ℚ) - 1 = ((Ideal.absNorm 𝔪 * c : ℕ) : 𝓞 ℚ) := by
    rw [ha]
    push_cast
    ring

  have hcop : IsCoprime (Ideal.span {((a : ℕ) : 𝓞 ℚ)}) 𝔪 := by
    rw [Ideal.isCoprime_iff_exists]
    refine ⟨(a : 𝓞 ℚ), Ideal.mem_span_singleton_self _, -((Ideal.absNorm 𝔪 * c : ℕ) : 𝓞 ℚ),
      𝔪.neg_mem hmem, ?_⟩
    rw [← hsub]
    ring
  have hray : RayPair 𝔪 ((a : ℕ) : 𝓞 ℚ) 1 := by
    unfold RayPair
    refine ⟨hα0, one_ne_zero, hcop, ?_, ?_, fun φ => ?_⟩
    · rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq, top_sup_eq]
    · rw [hsub]
      exact hmem
    · have hpos : 0 < a := by omega
      simpa using hpos
  unfold IsModulus at h
  have heq := h.2.2 _ _ hray
  have hN : Ideal.absNorm (Ideal.span {((a : ℕ) : 𝓞 ℚ)}) = a := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hI : Ideal.span {((a : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hα0
  have key := heckeIdeal_galChar m F ψ _ hI (by rw [hN]; exact hc)
  rw [hN] at key
  rw [← key, heq, Ideal.span_singleton_one, ← Ideal.one_eq_top, heckeIdeal_top]

end Cyc2

/- English proof (translation)
Apply `le_antisymm (condNorm_galChar_le 4 F ψ)` to reduce the goal to its premises. Unfold `condNorm`. Use `le_csInf ⟨_, _, isModulus_galChar 4 F ψ, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `n ⟨𝔪, h𝔪, rfl⟩`. Establish `hne : Ideal.absNorm 𝔪 ≠ 0`.

Establish `h` using `h𝔪`. Unfold `IsModulus at h`. Conclude with `fun h0 => h.1 (Ideal.absNorm_eq_zero_iff.mp h0)`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`.

Establish `key : ∀ k : ℕ, (k : ZMod 4) = 3 → ψ (k : ZMod 4) = 1 → ψ 3 = 1` using `fun k hk h => hk ▸ h`. Apply `hψ` to reduce the goal to its premises. Establish `hcases : Ideal.absNorm 𝔪 = 1 ∨ Ideal.absNorm 𝔪 = 2 ∨ Ideal.absNorm 𝔪 = 3` using `by omega`. Break down `hcases with h | h | h` into its components or cases. Conclude with `key _ (by rw [h]; decide) (eq_one_of_isModulus 4 F ψ h𝔪 2 (by rw [h]; decide))`.

Conclude with `key _ (by rw [h]; decide) (eq_one_of_isModulus 4 F ψ h𝔪 1 (by rw [h]; decide))`. Conclude with `key _ (by rw [h]; decide) (eq_one_of_isModulus 4 F ψ h𝔪 2 (by rw [h]; decide))`.
-/
theorem condNorm_four (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] (ψ : DirichletCharacter ℂ 4)
    (hψ : ψ 3 ≠ 1) : condNorm F (galChar 4 F ψ) = 4 := by
  apply le_antisymm (condNorm_galChar_le 4 F ψ)
  unfold condNorm
  refine le_csInf ⟨_, _, isModulus_galChar 4 F ψ, rfl⟩ ?_
  rintro n ⟨𝔪, h𝔪, rfl⟩
  have hne : Ideal.absNorm 𝔪 ≠ 0 := by
    have h := h𝔪
    unfold IsModulus at h
    exact fun h0 => h.1 (Ideal.absNorm_eq_zero_iff.mp h0)

  by_contra hlt
  push Not at hlt
  have key : ∀ k : ℕ, (k : ZMod 4) = 3 → ψ (k : ZMod 4) = 1 → ψ 3 = 1 := fun k hk h => hk ▸ h
  apply hψ
  have hcases : Ideal.absNorm 𝔪 = 1 ∨ Ideal.absNorm 𝔪 = 2 ∨ Ideal.absNorm 𝔪 = 3 := by omega
  rcases hcases with h | h | h
  · exact key _ (by rw [h]; decide) (eq_one_of_isModulus 4 F ψ h𝔪 2 (by rw [h]; decide))
  · exact key _ (by rw [h]; decide) (eq_one_of_isModulus 4 F ψ h𝔪 1 (by rw [h]; decide))
  · exact key _ (by rw [h]; decide) (eq_one_of_isModulus 4 F ψ h𝔪 2 (by rw [h]; decide))

/- English proof (translation)
Establish `hall : ∀ χ : (F ≃ₐ[ℚ] F) →* ℂˣ, condNorm F χ ≤ 4` using `fun χ => by`. Establish `hχ : galChar 4 F (MulChar.ofUnitHom (χ.comp (IsCyclotomicExtension.Rat.galEquivZMod 4 F).symm.toMonoidHom)) = χ`. Use `MonoidHom.ext fun σ => Units.ext ?_` and prove the remaining obligations. Simplify using `only [galChar, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulChar.coe_toUnitHom, MulChar.ofUnitHom_coe, MulEquiv.symm_apply_apply]`. Rewrite using `[← hχ]`.

Conclude with `condNorm_galChar_le 4 F _`. Set `ψ4 : DirichletCharacter ℂ 4` to `ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)`. Establish `h3 : ψ4 3 ≠ 1`. Establish `e : ZMod.χ₄ 3 = -1` using `by decide`. Rewrite using `[MulChar.ringHomComp_apply, e]`.

Evaluate the numerical expressions. Establish `hsup : (⨆ χ : (F ≃ₐ[ℚ] F) →* ℂˣ, condNorm F χ) = 4`. Apply `le_antisymm (ciSup_le hall)` to reduce the goal to its premises. Conclude with `(condNorm_four F ψ4 h3).symm.le.trans (le_ciSup ⟨4, by rintro _ ⟨χ, rfl⟩; exact hall χ⟩ (galChar 4 F ψ4))`. Unfold `bigQ`.

Rewrite using `[hsup]`. Simplify using the standard rewrite rules.
-/
theorem bigQ_four (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] : bigQ ℚ F = 4 := by

  have hall : ∀ χ : (F ≃ₐ[ℚ] F) →* ℂˣ, condNorm F χ ≤ 4 := fun χ => by
    have hχ : galChar 4 F (MulChar.ofUnitHom (χ.comp (IsCyclotomicExtension.Rat.galEquivZMod 4 F).symm.toMonoidHom)) = χ := by
      refine MonoidHom.ext fun σ => Units.ext ?_
      simp only [galChar, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulChar.coe_toUnitHom, MulChar.ofUnitHom_coe, MulEquiv.symm_apply_apply]
    rw [← hχ]
    exact condNorm_galChar_le 4 F _

  let ψ4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
  have h3 : ψ4 3 ≠ 1 := by
    have e : ZMod.χ₄ 3 = -1 := by decide
    rw [MulChar.ringHomComp_apply, e]
    norm_num
  have hsup : (⨆ χ : (F ≃ₐ[ℚ] F) →* ℂˣ, condNorm F χ) = 4 := by
    apply le_antisymm (ciSup_le hall)
    exact (condNorm_four F ψ4 h3).symm.le.trans
      (le_ciSup ⟨4, by rintro _ ⟨χ, rfl⟩; exact hall χ⟩ (galChar 4 F ψ4))
  unfold bigQ
  rw [hsup]
  simp

/- English proof (translation)
The claim follows from `@bigQ_four _ _ _ (CyclotomicField.isCyclotomicExtension 4 ℚ)`.
-/
example : bigQ ℚ (CyclotomicField 4 ℚ) = 4 :=
  @bigQ_four _ _ _ (CyclotomicField.isCyclotomicExtension 4 ℚ)

/- English proof (translation)
Establish `hX1 : Formalism.MainNotions.GlobalTheoryTheory.X1 (Real.exp 1) 5 = Real.exp (Real.exp 1)`. Unfold `Formalism.MainNotions.GlobalTheoryTheory.X1`. Evaluate the numerical expressions. Establish `hX2 : Formalism.MainNotions.GlobalTheoryTheory.X2 (Real.exp 1) 5 = Real.exp (Real.exp 1)`. Unfold `Formalism.MainNotions.GlobalTheoryTheory.X2`.

Evaluate the numerical expressions. Establish `he1` using `Real.exp_one_gt_d9`. Establish `he2` using `Real.exp_one_lt_d9`. Establish `hlo : (11 : ℝ) ≤ Real.exp (Real.exp 1)`. Establish `h2 : Real.exp (Real.exp 1) = Real.exp 1 * Real.exp 1 * Real.exp (Real.exp 1 - 2)`.

Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `Real.add_one_le_exp (Real.exp 1 - 2)`. Establish `hA : (7.3 : ℝ) < Real.exp 1 * Real.exp 1` using `by nlinarith`.

Establish `hB : (1.7 : ℝ) ≤ Real.exp (Real.exp 1 - 2)` using `by linarith`. Rewrite using `[h2]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hhi : Real.exp (Real.exp 1) < 49`. Establish `h2 : Real.exp (Real.exp 1) < Real.exp 3` using `Real.exp_lt_exp.mpr (by linarith)`.

Establish `h3 : Real.exp 3 = Real.exp 1 ^ 3`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions. Establish `h4` using `pow_lt_pow_left₀ he2 (Real.exp_pos 1).le (by norm_num : (3 : ℕ) ≠ 0)`. Evaluate the numerical expressions using `at h4`.

Combine the linear equalities and inequalities to obtain the conclusion. Unfold `QNum DNum`. Rewrite using `[hX1, hX2]`. Use `⟨⟨by norm_num, by norm_num, ?_, ?_⟩, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.sqrt_lt' (by norm_num)]`.

Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hlo` after adjusting the coercions. Rewrite using `[Real.sqrt_lt' (by norm_num)]`. Evaluate the numerical expressions.

Combine the linear equalities and inequalities to obtain the conclusion. Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Formalism.MainNotions.GlobalTheoryTheory.kronSym, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 11)]`. Evaluate the numerical expressions.

Introduce `p hp hle`. Establish `hp2 : p = 2`. Evaluate the numerical expressions using `at hle`. Establish `h3 : (p : ℝ) < 3` using `by linarith`. Establish `h4 : p < 3` using `by exact_mod_cast h3`.

Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Substitute `hp2` using the available equality. Simplify using `only [Formalism.MainNotions.GlobalTheoryTheory.kronSym, Formalism.MainNotions.GlobalTheoryTheory.kron2, Nat.prime_two.factorization_self]`. Evaluate the numerical expressions.
-/
theorem nums_example : QNum (Real.exp 1) 5 11 ∧ DNum (Real.exp 1) 5 11 7 := by
  have hX1 : Formalism.MainNotions.GlobalTheoryTheory.X1 (Real.exp 1) 5 = Real.exp (Real.exp 1) := by
    unfold Formalism.MainNotions.GlobalTheoryTheory.X1
    norm_num
  have hX2 : Formalism.MainNotions.GlobalTheoryTheory.X2 (Real.exp 1) 5 = Real.exp (Real.exp 1) := by
    unfold Formalism.MainNotions.GlobalTheoryTheory.X2
    norm_num
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9

  have hlo : (11 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h2 : Real.exp (Real.exp 1) = Real.exp 1 * Real.exp 1 * Real.exp (Real.exp 1 - 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have h3 := Real.add_one_le_exp (Real.exp 1 - 2)
    have hA : (7.3 : ℝ) < Real.exp 1 * Real.exp 1 := by nlinarith
    have hB : (1.7 : ℝ) ≤ Real.exp (Real.exp 1 - 2) := by linarith
    rw [h2]
    nlinarith
  have hhi : Real.exp (Real.exp 1) < 49 := by
    have h2 : Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr (by linarith)
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h4 := pow_lt_pow_left₀ he2 (Real.exp_pos 1).le (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at h4
    linarith
  unfold QNum DNum
  rw [hX1, hX2]
  refine ⟨⟨by norm_num, by norm_num, ?_, ?_⟩, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num
    linarith
  · exact_mod_cast hlo
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num
    linarith
  · norm_num
    linarith
  · simp only [Formalism.MainNotions.GlobalTheoryTheory.kronSym, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 11)]
    norm_num
  · intro p hp hle
    have hp2 : p = 2 := by
      norm_num at hle
      have h3 : (p : ℝ) < 3 := by linarith
      have h4 : p < 3 := by exact_mod_cast h3
      have := hp.two_le
      omega
    subst hp2
    simp only [Formalism.MainNotions.GlobalTheoryTheory.kronSym, Formalism.MainNotions.GlobalTheoryTheory.kron2, Nat.prime_two.factorization_self]
    norm_num

/- English proof (translation)
Unfold `ntZeros at h`. Simplify using `only [Set.mem_ofPred_eq] at h`. Take `⟨_, h1, hL⟩` from `h`. Establish `hρ : ρ ≠ 1` using `fun e => by`. Rewrite `h1` using `[e]`.

Simplify using `at h1`. Establish `han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ)` using `DifferentiableOn.analyticOnNhd (fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt) isOpen_compl_singleton`. Establish `hne0 : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0` using `(han ρ hρ).analyticOrderAt_ne_zero.mpr hL`. Establish `hnetop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤`. Introduce `htop`.

Establish `hconn : IsPreconnected ({1}ᶜ : Set ℂ)` using `(isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected`. Establish `hzero` using `han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hρ (analyticOrderAt_eq_top.mp htop)`. Establish `h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)` using `by norm_num`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num : (2 : ℂ) ≠ 1)) (by norm_num) (hzero h2)`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp hnetop`.

Unfold `mult analyticOrderNatAt`. Rewrite using `[← hn, ENat.toNat_natCast]`. Rewrite `hne0` using `[← hn]`. Conclude with `Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)`.
-/
theorem one_le_mult {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : ρ ∈ ntZeros χ) : 1 ≤ mult χ ρ := by
  unfold ntZeros at h
  simp only [Set.mem_ofPred_eq] at h
  obtain ⟨_, h1, hL⟩ := h
  have hρ : ρ ≠ 1 := fun e => by
    rw [e] at h1
    simp at h1

  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd (fun s hs =>
      (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt)
      isOpen_compl_singleton
  have hne0 : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    (han ρ hρ).analyticOrderAt_ne_zero.mpr hL

  have hnetop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro htop
    have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hρ
      (analyticOrderAt_eq_top.mp htop)
    have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num : (2 : ℂ) ≠ 1))
      (by norm_num) (hzero h2)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  unfold mult analyticOrderNatAt
  rw [← hn, ENat.toNat_natCast]
  rw [← hn] at hne0
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)

end GlobalTheory.NT.Model
end
