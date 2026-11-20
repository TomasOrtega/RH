import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SatOfPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IntGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatK
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IdeleNormValuationOfLocalCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IdeleNormLocalCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

/- English proof (translation)
The claim follows from `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)] refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩ · exact_mod_cast add_left_cancel e · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz …`.
-/
private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩

/- English proof (translation)
Establish `h0 : Ideal.span {(M : 𝓞 K)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.2 (by omega)`. Use `(Ideal.finite_factors h0).subset fun w hw => ?_` and prove the remaining obligations. Conclude with `Ideal.dvd_span_singleton.2 (not_not.1 hw)`.
-/
private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)

/- English proof (translation)
Establish `: w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal` using `⟨rfl⟩`. Use `w.isMaximal` as an intermediate fact. Use `(w.under (𝓞 K)).isMaximal` as an intermediate fact. Use `show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)`. Rewrite using `[← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]`.
-/
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

/- English proof (translation)
Establish `e : (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)` using `(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)`. Use `show Ideal.absNorm (cPl w).asIdeal = Ideal.absNorm w.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Use `(Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).symm ?_).toEquiv).symm` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `(Ideal.map_symm _).symm`.
-/
private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (cPl w) = normV w := by
  have e : (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)
  show Ideal.absNorm (cPl w).asIdeal = Ideal.absNorm w.asIdeal
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).symm ?_).toEquiv).symm
  rw [e]
  exact (Ideal.map_symm _).symm

/- English proof (translation)
Rewrite using `[Filter.eventually_cofinite]`. Use `((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 F)) fun v _ => ?_).subset fun w hw => hw` and prove the remaining obligations. Use `haveI := v.isMaximal`. Use `((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_` and prove the remaining obligations. Conclude with `⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩`.
-/
private theorem eventually_unr {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (χ : HChar F) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, χ.UnrAt (w.under (𝓞 F)) := by
  rw [Filter.eventually_cofinite]
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 F))
    fun v _ => ?_).subset fun w hw => hw
  haveI := v.isMaximal
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage
    (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩

/- English proof (translation)
Establish `hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (n - 1)`. Rewrite using `[← Complex.ofReal_mul, ← Real.rpow_add (by positivity), add_halves, ← Nat.cast_one (R := ℝ), ← Nat.cast_sub hn, Real.rpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression. Establish `h0 : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by positivity) _).ne'`.

Establish `ae : ∀ B : Multiset ℂˣ, algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ)` using `fun B => by simp [algSat]`. Simplify using `only [ae] at e e₁`. Use `clear ae`. Generalize the expression as in `(((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = c at *`. Establish `hs : σ c * σ c = c * c` using `by rw [← map_mul, hc, map_pow, map_natCast]`.

Establish `h1 : σ c ≠ 0` using `(map_ne_zero σ).2 h0`. Apply `Multiset.map_injective (f := fun x : ℂˣ => c⁻¹ * (x : ℂ)) (fun x y hxy => Units.ext (mul_left_cancel₀ (inv_ne_zero h0) hxy))` to reduce the goal to its premises. Establish `k1` using `congrArg (Multiset.map fun x : ℂ => x⁻¹) e₁`. Establish `k2` using `congrArg (Multiset.map fun x : ℂ => (c * c)⁻¹ * x * (σ z)⁻¹) e`. Establish `k3` using `congrArg (Multiset.map fun x : ℂˣ => σ (c⁻¹ * (x : ℂ))) h`.

Simplify using `only [Multiset.map_map, Function.comp_def] at k1 k2 k3 ⊢`. Use `(Multiset.map_congr rfl fun x _ => ?_).trans (k1.trans ((Multiset.map_congr rfl fun x _ => ?_).trans (k3.trans ((Multiset.map_congr rfl fun x _ => ?_).trans (k2.symm.trans (Multiset.map_congr rfl fun x _ => ?_))))))` and prove the remaining obligations. Simplify using `[mul_comm]`. Simplify using `[mul_comm]`. Rewrite using `[← hs]`.

Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, hz]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem dual_conj {n q : ℕ} (hn : 1 ≤ n) (hq : q ≠ 0) (σ : ℂ ≃+* ℂ) {B B₁ B' B₁' : Multiset ℂˣ} {z z' : ℂˣ}
    (hz : (z' : ℂ) = σ z) (h : B₁.map (·⁻¹) = B.map (· * z⁻¹)) (e : algSat n q B' = (algSat n q B).map σ)
    (e₁ : algSat n q B₁' = (algSat n q B₁).map σ) : B₁'.map (·⁻¹) = B'.map (· * z'⁻¹) := by
  have hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (n - 1) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity), add_halves, ← Nat.cast_one (R := ℝ), ← Nat.cast_sub hn,
      Real.rpow_natCast]
    push_cast
    rfl
  have h0 : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by positivity) _).ne'
  have ae : ∀ B : Multiset ℂˣ, algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) :=
    fun B => by simp [algSat]
  simp only [ae] at e e₁
  clear ae
  generalize (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = c at *
  have hs : σ c * σ c = c * c := by rw [← map_mul, hc, map_pow, map_natCast]
  have h1 : σ c ≠ 0 := (map_ne_zero σ).2 h0
  apply Multiset.map_injective (f := fun x : ℂˣ => c⁻¹ * (x : ℂ))
    (fun x y hxy => Units.ext (mul_left_cancel₀ (inv_ne_zero h0) hxy))
  have k1 := congrArg (Multiset.map fun x : ℂ => x⁻¹) e₁
  have k2 := congrArg (Multiset.map fun x : ℂ => (c * c)⁻¹ * x * (σ z)⁻¹) e
  have k3 := congrArg (Multiset.map fun x : ℂˣ => σ (c⁻¹ * (x : ℂ))) h
  simp only [Multiset.map_map, Function.comp_def] at k1 k2 k3 ⊢
  refine (Multiset.map_congr rfl fun x _ => ?_).trans (k1.trans ((Multiset.map_congr rfl fun x _ => ?_).trans (k3.trans
    ((Multiset.map_congr rfl fun x _ => ?_).trans (k2.symm.trans (Multiset.map_congr rfl fun x _ => ?_))))))
  · simp [mul_comm]
  · simp [mul_comm]
  · rw [← hs]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    field_simp
  · simp only [Units.val_mul, Units.val_inv_eq_inv_val, hz]
    field_simp

/- English proof (translation)
Introduce `P K _ _ _ hK n hn m hm M hM σ π ⟨hinf, ⟨χ, hpol⟩, hfix⟩`. Establish `hreg` using `regAlg_of_infOf hm hinf`. Take `⟨π', τ, τ', h1, h2, h3, h4⟩` from `P.conjC K n (by omega) π hreg σ`. Take `⟨hs, hs'⟩` from `sep_of_conj h1 h2 h3`. Establish `hsat : ∀ w B, (CG.mk π).HasSat w B → ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ` using `fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB`.

Use `⟨π', ⟨fun φ => ?_, ?_, hs.hasFixed hfix⟩, hsat⟩` and prove the remaining obligations. Establish `e : σ.toRingHom.comp (σ.symm.toRingHom.comp φ) = φ` using `RingHom.ext fun x => σ.apply_symm_apply _`. Conclude with `e ▸ h4 _ _ (hinf _)`. Take `⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ)` from `GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2`. Take `⟨r, wt, HT, H⟩` from `P.litN.aut.gal K (AlgebraicClosure K) 2 ι n (by omega) π _ hreg hpol`.

Take `⟨μ, ⟨-, art, a, -, ha, -⟩, -⟩` from `H.pol`. Establish `hF : Module.finrank ℚ (maximalRealSubfield K) = 1`. Establish `h1` using `Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K`. Rewrite `h1` using `[Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K]`. Use linear arithmetic over natural numbers and integers.

Take `⟨χ', hsg, hv⟩` from `UpperTheory.V.Br.charConj _ hF χ a ha σ`. Use `⟨χ', fun v => (hsg v).trans (hpol.sign v), UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse P.litN.aut.js.1 P.litN.aut.gk K n (by omega) π' _ ?_⟩` and prove the remaining obligations. Establish `hM1` using `eventually_notMem (K := K) hM`. Use `filter_upwards [eventually_unr (K := K) χ, hM1, (conjSrc_injective (IsCMField.complexConj K).toRingEquiv).tendsto_cofinite.eventually hM1] with w hw a1 a2`. Take `⟨B, hB⟩` from `satK P K n M π hfix w a1`.

Take `⟨B₁, hB₁⟩` from `satK P K n M π hfix (cPl w) a2`. Take `⟨B', hB', e⟩` from `hsat w B hB`. Take `⟨B₁', hB₁', e₁⟩` from `hsat _ B₁ hB₁`. Rewrite `e₁` using `[normV_cPl]`. Take `⟨e3, e4⟩` from `UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ w _ (normV_under w) hw`.

Take `⟨e5, e6⟩` from `UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ' w _ (normV_under w) (hv _ hw).1`. Use `⟨e5, B', B₁', hB', hB₁', dual_conj (by omega) (GlobalTheory.WeilDeligne.one_lt_normV w).ne_bot σ ?_ (UpperTheory.V.Br.satOfPol K n π _ hpol.dual w e3 B B₁ hB hB₁) e e₁⟩` and prove the remaining obligations. Rewrite using `[e4, e6, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, (hv _ hw).2]`.
-/
theorem UpperTheory.V.Br.conjPrime₂ :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.ConjP := by
  intro P K _ _ _ hK n hn m hm M hM σ π ⟨hinf, ⟨χ, hpol⟩, hfix⟩
  have hreg := regAlg_of_infOf hm hinf
  obtain ⟨π', τ, τ', h1, h2, h3, h4⟩ := P.conjC K n (by omega) π hreg σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  have hsat : ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ :=
    fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB
  refine ⟨π', ⟨fun φ => ?_, ?_, hs.hasFixed hfix⟩, hsat⟩
  · have e : σ.toRingHom.comp (σ.symm.toRingHom.comp φ) = φ := RingHom.ext fun x => σ.apply_symm_apply _
    exact e ▸ h4 _ _ (hinf _)
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨r, wt, HT, H⟩ := P.litN.aut.gal K (AlgebraicClosure K) 2 ι n (by omega) π _ hreg hpol
  obtain ⟨μ, ⟨-, art, a, -, ha, -⟩, -⟩ := H.pol
  have hF : Module.finrank ℚ (maximalRealSubfield K) = 1 := by
    have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K] at h1
    omega
  obtain ⟨χ', hsg, hv⟩ := UpperTheory.V.Br.charConj _ hF χ a ha σ
  refine ⟨χ', fun v => (hsg v).trans (hpol.sign v),
    UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse P.litN.aut.js.1 P.litN.aut.gk K n (by omega) π' _ ?_⟩
  have hM1 := eventually_notMem (K := K) hM
  filter_upwards [eventually_unr (K := K) χ, hM1,
    (conjSrc_injective (IsCMField.complexConj K).toRingEquiv).tendsto_cofinite.eventually hM1] with w hw a1 a2
  obtain ⟨B, hB⟩ := satK P K n M π hfix w a1
  obtain ⟨B₁, hB₁⟩ := satK P K n M π hfix (cPl w) a2
  obtain ⟨B', hB', e⟩ := hsat w B hB
  obtain ⟨B₁', hB₁', e₁⟩ := hsat _ B₁ hB₁
  rw [normV_cPl] at e₁
  obtain ⟨e3, e4⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ w _ (normV_under w) hw
  obtain ⟨e5, e6⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ' w _ (normV_under w) (hv _ hw).1
  refine ⟨e5, B', B₁', hB', hB₁', dual_conj (by omega) (GlobalTheory.WeilDeligne.one_lt_normV w).ne_bot σ ?_
    (UpperTheory.V.Br.satOfPol K n π _ hpol.dual w e3 B B₁ hB hB₁) e e₁⟩
  rw [e4, e6, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, (hv _ hw).2]
