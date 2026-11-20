import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.GoodLat
import Development.WeilBound.ThetaLifts.TowerModels.PlaneCodiff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes

noncomputable section

open scoped TensorProduct Matrix Topology nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `htop : differentIdeal (𝓞 F) (𝓞 E) = ⊤`. Assume the negation of the conclusion as `hn`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hn`.

Conclude with `(not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).2 inferInstance (Ideal.dvd_iff_le.2 hle)`. Establish `hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1`. Establish `e` using `coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)`. Rewrite `e` using `[htop, FractionalIdeal.coeIdeal_top]`. Conclude with `inv_eq_one.mp e.symm`.

Set `J : Ideal (𝓞 F)` to `LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))`. Distinguish the cases in `hJ : J = ⊤`. Establish `h1 : (1 : 𝓞 F) ∈ J` using `hJ ▸ Submodule.mem_top`. Take `⟨b, hb⟩` from `h1`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Use `Algebra.algebraMap_intTrace (K := F) (L := E) (A := 𝓞 F) b` as an intermediate fact. Rewrite `this` using `[hb, map_one]`. Conclude with `this.symm`. It suffices to derive a contradiction. Take `⟨p, hp, hJp⟩` from `Ideal.exists_le_maximal J hJ`.

Establish `hp0 : p ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField F)`. Take `⟨t, ht, ht1⟩` from `FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hp0 hp.ne_top`. Establish `hmem : algebraMap F E t ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)`. Rewrite using `[FractionalIdeal.mem_dual (by simp)]`. Introduce `a ha`.

Take `⟨b, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Establish `hb : Algebra.intTrace (𝓞 F) (𝓞 E) b ∈ p` using `hJp ⟨b, rfl⟩`. Establish `hp0' : (p : FractionalIdeal (𝓞 F)⁰ F) ≠ 0`. Rewrite using `[ne_eq, FractionalIdeal.coeIdeal_eq_zero]` and apply the resulting hypothesis. Establish `h2 : t * algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) b) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F)`.

Use `FractionalIdeal.mul_mem_mul ht ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hb, rfl⟩)` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel₀ hp0']`. Then use the resulting hypothesis. Take `⟨c, hc⟩` from `(FractionalIdeal.mem_one_iff _).1 h2`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, Algebra.traceForm_apply, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, Algebra.algebraMap_intTrace (L := E)]`.

Rewrite `hmem` using `[hd]`. Take `⟨c, hc⟩` from `(FractionalIdeal.mem_one_iff _).1 hmem`. Establish `hint : IsIntegral ℤ t`. Rewrite using `[← isIntegral_algebraMap_iff (algebraMap F E).injective, ← hc]`. Conclude with `RingOfIntegers.isIntegral_coe c`.

Conclude with `ht1 ((FractionalIdeal.mem_one_iff _).2 ⟨⟨t, hint⟩, rfl⟩)`.
-/
theorem exists_trace_one (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) : ∃ b : 𝓞 E, Algebra.trace F E (b : E) = 1 := by
  classical
  haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have htop : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra hn
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hn
    exact (not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).2 inferInstance (Ideal.dvd_iff_le.2 hle)
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have e := coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)
    rw [htop, FractionalIdeal.coeIdeal_top] at e
    exact inv_eq_one.mp e.symm
  let J : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))
  by_cases hJ : J = ⊤
  · have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := h1
    refine ⟨b, ?_⟩
    have := Algebra.algebraMap_intTrace (K := F) (L := E) (A := 𝓞 F) b
    rw [hb, map_one] at this
    exact this.symm
  · exfalso
    obtain ⟨p, hp, hJp⟩ := Ideal.exists_le_maximal J hJ
    have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField F)
    obtain ⟨t, ht, ht1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hp0 hp.ne_top
    have hmem : algebraMap F E t ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual (by simp)]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      have hb : Algebra.intTrace (𝓞 F) (𝓞 E) b ∈ p := hJp ⟨b, rfl⟩
      have hp0' : (p : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
      have h2 : t * algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) b) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        have := FractionalIdeal.mul_mem_mul ht ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hb, rfl⟩)
        rwa [inv_mul_cancel₀ hp0'] at this
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h2
      refine ⟨c, ?_⟩
      rw [hc, Algebra.traceForm_apply, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul,
        Algebra.algebraMap_intTrace (L := E)]
    rw [hd] at hmem
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
    have hint : IsIntegral ℤ t := by
      rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, ← hc]
      exact RingOfIntegers.isIntegral_coe c
    exact ht1 ((FractionalIdeal.mem_one_iff _).2 ⟨⟨t, hint⟩, rfl⟩)

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_trace_one hu`. Use `⟨b, RingOfIntegers.ext ?_⟩` and prove the remaining obligations. Use `show (b : E) + σ b = 1`. Rewrite using `[← PositivityTheory.ThKG.Tow.Pln.trace_cm h, hb, map_one]`.
-/
theorem exists_w (h : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) : ∃ w : 𝓞 E, w + sgOF σ w = 1 := by
  obtain ⟨b, hb⟩ := exists_trace_one hu
  refine ⟨b, RingOfIntegers.ext ?_⟩
  show (b : E) + σ b = 1
  rw [← PositivityTheory.ThKG.Tow.Pln.trace_cm h, hb, map_one]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Establish `h1` using `h.2.2.2 (τ.comp (g : E →+* E)) x`. Establish `h2` using `h.2.2.2 τ (g x)`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe] at h1`.

Rewrite using `[h2]`. Conclude with `h1`.
-/
theorem sg_comm (h : IsCMExt F E σ) (g : E ≃ₐ[ℚ] E) (x : E) : g (σ x) = σ (g x) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  have h1 := h.2.2.2 (τ.comp (g : E →+* E)) x
  have h2 := h.2.2.2 τ (g x)
  simp only [RingHom.comp_apply, RingHom.coe_coe] at h1
  rw [h2]
  exact h1

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem sg_sg (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Use `h.2.1` as an intermediate fact. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `IsTotallyComplex.complexEmbedding_not_isReal τ ?_` and prove the remaining obligations.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `y`. Use `h.2.2.2 τ y` as an intermediate fact. Rewrite `this` using `[hn y]`. Simplify using `using this.symm`.
-/
theorem sg_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  have := h.2.1
  by_contra hn
  push Not at hn
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hn y] at this
  simpa using this.symm

/- English proof (translation)
Introduce `Q hQ hqQ r hr`. Establish `hmax : (Ideal.span {(q : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible`. Establish `key : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → P.LiesOver (Ideal.span {(q : ℤ)})` using `fun P hP h => ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by`. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]`. Simplify using `using h)⟩`.

Use `haveI := key P hP.isPrime hqP`. Use `haveI := key Q hQ.isPrime hqQ`. Take `⟨g, rfl⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P Q (E ≃ₐ[ℚ] E)`. Rewrite `hr`, the goal using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Establish `e : g⁻¹ • sgOF σ r = sgOF σ (g⁻¹ • r)` using `RingOfIntegers.ext (sg_comm h g⁻¹ r)`.

Rewrite using `[e]`. Conclude with `hfix _ hr`.
-/
theorem inertQ_of_fix (h : IsCMExt F E σ) [IsGalois ℚ E] {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 E) ∈ P) (hfix : ∀ r ∈ P, sgOF σ r ∈ P) : InertQF σ q := by
  intro Q hQ hqQ r hr
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have key : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → P.LiesOver (Ideal.span {(q : ℤ)}) :=
    fun P hP h => ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
      simpa using h)⟩
  haveI := key P hP.isPrime hqP
  haveI := key Q hQ.isPrime hqQ
  obtain ⟨g, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hr ⊢
  have e : g⁻¹ • sgOF σ r = sgOF σ (g⁻¹ • r) := RingOfIntegers.ext (sg_comm h g⁻¹ r)
  rw [e]
  exact hfix _ hr

/- English proof (translation)
Establish `: Algebra.IsQuadraticExtension F E` using `{ finrank_eq_two' := h.2.2.1 }`. Establish `: IsGalois F E` using `inferInstance`. Establish `hσ` using `sg_sg h`. Establish `: (P.under (𝓞 F)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Establish `hcard` using `Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) (P.under (𝓞 F)) P`.

Rewrite `hcard` using `[Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P (E ≃ₐ[F] E), Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]`. Set `s : E ≃ₐ[F] E` to `AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)`. Establish `hs1 : s ≠ 1` using `fun hs => by`. Take `⟨x, hx⟩` from `sg_ne h`. Conclude with `hx (congrArg (fun t : E ≃ₐ[F] E => t x) hs)`.

Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Establish `hs : s ∈ P.inertia (E ≃ₐ[F] E)` using `AddSubgroup.mem_inertia.2 fun x => hn x`. Rewrite `hs` using `[Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot]`. Conclude with `hs1 hs`.
-/
theorem exists_move (h : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) {P : Ideal (𝓞 E)}
    (hP : P.IsMaximal) : ∃ r, sgOF σ r - r ∉ P := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have hσ := sg_sg h
  have : (P.under (𝓞 F)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) (P.under (𝓞 F)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P (E ≃ₐ[F] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcard
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => by
    obtain ⟨x, hx⟩ := sg_ne h
    exact hx (congrArg (fun t : E ≃ₐ[F] E => t x) hs)
  by_contra hn
  push Not at hn
  have hs : s ∈ P.inertia (E ≃ₐ[F] E) := AddSubgroup.mem_inertia.2 fun x => hn x
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact hs1 hs

/- English proof (translation)
Take `⟨lam, h0, h1, h2⟩` from `GlobalTheory.FinWeil.exists_lam (InertQF σ) fun q => (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E)`. Use `⟨lam, ⟨h0, fun P hP _ => ?_⟩, h2⟩` and prove the remaining obligations. Take `⟨q, hq, hqP, hf, hc⟩` from `GlobalTheory.FinWeil.exists_card_eq_pow P hP`. Establish `hsq : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n` using `fun n => by`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]`.

Use `⟨?_, fun hfix => ⟨?_, exists_move h hu hP⟩⟩` and prove the remaining obligations. Rewrite using `[hc]`. Distinguish the cases in `hI : InertQF σ q`. Rewrite using `[h1 q hq hf hI, neg_sq, hsq]`. Rewrite using `[h2 _ (pow_ne_zero _ hq.ne_zero) fun p hp hIp hd => hI ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd) ▸ hIp), hsq]`.

Rewrite using `[hc]`. Conclude with `h1 q hq hf (inertQ_of_fix h hP hq hqP hfix)`.
-/
theorem exists_goodNorm (h : IsCMExt F E σ) [IsGalois ℚ E] (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) :
    ∃ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam ∧
      ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  classical
  obtain ⟨lam, h0, h1, h2⟩ := GlobalTheory.FinWeil.exists_lam (InertQF σ)
    fun q => (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E)
  refine ⟨lam, ⟨h0, fun P hP _ => ?_⟩, h2⟩
  obtain ⟨q, hq, hqP, hf, hc⟩ := GlobalTheory.FinWeil.exists_card_eq_pow P hP
  have hsq : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := fun n => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  refine ⟨?_, fun hfix => ⟨?_, exists_move h hu hP⟩⟩
  · rw [hc]
    by_cases hI : InertQF σ q
    · rw [h1 q hq hf hI, neg_sq, hsq]
    · rw [h2 _ (pow_ne_zero _ hq.ne_zero) fun p hp hIp hd => hI
        ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd) ▸ hIp), hsq]
  · rw [hc]
    exact h1 q hq hf (inertQ_of_fix h hP hq hqP hfix)

end PositivityTheory.ThKW.LatB

end
