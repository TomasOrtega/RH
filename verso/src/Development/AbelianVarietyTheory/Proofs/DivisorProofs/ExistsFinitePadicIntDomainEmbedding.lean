import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteOfFiniteQuotMapOfIsPrecomplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

open IsLocalRing

namespace GlobalTheory.CompletionEmbed

variable (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsLocalRing C]

noncomputable def levelMap (hpm : (p : C) ∈ maximalIdeal C) (n : ℕ) :
    ℤ_[p] →+* C ⧸ maximalIdeal C ^ n :=
  have h : ((p ^ n : ℕ) : C ⧸ maximalIdeal C ^ n) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal C ^ n)), Ideal.Quotient.eq_zero_iff_mem,
      Nat.cast_pow]
    exact Ideal.pow_mem_pow hpm n
  (ZMod.castHom (ringChar.dvd h) (C ⧸ maximalIdeal C ^ n)).comp (PadicInt.toZModPow n)

/- English proof (translation)
Unfold `levelMap`. Rewrite using `[← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]`. Use `congr 1`. Conclude with `Subsingleton.elim _ _`.
-/
theorem levelMap_compat (hpm : (p : C) ∈ maximalIdeal C) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal C) hle).comp (levelMap p C hpm n) =
      levelMap p C hpm m := by
  unfold levelMap
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact Subsingleton.elim _ _

noncomputable def toCompletion (hpm : (p : C) ∈ maximalIdeal C) :
    ℤ_[p] →+* AdicCompletion (maximalIdeal C) C :=
  AdicCompletion.liftRingHom (maximalIdeal C) (levelMap p C hpm)
    (fun hle => levelMap_compat p C hpm hle)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `hmem : x ∈ ⨅ n : ℕ, maximalIdeal C ^ n`. Rewrite using `[Submodule.mem_iInf]`. Introduce `n`.

Use `congrArg (AdicCompletion.evalₐ (maximalIdeal C) n) hx` as an intermediate fact. Rewrite `this` using `[map_zero]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `using this`. Rewrite `hmem` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal C).ne_top]`.

Conclude with `hmem`.
-/
theorem algebraMap_injective [IsNoetherianRing C] :
    Function.Injective (algebraMap C (AdicCompletion (maximalIdeal C) C)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ ⨅ n : ℕ, maximalIdeal C ^ n := by
    rw [Submodule.mem_iInf]
    intro n
    have := congrArg (AdicCompletion.evalₐ (maximalIdeal C) n) hx
    rw [map_zero] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal C).ne_top] at hmem
  exact hmem

/- English proof (translation)
Use `Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)` and prove the remaining obligations. Rewrite using `[Ideal.radical_eq_sInf]`. Use `le_sInf fun Q ⟨hle, hQ⟩ => ?_` and prove the remaining obligations. Establish `hQ0 : Q ≠ ⊥` using `fun h => hp0 (by`. Use `hle (Ideal.mem_span_singleton_self _)` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `(Ideal.mem_bot).mp this)`. Rewrite using `[hprime Q hQ hQ0]`.
-/
theorem exists_pow_le_span [IsNoetherianRing C] (hp0 : (p : C) ≠ 0)
    (hprime : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) :
    ∃ N : ℕ, maximalIdeal C ^ N ≤ Ideal.span {(p : C)} := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun Q ⟨hle, hQ⟩ => ?_
  have hQ0 : Q ≠ ⊥ := fun h => hp0 (by
    have := hle (Ideal.mem_span_singleton_self _)
    rw [h] at this
    exact (Ideal.mem_bot).mp this)
  rw [hprime Q hQ hQ0]

/- English proof (translation)
Use `set A := AdicCompletion (maximalIdeal C) C`. Establish `fg : (maximalIdeal C).FG` using `IsNoetherian.noetherian _`. Use `haveI : Finite (C ⧸ maximalIdeal C) := ‹Finite (ResidueField C)›`. Use `haveI : Finite (A ⧸ (maximalIdeal C).map (algebraMap C A)) := by`. Establish `h` using `Finite.of_injective _ (RingHom.kerLift_injective (AdicCompletion.evalOneₐ (maximalIdeal C)).toRingHom)`.

Rewrite `h` using `[AdicCompletion.ker_evalOneₐ_eq_map _ fg]`. Conclude with `h`. Take `⟨N, hN⟩` from `exists_pow_le_span p C hp0 hprime`. Use `haveI : Finite (A ⧸ ((maximalIdeal C).map (algebraMap C A)) ^ N) := Ideal.finite_quotient_pow (fg.map _) N`. Establish `hle : ((maximalIdeal C).map (algebraMap C A)) ^ N ≤ Ideal.span {(p : A)}`.

Rewrite using `[← Ideal.map_pow]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)`.
-/
theorem finite_quot_span [IsNoetherianRing C] [Finite (ResidueField C)] (hp0 : (p : C) ≠ 0)
    (hprime : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) :
    Finite (AdicCompletion (maximalIdeal C) C ⧸
      Ideal.span {(p : AdicCompletion (maximalIdeal C) C)}) := by
  set A := AdicCompletion (maximalIdeal C) C
  have fg : (maximalIdeal C).FG := IsNoetherian.noetherian _
  haveI : Finite (C ⧸ maximalIdeal C) := ‹Finite (ResidueField C)›
  haveI : Finite (A ⧸ (maximalIdeal C).map (algebraMap C A)) := by
    have h := Finite.of_injective _
      (RingHom.kerLift_injective (AdicCompletion.evalOneₐ (maximalIdeal C)).toRingHom)
    rw [AdicCompletion.ker_evalOneₐ_eq_map _ fg] at h
    exact h
  obtain ⟨N, hN⟩ := exists_pow_le_span p C hp0 hprime
  haveI : Finite (A ⧸ ((maximalIdeal C).map (algebraMap C A)) ^ N) :=
    Ideal.finite_quotient_pow (fg.map _) N
  have hle : ((maximalIdeal C).map (algebraMap C A)) ^ N ≤ Ideal.span {(p : A)} := by
    rw [← Ideal.map_pow]
    calc _ ≤ (Ideal.span {(p : C)}).map (algebraMap C A) := Ideal.map_mono hN
      _ = _ := by rw [Ideal.map_span, Set.image_singleton, map_natCast]
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)

end GlobalTheory.CompletionEmbed

open IsLocalRing GlobalTheory.CompletionEmbed in

/- English proof (translation)
Introduce `p _ C _ _ _ _ hfin hp0 hpm hprime`. Use `set A := AdicCompletion (maximalIdeal C) C`. Use `haveI : IsNoetherianRing A := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _`. Use `letI : Algebra ℤ_[p] A := (toCompletion p C hpm).toAlgebra`. Establish `hJ : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A) = Ideal.span {(p : A)}`.

Rewrite using `[PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]`. Use `haveI : Finite (A ⧸ Ideal.span {(p : A)}) := finite_quot_span p C hp0 hprime`. Establish `hne : Ideal.span {(p : A)} ≠ ⊤`. Introduce `h`. Establish `hu : IsUnit (p : A)` using `Ideal.span_singleton_eq_top.mp h`.

Establish `hu'` using `hu.map (AdicCompletion.evalOneₐ (maximalIdeal C))`. Rewrite `hu'` using `[map_natCast, ← map_natCast (Ideal.Quotient.mk (maximalIdeal C)), Ideal.Quotient.eq_zero_iff_mem.mpr hpm]`. Conclude with `not_isUnit_zero hu'`. Use `haveI : Module.Finite ℤ_[p] A := by`. Use `GlobalTheory.finite_of_finite_quot_map_of_isPrecomplete ℤ_[p] A (maximalIdeal ℤ_[p]) ?_ ?_` and prove the remaining obligations.

Rewrite using `[hJ]`. Conclude with `hne`. Rewrite using `[hJ]`. Conclude with `Module.Finite.of_finite`. Establish `hnil : ¬ IsNilpotent (p : A)`.

Introduce and unpack `⟨n, hn⟩`. Establish `h : algebraMap C A ((p : C) ^ n) = 0` using `by rw [map_pow, map_natCast]; exact hn`. Establish `h3` using `(injective_iff_map_eq_zero _).mp (algebraMap_injective C) _ h`. Conclude with `hp0 (IsNilpotent.eq_zero ⟨n, h3⟩)`. Choose the witnesses or unpack the hypotheses as in `⟨Q, hQ, hpQ⟩ : ∃ Q : Ideal A, Q.IsPrime ∧ (p : A) ∉ Q := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hnil (nilpotent_iff_mem_prime.mpr h)`. Use `haveI := hQ`. Use `⟨A ⧸ Q, inferInstance, inferInstance, inferInstance, ?_, (Ideal.Quotient.mk Q).comp (algebraMap C A), ?_⟩` and prove the remaining obligations.

Conclude with `Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] Q).toLinearMap (Ideal.Quotient.mkₐ_surjective ℤ_[p] Q)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `hbot : Q.comap (algebraMap C A) = ⊥`. Assume the negation of the conclusion as `hb`.

Establish `h1` using `hprime _ (Ideal.comap_isPrime _ _) hb`. Apply `hpQ` to reduce the goal to its premises. Establish `h2 : (p : C) ∈ Q.comap (algebraMap C A)`. Rewrite using `[h1]`. Conclude with `hpm`.

Rewrite `h2` using `[Ideal.mem_comap, map_natCast]`. Conclude with `h2`. Establish `hx' : x ∈ Q.comap (algebraMap C A)`. Rewrite using `[Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hx`.

Rewrite `hx'` using `[hbot]`. Conclude with `(Ideal.mem_bot).mp hx'`.
-/
theorem GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C]
      [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C →
      (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) →
      ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D),
        Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  intro p _ C _ _ _ _ hfin hp0 hpm hprime
  set A := AdicCompletion (maximalIdeal C) C
  haveI : IsNoetherianRing A := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _
  letI : Algebra ℤ_[p] A := (toCompletion p C hpm).toAlgebra
  have hJ : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A) = Ideal.span {(p : A)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  haveI : Finite (A ⧸ Ideal.span {(p : A)}) := finite_quot_span p C hp0 hprime
  have hne : Ideal.span {(p : A)} ≠ ⊤ := by
    intro h
    have hu : IsUnit (p : A) := Ideal.span_singleton_eq_top.mp h
    have hu' := hu.map (AdicCompletion.evalOneₐ (maximalIdeal C))
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk (maximalIdeal C)),
      Ideal.Quotient.eq_zero_iff_mem.mpr hpm] at hu'
    exact not_isUnit_zero hu'
  haveI : Module.Finite ℤ_[p] A := by
    refine GlobalTheory.finite_of_finite_quot_map_of_isPrecomplete ℤ_[p] A (maximalIdeal ℤ_[p]) ?_ ?_
    · rw [hJ]; exact hne
    · rw [hJ]; exact Module.Finite.of_finite
  have hnil : ¬ IsNilpotent (p : A) := by
    rintro ⟨n, hn⟩
    have h : algebraMap C A ((p : C) ^ n) = 0 := by rw [map_pow, map_natCast]; exact hn
    have h3 := (injective_iff_map_eq_zero _).mp (algebraMap_injective C) _ h
    exact hp0 (IsNilpotent.eq_zero ⟨n, h3⟩)
  obtain ⟨Q, hQ, hpQ⟩ : ∃ Q : Ideal A, Q.IsPrime ∧ (p : A) ∉ Q := by
    by_contra h
    push_neg at h
    exact hnil (nilpotent_iff_mem_prime.mpr h)
  haveI := hQ
  refine ⟨A ⧸ Q, inferInstance, inferInstance, inferInstance, ?_,
    (Ideal.Quotient.mk Q).comp (algebraMap C A), ?_⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] Q).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[p] Q)
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hbot : Q.comap (algebraMap C A) = ⊥ := by
      by_contra hb
      have h1 := hprime _ (Ideal.comap_isPrime _ _) hb
      apply hpQ
      have h2 : (p : C) ∈ Q.comap (algebraMap C A) := by
        rw [h1]; exact hpm
      rw [Ideal.mem_comap, map_natCast] at h2
      exact h2
    have hx' : x ∈ Q.comap (algebraMap C A) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    rw [hbot] at hx'
    exact (Ideal.mem_bot).mp hx'
