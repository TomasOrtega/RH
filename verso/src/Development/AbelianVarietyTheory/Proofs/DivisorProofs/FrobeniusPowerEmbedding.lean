import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfInertCore

open NumberField IsDedekindDomain IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

set_option linter.style.haveILetI false

namespace GlobalTheory.FrobEmb

/- English proof (translation)
Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Establish `hpI : (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ`. Take `⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E))` from `inferInstance`. Establish `hne : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) (by simpa using hp.ne_zero) P`. Use `haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne`.

Take `⟨σ, hσ⟩` from `IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P`. Use `⟨σ, fun Q _ _ => ?_⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)`. Use `hσ.conj t` as an intermediate fact. Rewrite `this` using `[hc t σ, mul_inv_cancel_right]`. Then use the resulting hypothesis.
-/
theorem exists_frob_all (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (hc : ∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) (p : ℕ) (hp : p.Prime) :
    ∃ σ : E ≃ₐ[ℚ] E, ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ σ P := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)) := inferInstance
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(p : ℤ)}) (by simpa using hp.ne_zero) P
  haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P
  refine ⟨σ, fun Q _ _ => ?_⟩
  obtain ⟨t, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have := hσ.conj t
  rwa [hc t σ, mul_inv_cancel_right] at this

/- English proof (translation)
Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp.out`. Establish `hirr : Irreducible (p : WittVector p k)` using `WittVector.irreducible p`. Establish `hm : ∀ y : WittVector p k, y ∈ maximalIdeal (WittVector p k) ↔ WittVector.constantCoeff y = 0` using `fun y => by`. Rewrite using `[hirr.maximalIdeal_eq, ← RingHom.mem_ker, WittVector.ker_constantCoeff]`. Take `⟨g, hg⟩` from `GO.PlWitt.exists_intHom (O := WittVector p k) τ`.

Establish `h : (p : 𝓞 E) ∈ (maximalIdeal (WittVector p k)).comap g`. Rewrite using `[Ideal.mem_comap, map_natCast, hm, map_natCast, CharP.cast_eq_zero]`. Set `Q : HeightOneSpectrum (𝓞 E)` to `⟨(maximalIdeal (WittVector p k)).comap g, inferInstance, fun e => by`. Rewrite `h` using `[e, Ideal.mem_bot]`. Conclude with `hp.out.ne_zero (Nat.cast_eq_zero.1 h)⟩`.

Establish `hQ : ∀ y, y ∈ Q.asIdeal ↔ WittVector.constantCoeff (g y) = 0` using `fun y => hm _`. Use `haveI hl : Q.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by haveI : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p`. Use `this.eq_of_le (Ideal.comap_ne_top _ Q.isPrime.ne_top) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]`. Conclude with `h⟩`.

Use `haveI : Algebra.IsUnramifiedAt ℤ Q.asIdeal := (NumberField.not_dvd_discr_iff_forall_liesOver E (𝓞 E) hpZ).1 (fun hd => hu (Int.natCast_dvd.1 hd)) Q.asIdeal Q.isMaximal hl`. Establish `e : ∀ y : WittVector p k, WittVector.constantCoeff (WittVector.frobenius y) = WittVector.constantCoeff y ^ p` using `fun y => WittVector.coeff_frobenius_charP p y 0`. Set `s : 𝓞 E →+* 𝓞 E` to `(MulSemiringAction.toAlgHom ℤ (𝓞 E) σ).toRingHom`. Establish `key : WittVector.frobenius.comp g = g.comp s` using `GO.PlWitt.eq_of_cong Q _ _ (fun y => by rw [hQ, hm, RingHom.comp_apply, e, pow_eq_zero_iff hp.out.ne_zero]) fun y => by`. Establish `h1` using `hσ Q.asIdeal y`.

Rewrite `h1` using `[← Ideal.LiesOver.over (P := Q.asIdeal) (p := Ideal.span {(p : ℤ)}), Int.card_ideal_quot, hQ, map_sub, map_sub, map_pow, map_pow, sub_eq_zero]`. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff, hm, map_sub, RingHom.comp_apply, e, sub_eq_zero]`. Conclude with `h1.symm`. Establish `h2 : (WittVector.FractionRing.frobenius p k : _ →+* _).comp τ = τ.comp (σ : E →+* E)` using `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun y => by`. Establish `h3` using `congrArg (algebraMap _ (FractionRing (WittVector p k))) (RingHom.congr_fun key y)`.

Rewrite `h3` using `[RingHom.comp_apply, RingHom.comp_apply, ← SqrtUnif.fractionRing_frobenius_algebraMap, hg, hg]`. Conclude with `h3)`. Conclude with `RingHom.congr_fun h2 x`.
-/
theorem frobenius_comp (E : Type) [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime]
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (hu : ¬ p ∣ (discr E).natAbs) (σ : E ≃ₐ[ℚ] E)
    (hσ : ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ σ P)
    (τ : E →+* FractionRing (WittVector p k)) (x : E) :
    WittVector.FractionRing.frobenius p k (τ x) = τ (σ x) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.out
  have hirr : Irreducible (p : WittVector p k) := WittVector.irreducible p
  have hm : ∀ y : WittVector p k, y ∈ maximalIdeal (WittVector p k) ↔ WittVector.constantCoeff y = 0 := fun y => by
    rw [hirr.maximalIdeal_eq, ← RingHom.mem_ker, WittVector.ker_constantCoeff]
  obtain ⟨g, hg⟩ := GO.PlWitt.exists_intHom (O := WittVector p k) τ
  have h : (p : 𝓞 E) ∈ (maximalIdeal (WittVector p k)).comap g := by
    rw [Ideal.mem_comap, map_natCast, hm, map_natCast, CharP.cast_eq_zero]
  let Q : HeightOneSpectrum (𝓞 E) := ⟨(maximalIdeal (WittVector p k)).comap g, inferInstance, fun e => by
    rw [e, Ideal.mem_bot] at h
    exact hp.out.ne_zero (Nat.cast_eq_zero.1 h)⟩
  have hQ : ∀ y, y ∈ Q.asIdeal ↔ WittVector.constantCoeff (g y) = 0 := fun y => hm _
  haveI hl : Q.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    refine this.eq_of_le (Ideal.comap_ne_top _ Q.isPrime.ne_top) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact h⟩
  haveI : Algebra.IsUnramifiedAt ℤ Q.asIdeal :=
    (NumberField.not_dvd_discr_iff_forall_liesOver E (𝓞 E) hpZ).1
      (fun hd => hu (Int.natCast_dvd.1 hd)) Q.asIdeal Q.isMaximal hl
  have e : ∀ y : WittVector p k, WittVector.constantCoeff (WittVector.frobenius y) = WittVector.constantCoeff y ^ p :=
    fun y => WittVector.coeff_frobenius_charP p y 0
  let s : 𝓞 E →+* 𝓞 E := (MulSemiringAction.toAlgHom ℤ (𝓞 E) σ).toRingHom
  have key : WittVector.frobenius.comp g = g.comp s := GO.PlWitt.eq_of_cong Q _ _
    (fun y => by rw [hQ, hm, RingHom.comp_apply, e, pow_eq_zero_iff hp.out.ne_zero]) fun y => by
      have h1 := hσ Q.asIdeal y
      rw [← Ideal.LiesOver.over (P := Q.asIdeal) (p := Ideal.span {(p : ℤ)}), Int.card_ideal_quot, hQ, map_sub,
        map_sub, map_pow, map_pow, sub_eq_zero] at h1
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, hm, map_sub, RingHom.comp_apply, e, sub_eq_zero]
      exact h1.symm
  have h2 : (WittVector.FractionRing.frobenius p k : _ →+* _).comp τ = τ.comp (σ : E →+* E) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun y => by
      have h3 := congrArg (algebraMap _ (FractionRing (WittVector p k))) (RingHom.congr_fun key y)
      rw [RingHom.comp_apply, RingHom.comp_apply, ← SqrtUnif.fractionRing_frobenius_algebraMap, hg, hg] at h3
      exact h3)
  exact RingHom.congr_fun h2 x

/- English proof (translation)
Use `haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois`. Establish `h : ∃ g : D.R.GG, ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf g) P`. Take `⟨σ, hσ⟩` from `exists_frob_all D.host.E (fun a b => (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])) p hp`. Take `⟨g, hg⟩` from `(D.host.gal).symm.surjective σ`. Establish `hg' : D.host.sigmaOf g = σ` using `hg`.

Conclude with `⟨g, hg' ▸ hσ⟩`. Unfold `frobG`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec P`.
-/
theorem isArithFrobAt_frobG (D : D7) (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : IsArithFrobAt ℤ (D.host.sigmaOf (frobG D p)) P := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have h : ∃ g : D.R.GG, ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
      [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf g) P := by
    obtain ⟨σ, hσ⟩ := exists_frob_all D.host.E (fun a b =>
      (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])) p hp
    obtain ⟨g, hg⟩ := (D.host.gal).symm.surjective σ
    have hg' : D.host.sigmaOf g = σ := hg
    exact ⟨g, hg' ▸ hσ⟩
  unfold frobG
  rw [dif_pos h]
  exact h.choose_spec P

/- English proof (translation)
Introduce `D p hp hu τ`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Unfold `phiPow`. Rewrite using `[pow_one]`. Conclude with `frobenius_comp D.host.E p _ hu _ (fun P _ _ => isArithFrobAt_frobG D p hp.out P) τ x`.
-/
theorem phiPow_one_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime], UnramE D p → ∀ τ : Emb D p,
    phiPow D 1 τ = τ.comp (D.host.sigmaOf (frobG D p) : D.host.E →+* D.host.E) := by
  intro D p hp hu τ
  refine RingHom.ext fun x => ?_
  unfold phiPow
  rw [pow_one]
  exact frobenius_comp D.host.E p _ hu _ (fun P _ _ => isArithFrobAt_frobG D p hp.out P) τ x

end GlobalTheory.FrobEmb
