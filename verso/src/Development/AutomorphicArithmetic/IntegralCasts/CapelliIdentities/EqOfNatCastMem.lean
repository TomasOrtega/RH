import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yza3.Pl :
    Type :=
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)

noncomputable def UpperTheory.Reformulated.B.Yza3.normV.{u_1} :
    {F : Type u_1} → [inst : Field F] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℕ :=
    fun {F : Type u_1} [Field F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      Nat.card (NumberField.RingOfIntegers F ⧸ v.asIdeal)

namespace UpperTheory.Reformulated.B.Yza3

open NumberField in
/- English proof (translation)
Set `e : 𝓞 ℚ ≃+* ℤ` to `Rat.ringOfIntegersEquiv`. Establish `hprime : v.asIdeal.IsPrime` using `v.isPrime`. Take `⟨g, hg⟩ : ∃ g : 𝓞 ℚ, v.asIdeal = Ideal.span {g}` from `haveI : IsPrincipalIdealRing (𝓞 ℚ) := IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective (IsPrincipalIdealRing.principal v.asIdeal).principal`. Establish `hg0 : g ≠ 0`. Introduce and unpack `rfl`.

Conclude with `v.ne_bot (by simpa using hg)`. Establish `hgp : Prime g`. Rewrite using `[← Ideal.span_singleton_prime hg0, ← hg]`. Conclude with `hprime`. Establish `hep : Prime (e g)` using `(MulEquiv.prime_iff e.toMulEquiv).2 hgp`.

Use `⟨(e g).natAbs, Int.prime_iff_natAbs_prime.1 hep, ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Establish `hassoc : Associated (e g) (((e g).natAbs : ℕ) : ℤ)` using `(Int.associated_natAbs _)`. Establish `: Associated g (((e g).natAbs : ℕ) : 𝓞 ℚ)`. Establish `h2` using `hassoc.map e.symm.toMonoidHom`.

Generalize the expression as in `(e g).natAbs = n at h2 ⊢`. Establish `h3 : e.symm.toMonoidHom (e g) = g` using `e.symm_apply_apply g`. Establish `h4 : e.symm.toMonoidHom ((n : ℕ) : ℤ) = (n : 𝓞 ℚ)` using `map_natCast e.symm n`. Rewrite `h2` using `[h3, h4]`. Then use the resulting hypothesis. Conclude with `Ideal.span_singleton_eq_span_singleton.2 this`.
-/
private lemma exists_prime_gen (v : Pl) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  classical
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hprime : v.asIdeal.IsPrime := v.isPrime
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 ℚ, v.asIdeal = Ideal.span {g} :=
    haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
      IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
    (IsPrincipalIdealRing.principal v.asIdeal).principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by simpa using hg)
  have hgp : Prime g := by
    rw [← Ideal.span_singleton_prime hg0, ← hg]
    exact hprime
  have hep : Prime (e g) := (MulEquiv.prime_iff e.toMulEquiv).2 hgp
  refine ⟨(e g).natAbs, Int.prime_iff_natAbs_prime.1 hep, ?_⟩
  rw [hg]
  have hassoc : Associated (e g) (((e g).natAbs : ℕ) : ℤ) := (Int.associated_natAbs _)
  have : Associated g (((e g).natAbs : ℕ) : 𝓞 ℚ) := by
    have h2 := hassoc.map e.symm.toMonoidHom
    generalize (e g).natAbs = n at h2 ⊢
    have h3 : e.symm.toMonoidHom (e g) = g := e.symm_apply_apply g
    have h4 : e.symm.toMonoidHom ((n : ℕ) : ℤ) = (n : 𝓞 ℚ) := map_natCast e.symm n
    rwa [h3, h4] at h2
  exact Ideal.span_singleton_eq_span_singleton.2 this

open NumberField in
/- English proof (translation)
Establish `key : ∀ u : Pl, (p : 𝓞 ℚ) ∈ u.asIdeal → u.asIdeal = Ideal.span {(p : 𝓞 ℚ)}`. Introduce `u hu`. Take `⟨q, hq, huq⟩` from `exists_prime_gen u`. Rewrite `hu`, the goal using `[huq]`. Establish `hd : (q : 𝓞 ℚ) ∣ (p : 𝓞 ℚ)` using `Ideal.mem_span_singleton.1 hu`.

Establish `hd' : (q : ℤ) ∣ (p : ℤ)`. Use `map_dvd (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) hd` as an intermediate fact. Simplify using `using this`. Establish `: q = p` using `(Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 hd')`. Rewrite using `[this]`.

Conclude with `IsDedekindDomain.HeightOneSpectrum.ext ((key v h).trans (key v' h').symm)`.
-/
private lemma eq_of_natCast_mem {p : ℕ} (hp : p.Prime) (v v' : Pl)
    (h : (p : 𝓞 ℚ) ∈ v.asIdeal) (h' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have key : ∀ u : Pl, (p : 𝓞 ℚ) ∈ u.asIdeal → u.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
    intro u hu
    obtain ⟨q, hq, huq⟩ := exists_prime_gen u
    rw [huq] at hu ⊢
    have hd : (q : 𝓞 ℚ) ∣ (p : 𝓞 ℚ) := Ideal.mem_span_singleton.1 hu
    have hd' : (q : ℤ) ∣ (p : ℤ) := by
      have := map_dvd (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) hd
      simpa using this
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 hd')
    rw [this]
  exact IsDedekindDomain.HeightOneSpectrum.ext ((key v h).trans (key v' h').symm)

open NumberField in
/- English proof (translation)
Introduce `w`. Take `⟨p, hp, hw⟩` from `exists_prime_gen w`. Establish `hnorm : normV w = p`. Establish `h1 : normV w = Ideal.absNorm w.asIdeal`. Simplify using `[normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Rewrite using `[h1, hw, Ideal.absNorm_span_singleton]`. Establish `: ((p : 𝓞 ℚ)) = algebraMap ℤ (𝓞 ℚ) (p : ℤ)` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, RingOfIntegers.rank]`. Simplify using the standard rewrite rules. Use `⟨by rw [hnorm]; exact hp.ne_zero, ?_, fun q hq v v' => eq_of_natCast_mem hq v v'⟩` and prove the remaining obligations.

Introduce `v hvw hmem`. Rewrite `hmem` using `[hnorm]`. Use `hvw (eq_of_natCast_mem hp v w hmem ?_)` and prove the remaining obligations. Rewrite using `[hw]`. Conclude with `Ideal.mem_span_singleton_self _`.
-/
theorem htc_places :
    ∀ (w : UpperTheory.Reformulated.B.Yza3.Pl),
      UpperTheory.Reformulated.B.Yza3.normV w ≠ (0 : ℕ) ∧
        (∀ (v : UpperTheory.Reformulated.B.Yza3.Pl), v ≠ w → (↑(UpperTheory.Reformulated.B.Yza3.normV w) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal) ∧
          ∀ (p : ℕ),
            Nat.Prime p →
              ∀ (v v' : UpperTheory.Reformulated.B.Yza3.Pl),
                (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → (↑p : NumberField.RingOfIntegers ℚ) ∈ v'.asIdeal → v = v' := by
  intro w
  obtain ⟨p, hp, hw⟩ := exists_prime_gen w
  have hnorm : normV w = p := by
    have h1 : normV w = Ideal.absNorm w.asIdeal := by
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h1, hw, Ideal.absNorm_span_singleton]
    have : ((p : 𝓞 ℚ)) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  refine ⟨by rw [hnorm]; exact hp.ne_zero, ?_, fun q hq v v' => eq_of_natCast_mem hq v v'⟩
  intro v hvw hmem
  rw [hnorm] at hmem
  refine hvw (eq_of_natCast_mem hp v w hmem ?_)
  rw [hw]
  exact Ideal.mem_span_singleton_self _

end UpperTheory.Reformulated.B.Yza3
