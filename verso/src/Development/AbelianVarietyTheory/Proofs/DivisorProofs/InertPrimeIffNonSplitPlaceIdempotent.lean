import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertPlace

open GlobalTheory.IdemSupport

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hI`. Conclude with `((isConjPl_iff P P).1 (GlobalTheory.XiSplit.isConjPl_of_smul_eq (hI P.asIdeal P.isPrime P.ne_bot hqP))).symm`. Introduce `hc`. Assume the negation of the conclusion as `h`.

Conclude with `GlobalTheory.NormSum.VacInt.conj_smul_ne D hq h P.asIdeal P.isPrime hqP (GlobalTheory.XiSplit.smul_eq_of_isConjPl ((isConjPl_iff P P).2 hc.symm))`.
-/
theorem inertQ_iff_cP {D : D7} {q : ℕ} (hq : q.Prime) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hqP : (q : 𝓞 D.host.E) ∈ P.asIdeal) : Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ cP P = P := by
  constructor
  · intro hI
    exact ((isConjPl_iff P P).1 (GlobalTheory.XiSplit.isConjPl_of_smul_eq (hI P.asIdeal P.isPrime P.ne_bot hqP))).symm
  · intro hc
    by_contra h
    exact GlobalTheory.NormSum.VacInt.conj_smul_ne D hq h P.asIdeal P.isPrime hqP
      (GlobalTheory.XiSplit.smul_eq_of_isConjPl ((isConjPl_iff P P).2 hc.symm))

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `exists_comp D`. Take `⟨h0, h1, h2⟩` from `place_comp hΦ hη`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hns⟩`. Assume the negation of the conclusion as `hc`.

Take `⟨e, f, h⟩` from `exists_isPrimeIdem hΦ P`. Take `⟨hd, ε, hε, hf⟩` from `of_isPrimeIdem hΦ h`. Rewrite `hε` using `[hP]`. Establish `hεη` using `placeIdem_unique hε hη`. Substitute `hεη` using the available equality.

Break down `h with ⟨h, rfl⟩ | ⟨rfl, -, -⟩` into its components or cases. Conclude with `hns ⟨e, h.1, hf⟩`. Establish `hd'` using `delta_conj hΦ hd`. Rewrite `hd'` using `[hf, cA_algebraMap, ← hf]`. Use `hd'.2.2 P (Ne.symm hc)` as an intermediate fact.

Rewrite `this` using `[hd.2.1]`. Conclude with `one_ne_zero this`. Introduce `hc`. Use `⟨hη, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨e, ⟨ee, ec, -⟩, hs⟩`.

Establish `he : e * algebraMap (AF D.host.F) (AE D) η = e`. Rewrite using `[← hs, mul_add, ee, ec, add_zero]`. Establish `hi : infPart D e = 0`. Rewrite using `[← he, RingHom.map_mul, h0, mul_zero]`. Establish `hout : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q ≠ P → Φ e Q = 0`.

Introduce `Q hQ`. Establish `hQv : Q.under (𝓞 D.host.F) ≠ v`. Introduce `hv`. Break down `eq_or_eq_cP (hv.trans hP.symm) with h | h` into its components or cases. Conclude with `hQ h`.

Conclude with `hQ (h.trans hc)`. Rewrite using `[← he, ev_mul, h2 Q hQv, mul_zero]`. Establish `hPP : Φ e P * Φ e P = Φ e P` using `by rw [← ev_mul, ee]`. Establish `h01 : Φ e P = 0 ∨ Φ e P = 1`. Establish `: Φ e P * (Φ e P - 1) = 0` using `by rw [mul_sub, hPP, mul_one, sub_self]`.

Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr (sub_eq_zero.1 h)`. Break down `h01 with h | h` into its components or cases. Establish `e0 : e = 0`.

Use `hΦ.ext e hi (FiniteAdeleRing.ext _ fun Q => ?_)` and prove the remaining obligations. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[h]`. Both sides reduce to the same expression.

Rewrite using `[hout Q hQ]`. Both sides reduce to the same expression. Use `h1 P hP` as an intermediate fact. Rewrite `this` using `[← hs, e0, map_zero, add_zero, ev_zero]`. Conclude with `zero_ne_one this`.

Establish `hd : IsDelta Φ P e` using `⟨hi, h, hout⟩`. Establish `hd'` using `delta_conj hΦ hd`. Rewrite `hd'` using `[hc]`. Establish `hce` using `delta_unique hΦ hd' hd`. Rewrite `ec` using `[hce, ee]`.

Rewrite `h` using `[ec, ev_zero]`. Conclude with `zero_ne_one h`.
-/
theorem nonSplitAt_iff_cP {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F}
    (hη : IsPlaceIdem D v η) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) = v) :
    GlobalTheory.WeilParts.NonSplitAt D v η ↔ cP P = P := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hη
  constructor
  · rintro ⟨-, hns⟩
    by_contra hc
    obtain ⟨e, f, h⟩ := exists_isPrimeIdem hΦ P
    obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem hΦ h
    rw [hP] at hε
    have hεη := placeIdem_unique hε hη
    subst hεη
    rcases h with ⟨h, rfl⟩ | ⟨rfl, -, -⟩
    · exact hns ⟨e, h.1, hf⟩
    · have hd' := delta_conj hΦ hd
      rw [hf, cA_algebraMap, ← hf] at hd'
      have := hd'.2.2 P (Ne.symm hc)
      rw [hd.2.1] at this
      exact one_ne_zero this
  · intro hc
    refine ⟨hη, ?_⟩
    rintro ⟨e, ⟨ee, ec, -⟩, hs⟩
    have he : e * algebraMap (AF D.host.F) (AE D) η = e := by
      rw [← hs, mul_add, ee, ec, add_zero]
    have hi : infPart D e = 0 := by
      rw [← he, RingHom.map_mul, h0, mul_zero]
    have hout : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q ≠ P → Φ e Q = 0 := by
      intro Q hQ
      have hQv : Q.under (𝓞 D.host.F) ≠ v := by
        intro hv
        rcases eq_or_eq_cP (hv.trans hP.symm) with h | h
        · exact hQ h
        · exact hQ (h.trans hc)
      rw [← he, ev_mul, h2 Q hQv, mul_zero]
    have hPP : Φ e P * Φ e P = Φ e P := by rw [← ev_mul, ee]
    have h01 : Φ e P = 0 ∨ Φ e P = 1 := by
      have : Φ e P * (Φ e P - 1) = 0 := by rw [mul_sub, hPP, mul_one, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.1 h)
    rcases h01 with h | h
    · have e0 : e = 0 := by
        refine hΦ.ext e hi (FiniteAdeleRing.ext _ fun Q => ?_)
        by_cases hQ : Q = P
        · subst hQ; rw [h]; rfl
        · rw [hout Q hQ]; rfl
      have := h1 P hP
      rw [← hs, e0, map_zero, add_zero, ev_zero] at this
      exact zero_ne_one this
    · have hd : IsDelta Φ P e := ⟨hi, h, hout⟩
      have hd' := delta_conj hΦ hd
      rw [hc] at hd'
      have hce := delta_unique hΦ hd' hd
      rw [hce, ee] at ec
      rw [ec, ev_zero] at h
      exact zero_ne_one h

/- English proof (translation)
Introduce `D q hq v η hη hqv`. Use `v.isPrime` as an intermediate fact. Take `⟨Q, hQ, hl⟩` from `(Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some`. Set `P : HeightOneSpectrum (𝓞 D.host.E)` to `⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩`. Establish `hP : P.under (𝓞 D.host.F) = v` using `HeightOneSpectrum.ext hl.over.symm`.

Establish `hqP : (q : 𝓞 D.host.E) ∈ P.asIdeal`. Establish `h : (q : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal` using `by rw [hP]; exact hqv`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal at h`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis. Rewrite using `[inertQ_iff_cP hq P hqP, nonSplitAt_iff_cP hη P hP]`.
-/
theorem inertQ_iff_nonSplitAt : ∀ (D : D7) (q : ℕ), q.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η →
    (q : 𝓞 D.host.F) ∈ v.asIdeal → (Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ GlobalTheory.WeilParts.NonSplitAt D v η) := by
  intro D q hq v η hη hqv
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hP : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hl.over.symm
  have hqP : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h : (q : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by rw [hP]; exact hqv
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal at h
    rwa [map_natCast] at h
  rw [inertQ_iff_cP hq P hqP, nonSplitAt_iff_cP hη P hP]

end GlobalTheory.InertPlace
