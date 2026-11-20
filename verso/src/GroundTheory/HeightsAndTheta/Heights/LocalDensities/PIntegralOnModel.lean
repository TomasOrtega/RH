import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.KrullDomain
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

/- English proof (translation)
Distinguish the cases in `hb : b = 0`. Use `⟨⊥, Ideal.isPrime_bot, 1, ?_, 0, (⊥ : Ideal A).zero_mem, by simp [hb]⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_bot]`. Conclude with `one_ne_zero`. Set `N : Submodule A (A ⧸ Ideal.span {b})` to `Submodule.span A {Ideal.Quotient.mk _ a}`.

Set `n₀ : N` to `⟨Ideal.Quotient.mk _ a, Submodule.subset_span rfl⟩`. Establish `hn₀ : n₀ ≠ 0`. Introduce `h`. Apply `hab` to reduce the goal to its premises. Establish `: Ideal.Quotient.mk (Ideal.span {b}) a = 0` using `congrArg Subtype.val h`.

Rewrite `this` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Take `⟨P, hP, -⟩` from `exists_le_isAssociatedPrime_of_isNoetherianRing A n₀ hn₀`. Take `⟨hPp, ⟨m, hm⟩, hPy⟩` from `isAssociatedPrime_iff.1 hP`. Take `⟨x, rfl⟩` from `Submodule.mem_span_singleton.1 hm`. Take `⟨y, hy⟩ : ∃ y, y = x * a` from `⟨_, rfl⟩`.

Establish `hmem : ∀ r, r ∈ P ↔ b ∣ r * y`. Introduce `r`. Rewrite using `[hPy, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Subtype.coe_inj]`. Use `show r • (x • Ideal.Quotient.mk (Ideal.span {b}) a) = 0 ↔ b ∣ r * y`. Rewrite using `[smul_smul, GroundTheory.Arith.Toric.smul_mk_eq_zero_iff, hy, mul_assoc]`.

Establish `hbP : b ∈ P` using `(hmem b).2 (dvd_mul_right b y)`. Distinguish the cases in `hcase : ∀ r s : A, r ∈ P → r * y = b * s → s ∈ P`. It suffices to derive a contradiction. Set `K` to `FractionRing A`. Establish `hinj : Function.Injective (algebraMap A K)` using `IsFractionRing.injective A K`.

Set `M : Submodule A K` to `Submodule.map (Algebra.linearMap A K) P`. Establish `hMfg : M.FG` using `(IsNoetherian.noetherian P).map _`. Establish `hM0 : M ≠ ⊥`. Introduce `h`. Establish `: algebraMap A K b ∈ M` using `Submodule.mem_map.2 ⟨b, hbP, rfl⟩`.

Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hb (hinj (by rw [this, map_zero]))`. Establish `hbK : algebraMap A K b ≠ 0` using `fun h => hb (hinj (by rw [h, map_zero]))`. Establish `hint : IsIntegral A (algebraMap A K y / algebraMap A K b)`. Use `isIntegral_of_smul_mem_submodule M hM0 hMfg _ ?_` and prove the remaining obligations.

Introduce `n hn`. Take `⟨r, hr, rfl⟩` from `Submodule.mem_map.1 hn`. Take `⟨s, hs⟩` from `(hmem r).1 hr`. Use `Submodule.mem_map.2 ⟨s, hcase r s hr hs, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap A K s = (algebraMap A K y / algebraMap A K b) * algebraMap A K r`.

Rewrite using `[div_mul_eq_mul_div, eq_div_iff hbK, ← map_mul, ← map_mul, mul_comm y r, hs, mul_comm]`. Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Establish `hyz : y = b * z`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hz, mul_div_cancel₀ _ hbK]`.

Apply `hPp.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, hmem, one_mul, hyz]`. Conclude with `dvd_mul_right b z`. Use `push Not at hcase`. Take `⟨r₀, s₀, hr₀, hrs, hs₀⟩` from `hcase`.

Use `⟨P, hPp, s₀, hs₀, r₀ * x, P.mul_mem_right x hr₀, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, ← hy, hrs, mul_comm]`.
-/
theorem exists_prime_mul_eq_of_not_dvd {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a b : A} (hab : ¬ b ∣ a) :
    ∃ P : Ideal A, P.IsPrime ∧ ∃ w ∉ P, ∃ c ∈ P, w * b = c * a := by
  classical
  by_cases hb : b = 0
  · refine ⟨⊥, Ideal.isPrime_bot, 1, ?_, 0, (⊥ : Ideal A).zero_mem, by simp [hb]⟩
    rw [Submodule.mem_bot]
    exact one_ne_zero
  let N : Submodule A (A ⧸ Ideal.span {b}) := Submodule.span A {Ideal.Quotient.mk _ a}
  let n₀ : N := ⟨Ideal.Quotient.mk _ a, Submodule.subset_span rfl⟩
  have hn₀ : n₀ ≠ 0 := by
    intro h
    apply hab
    have : Ideal.Quotient.mk (Ideal.span {b}) a = 0 := congrArg Subtype.val h
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A n₀ hn₀
  obtain ⟨hPp, ⟨m, hm⟩, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.1 hm
  obtain ⟨y, hy⟩ : ∃ y, y = x * a := ⟨_, rfl⟩
  have hmem : ∀ r, r ∈ P ↔ b ∣ r * y := by
    intro r
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Subtype.coe_inj]
    show r • (x • Ideal.Quotient.mk (Ideal.span {b}) a) = 0 ↔ b ∣ r * y
    rw [smul_smul, GroundTheory.Arith.Toric.smul_mk_eq_zero_iff, hy, mul_assoc]
  have hbP : b ∈ P := (hmem b).2 (dvd_mul_right b y)
  by_cases hcase : ∀ r s : A, r ∈ P → r * y = b * s → s ∈ P
  · exfalso
    let K := FractionRing A
    have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
    let M : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hMfg : M.FG := (IsNoetherian.noetherian P).map _
    have hM0 : M ≠ ⊥ := by
      intro h
      have : algebraMap A K b ∈ M := Submodule.mem_map.2 ⟨b, hbP, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hb (hinj (by rw [this, map_zero]))
    have hbK : algebraMap A K b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hint : IsIntegral A (algebraMap A K y / algebraMap A K b) := by
      refine isIntegral_of_smul_mem_submodule M hM0 hMfg _ ?_
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      refine Submodule.mem_map.2 ⟨s, hcase r s hr hs, ?_⟩
      change algebraMap A K s = (algebraMap A K y / algebraMap A K b) * algebraMap A K r
      rw [div_mul_eq_mul_div, eq_div_iff hbK, ← map_mul, ← map_mul, mul_comm y r, hs, mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hyz : y = b * z := by
      apply hinj
      rw [map_mul, hz, mul_div_cancel₀ _ hbK]
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, hmem, one_mul, hyz]
    exact dvd_mul_right b z
  · push Not at hcase
    obtain ⟨r₀, s₀, hr₀, hrs, hs₀⟩ := hcase
    refine ⟨P, hPp, s₀, hs₀, r₀ * x, P.mul_mem_right x hr₀, ?_⟩
    rw [mul_assoc, ← hy, hrs, mul_comm]

/- English proof (translation)
Introduce `F _ _ R _ _ _ _ _ _ r g s ⟨hs, hg, hpts⟩`. Establish `: IsNoetherianRing R` using `Algebra.FiniteType.isNoetherianRing (𝓞 F) R`. Assume the negation of the conclusion as `hndvd`. Establish `hnd : ¬ algebraMap (𝓞 F) R s ∣ r` using `fun ⟨r', h⟩ => hndvd ⟨r', h⟩`. Take `⟨P, hP, w, hw, c, hc, hwc⟩` from `exists_prime_mul_eq_of_not_dvd hnd`.

Establish `hsP : algebraMap (𝓞 F) R s ∈ P`. Establish `: w * algebraMap (𝓞 F) R s ∈ P` using `hwc ▸ P.mul_mem_right r hc`. Conclude with `(hP.mem_or_mem this).resolve_left hw`. Establish `hpP : (P.comap (algebraMap (𝓞 F) R)).IsPrime` using `Ideal.comap_isPrime _ P`. Establish `hp0 : P.comap (algebraMap (𝓞 F) R) ≠ ⊥`.

Introduce `h`. Establish `: s ∈ P.comap (algebraMap (𝓞 F) R)` using `hsP`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hs this`. Set `v : HeightOneSpectrum (𝓞 F)` to `⟨P.comap (algebraMap (𝓞 F) R), hpP, hp0⟩`.

Take `⟨L, _, _, _, y, hcomp, hint, hyg, ⟨bw, hbw, hbwint⟩, hPnon⟩` from `hpt F R v P w g ⟨hP, rfl, hw, hg⟩`. Establish `hys : y (algebraMap (𝓞 F) R s) ≠ 0`. Rewrite using `[← RingHom.comp_apply, hcomp]`. Simplify using `only [RingHom.comp_apply, ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]`. Conclude with `hs`.

Establish `hyr` using `hpts v L y hcomp hint hyg`. Apply `hPnon c hc (y r / y (algebraMap (𝓞 F) R s) * bw) _ (RingHom.IsIntegralElem.mul _ hyr hbwint)` to reduce the goal to its premises. Establish `h1 : y w * y (algebraMap (𝓞 F) R s) = y c * y r` using `by rw [← map_mul, ← map_mul, hwc]`. Combine the equalities or inequalities in the displayed calculation. Establish `hyw : y w ≠ 0` using `fun h0 => by simp [h0] at hbw`.

Clear the denominators using the available nonvanishing facts. Use `_ = 1 := by rw [hbw, ← h1, div_self (mul_ne_zero (fun h0 => by simp [h0] at hbw) hys), one_mul]`.
-/
theorem IntegralOnModel.proof (hpt : IntegralPointThroughPrime.Statement) :
    IntegralOnModel.Statement := by
  intro F _ _ R _ _ _ _ _ _ r g s ⟨hs, hg, hpts⟩
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (𝓞 F) R
  by_contra hndvd
  have hnd : ¬ algebraMap (𝓞 F) R s ∣ r := fun ⟨r', h⟩ => hndvd ⟨r', h⟩
  obtain ⟨P, hP, w, hw, c, hc, hwc⟩ := exists_prime_mul_eq_of_not_dvd hnd
  have hsP : algebraMap (𝓞 F) R s ∈ P := by
    have : w * algebraMap (𝓞 F) R s ∈ P := hwc ▸ P.mul_mem_right r hc
    exact (hP.mem_or_mem this).resolve_left hw
  have hpP : (P.comap (algebraMap (𝓞 F) R)).IsPrime := Ideal.comap_isPrime _ P
  have hp0 : P.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
    intro h
    have : s ∈ P.comap (algebraMap (𝓞 F) R) := hsP
    rw [h, Submodule.mem_bot] at this
    exact hs this
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.comap (algebraMap (𝓞 F) R), hpP, hp0⟩
  obtain ⟨L, _, _, _, y, hcomp, hint, hyg, ⟨bw, hbw, hbwint⟩, hPnon⟩ :=
    hpt F R v P w g ⟨hP, rfl, hw, hg⟩
  have hys : y (algebraMap (𝓞 F) R s) ≠ 0 := by
    rw [← RingHom.comp_apply, hcomp]
    simp only [RingHom.comp_apply, ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hs
  have hyr := hpts v L y hcomp hint hyg
  apply hPnon c hc (y r / y (algebraMap (𝓞 F) R s) * bw) _ (RingHom.IsIntegralElem.mul _ hyr hbwint)
  have h1 : y w * y (algebraMap (𝓞 F) R s) = y c * y r := by rw [← map_mul, ← map_mul, hwc]
  calc y r / y (algebraMap (𝓞 F) R s) * bw * y c
      = bw * y w * ((y c * y r) / (y w * y (algebraMap (𝓞 F) R s))) := by
        have hyw : y w ≠ 0 := fun h0 => by simp [h0] at hbw
        field_simp
    _ = 1 := by rw [hbw, ← h1, div_self (mul_ne_zero (fun h0 => by simp [h0] at hbw) hys), one_mul]

end GroundTheory.Heights₂.Heights.FourB
