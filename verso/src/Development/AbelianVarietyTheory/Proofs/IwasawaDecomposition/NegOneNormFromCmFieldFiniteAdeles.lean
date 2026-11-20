import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootQuadratic

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

/- English proof (translation)
Take `⟨t, ht⟩` from `(cm.fixed x).1 hx`. Establish `hi : IsIntegral ℤ t`. Establish `h1 : IsIntegral ℤ (algebraMap F E t)`. Rewrite using `[ht]`. Conclude with `RingOfIntegers.isIntegral_coe x`.

Conclude with `(isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 h1`. Conclude with `⟨⟨t, hi⟩, ht.symm⟩`.
-/
theorem cm_fixed_integer (cm : CMData F E) (x : 𝓞 E) (hx : star (x : E) = (x : E)) :
    ∃ t : 𝓞 F, (x : E) = algebraMap F E t := by
  obtain ⟨t, ht⟩ := (cm.fixed x).1 hx
  have hi : IsIntegral ℤ t := by
    have h1 : IsIntegral ℤ (algebraMap F E t) := by
      rw [ht]; exact RingOfIntegers.isIntegral_coe x
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 h1
  exact ⟨⟨t, hi⟩, ht.symm⟩

/- English proof (translation)
Take `⟨P, hP, hPM⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) M (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]`. Conclude with `bot_le)`. Take `⟨θ, s, hs, hθ⟩` from `cm.cmUnram.2.2 P hP`. Establish `hs' : (s : E) = star (θ : E)` using `hs`.

Take `⟨t, ht⟩` from `cm_fixed_integer cm (θ + s) (by`. Express the relevant statement in the definitionally equal form `star ((θ : E) + s) = (θ : E) + s`. Rewrite using `[hs', star_add, star_star, add_comm])`. Take `⟨n, hn⟩` from `cm_fixed_integer cm (θ * s) (by`. Express the relevant statement in the definitionally equal form `star ((θ : E) * s) = (θ : E) * s`.

Rewrite using `[hs', star_mul, star_star])`. Express the relevant statement in the definitionally equal form `(θ : E) + s = _ at ht`. Express the relevant statement in the definitionally equal form `(θ : E) * s = _ at hn`. Use `⟨θ, t, n, hs' ▸ ht, hs' ▸ hn, fun h => hθ ?_⟩` and prove the remaining obligations. Rewrite `h` using `[← hPM, Ideal.mem_comap]`.

Establish `e : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (θ - s) ^ 2`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `h1 : ∀ z : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z) = algebraMap F E (z : F)` using `fun z => rfl`. Rewrite using `[h1]`. Simplify using `only [map_sub, map_pow, map_mul, map_ofNat]`.

Express the relevant statement in the definitionally equal form `algebraMap F E t ^ 2 - 4 * algebraMap F E n = ((θ : E) - s) ^ 2`. Rewrite using `[← ht, ← hn]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`. Conclude with `hP.isPrime.mem_of_pow_mem 2 h`.
-/
theorem cm_exists_unit_disc (cm : CMData F E) (M : Ideal (𝓞 F)) (hM : M.IsMaximal) :
    ∃ θ : 𝓞 E, ∃ t : 𝓞 F, ∃ n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧
      (θ : E) * star (θ : E) = algebraMap F E n ∧ t ^ 2 - 4 * n ∉ M := by
  obtain ⟨P, hP, hPM⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) M (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact bot_le)
  obtain ⟨θ, s, hs, hθ⟩ := cm.cmUnram.2.2 P hP
  have hs' : (s : E) = star (θ : E) := hs
  obtain ⟨t, ht⟩ := cm_fixed_integer cm (θ + s) (by
    change star ((θ : E) + s) = (θ : E) + s
    rw [hs', star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := cm_fixed_integer cm (θ * s) (by
    change star ((θ : E) * s) = (θ : E) * s
    rw [hs', star_mul, star_star])
  change (θ : E) + s = _ at ht
  change (θ : E) * s = _ at hn
  refine ⟨θ, t, n, hs' ▸ ht, hs' ▸ hn, fun h => hθ ?_⟩
  rw [← hPM, Ideal.mem_comap] at h
  have e : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (θ - s) ^ 2 := by
    apply RingOfIntegers.coe_injective
    have h1 : ∀ z : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z) = algebraMap F E (z : F) :=
      fun z => rfl
    rw [h1]
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    change algebraMap F E t ^ 2 - 4 * algebraMap F E n = ((θ : E) - s) ^ 2
    rw [← ht, ← hn]; ring
  rw [e] at h
  exact hP.isPrime.mem_of_pow_mem 2 h

/- English proof (translation)
Establish `hθ' : star θ - θ ≠ 0` using `fun h => hθ (by linear_combination -h)`. Establish `hq : star ((x - star x) / (θ - star θ)) = (x - star x) / (θ - star θ)`. Rewrite using `[star_div₀, star_sub, star_sub, star_star, star_star]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take `⟨q, hq'⟩` from `(cm.fixed _).1 hq`. Establish `hp : star (x - (x - star x) / (θ - star θ) * θ) = x - (x - star x) / (θ - star θ) * θ`. Rewrite using `[star_sub, star_mul, hq]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take `⟨p, hp'⟩` from `(cm.fixed _).1 hp`. Conclude with `⟨p, q, by rw [hp', hq']; ring⟩`.
-/
theorem cm_exists_coords (cm : CMData F E) (θ : E) (hθ : θ - star θ ≠ 0) (x : E) :
    ∃ p q : F, x = algebraMap F E p + algebraMap F E q * θ := by
  have hθ' : star θ - θ ≠ 0 := fun h => hθ (by linear_combination -h)
  have hq : star ((x - star x) / (θ - star θ)) = (x - star x) / (θ - star θ) := by
    rw [star_div₀, star_sub, star_sub, star_star, star_star]
    field_simp
    ring
  obtain ⟨q, hq'⟩ := (cm.fixed _).1 hq
  have hp : star (x - (x - star x) / (θ - star θ) * θ) = x - (x - star x) / (θ - star θ) * θ := by
    rw [star_sub, star_mul, hq]
    field_simp
    ring
  obtain ⟨p, hp'⟩ := (cm.fixed _).1 hp
  exact ⟨p, q, by rw [hp', hq']; ring⟩

/- English proof (translation)
Establish `key : ∀ (a b : v.adicCompletionIntegers F) (t n : 𝓞 F), a ^ 2 + a * b * algebraMap (𝓞 F) (v.adicCompletionIntegers F) t + b ^ 2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = -1 → (a : v.adicCompletion F) ^ 2 + a * b * algebraMap F (v.adicCompletion F) t + b ^ 2 * algebraMap …`. Introduce `a b t n h`. Establish `h2` using `congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) h`. Establish `h1 : ∀ z : 𝓞 F, ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) z : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (z : F)` using `fun z => rfl`. Move the coercions through the operations in `at h2`.

Rewrite `h2` using `[h1, h1]`. Conclude with `h2`. Distinguish the cases in `hd : t ^ 2 - 4 * n ∈ v.asIdeal`. Take `⟨θ', h⟩` from `cm_exists_unit_disc cm v.asIdeal v.isMaximal`. Take `⟨a, b, t', n', ht', hn', h⟩` from `GlobalTheory.LocalNormNegOne.main F E cm v θ' h`.

Establish `h` using `key a b t' n' h`. Take `⟨p, q, hpq⟩` from `cm_exists_coords cm θ hθ θ'`. Establish `hs : ∀ z : F, star (algebraMap F E z) = algebraMap F E z` using `fun z => (cm.fixed _).2 ⟨z, rfl⟩`. Establish `hst : star (θ' : E) = algebraMap F E p + algebraMap F E q * star (θ : E)`. Rewrite using `[hpq, star_add, star_mul, hs, hs, mul_comm]`.

Establish `e1 : (t' : F) = 2 * p + q * t`. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Simplify using `only [map_add, map_mul, map_ofNat]`. Rewrite using `[← ht', ← ht, hst, hpq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : (n' : F) = p ^ 2 + p * q * t + q ^ 2 * n`. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Simplify using `only [map_add, map_mul, map_pow]`. Rewrite using `[← hn', ← ht, ← hn, hst, hpq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[e1, e2]`. Simplify using `only [map_add, map_mul, map_pow, map_ofNat] at h`. Use `⟨a + b * algebraMap F _ p, b * algebraMap F _ q, ?_, fun h => (h hd).elim⟩` and prove the remaining obligations. Take the linear combination `h`. Take `⟨a, b, t', n', ht', hn', h⟩` from `GlobalTheory.LocalNormNegOne.main F E cm v θ ⟨t, n, ht, hn, hd⟩`.

Establish `h` using `key a b t' n' h`. Establish `e1 : (t' : F) = t` using `(algebraMap F E).injective (ht'.symm.trans ht)`. Establish `e2 : (n' : F) = n` using `(algebraMap F E).injective (hn'.symm.trans hn)`. Rewrite `h` using `[e1, e2]`. Conclude with `⟨a, b, h, fun _ => ⟨a.2, b.2⟩⟩`.
-/
theorem cm_local_neg_one (cm : CMData F E) (θ : 𝓞 E) (t n : 𝓞 F)
    (ht : (θ : E) + star (θ : E) = algebraMap F E t) (hn : (θ : E) * star (θ : E) = algebraMap F E n)
    (hθ : (θ : E) - star (θ : E) ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A B : v.adicCompletion F,
      A ^ 2 + A * B * algebraMap F (v.adicCompletion F) t + B ^ 2 * algebraMap F (v.adicCompletion F) n = -1 ∧
      (t ^ 2 - 4 * n ∉ v.asIdeal → A ∈ v.adicCompletionIntegers F ∧ B ∈ v.adicCompletionIntegers F) := by
  have key : ∀ (a b : v.adicCompletionIntegers F) (t n : 𝓞 F),
      a ^ 2 + a * b * algebraMap (𝓞 F) (v.adicCompletionIntegers F) t +
        b ^ 2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = -1 →
      (a : v.adicCompletion F) ^ 2 + a * b * algebraMap F (v.adicCompletion F) t +
        b ^ 2 * algebraMap F (v.adicCompletion F) n = -1 := by
    intro a b t n h
    have h2 := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) h
    have h1 : ∀ z : 𝓞 F, ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) z : v.adicCompletionIntegers F) :
        v.adicCompletion F) = algebraMap F (v.adicCompletion F) (z : F) := fun z => rfl
    push_cast at h2
    rw [h1, h1] at h2
    exact h2
  by_cases hd : t ^ 2 - 4 * n ∈ v.asIdeal
  · obtain ⟨θ', h⟩ := cm_exists_unit_disc cm v.asIdeal v.isMaximal
    obtain ⟨a, b, t', n', ht', hn', h⟩ := GlobalTheory.LocalNormNegOne.main F E cm v θ' h
    have h := key a b t' n' h
    obtain ⟨p, q, hpq⟩ := cm_exists_coords cm θ hθ θ'
    have hs : ∀ z : F, star (algebraMap F E z) = algebraMap F E z := fun z => (cm.fixed _).2 ⟨z, rfl⟩
    have hst : star (θ' : E) = algebraMap F E p + algebraMap F E q * star (θ : E) := by
      rw [hpq, star_add, star_mul, hs, hs, mul_comm]
    have e1 : (t' : F) = 2 * p + q * t := by
      apply (algebraMap F E).injective
      simp only [map_add, map_mul, map_ofNat]
      rw [← ht', ← ht, hst, hpq]; ring
    have e2 : (n' : F) = p ^ 2 + p * q * t + q ^ 2 * n := by
      apply (algebraMap F E).injective
      simp only [map_add, map_mul, map_pow]
      rw [← hn', ← ht, ← hn, hst, hpq]; ring
    rw [e1, e2] at h
    simp only [map_add, map_mul, map_pow, map_ofNat] at h
    refine ⟨a + b * algebraMap F _ p, b * algebraMap F _ q, ?_, fun h => (h hd).elim⟩
    linear_combination h
  · obtain ⟨a, b, t', n', ht', hn', h⟩ := GlobalTheory.LocalNormNegOne.main F E cm v θ ⟨t, n, ht, hn, hd⟩
    have h := key a b t' n' h
    have e1 : (t' : F) = t := (algebraMap F E).injective (ht'.symm.trans ht)
    have e2 : (n' : F) = n := (algebraMap F E).injective (hn'.symm.trans hn)
    rw [e1, e2] at h
    exact ⟨a, b, h, fun _ => ⟨a.2, b.2⟩⟩

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ cm`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Take `⟨θ, t, n, ht, hn, hd⟩` from `cm_exists_unit_disc cm M hM`. Establish `hd0 : t ^ 2 - 4 * n ≠ 0` using `fun h => hd (h ▸ M.zero_mem)`. Establish `hθ : (θ : E) - star (θ : E) ≠ 0`.

Introduce `h`. Apply `hd0` to reduce the goal to its premises. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Simplify using `only [map_sub, map_pow, map_mul, map_ofNat, map_zero]`.

Express the relevant statement in the definitionally equal form `algebraMap F E t ^ 2 - 4 * algebraMap F E n = 0`. Rewrite using `[← ht, ← hn]`. Take the linear combination `((θ : E) - star (θ : E)) * h`. Use `choose A B hAB hint using cm_local_neg_one cm θ t n ht hn hθ`. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | t ^ 2 - 4 * n ∈ v.asIdeal}.Finite`.

Use `Ideal.finite_factors (R := 𝓞 F) (I := Ideal.span {t ^ 2 - 4 * n}) (by simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)` as an intermediate fact. Simplify `this` using `only [Ideal.dvd_span_singleton]`. Establish `hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, t ^ 2 - 4 * n ∉ v.asIdeal`. Simplify `hfin` using `only [Filter.eventually_cofinite, not_not]`. Set `a : FiniteAdeleRing (𝓞 F) F` to `⟨A, hev.mono fun v hv => (hint v hv).1⟩`.

Set `b : FiniteAdeleRing (𝓞 F) F` to `⟨B, hev.mono fun v hv => (hint v hv).2⟩`. Establish `hab : a ^ 2 + a * b * algebraMap F (FiniteAdeleRing (𝓞 F) F) t + b ^ 2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) n = -1`. Apply `FiniteAdeleRing.ext` to reduce the goal to its premises. Introduce `v`. Use `hAB v` as an intermediate fact.

Rewrite `this`, the goal using `[sq, sq]`. Conclude with `this`. Set `L : E →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F` to `Algebra.TensorProduct.includeLeft`. Set `Rr : FiniteAdeleRing (𝓞 F) F →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F` to `Algebra.TensorProduct.includeRight`. Use `⟨Rr a + L θ * Rr b, ?_⟩` and prove the remaining obligations.

Establish `hL : ∀ x, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) (L x) = L (star x)` using `fun x => by`. Simplify using `[Formalism.UG.sigR, L, CMData.sig, starRingEnd_apply]`. Establish `hR : ∀ x, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) (Rr x) = Rr x` using `fun x => by`. Simplify using `[Formalism.UG.sigR, Rr]`. Establish `h1` using `congrArg L ht`.

Establish `h2` using `congrArg L hn`. Establish `h3` using `congrArg Rr hab`. Simplify using `only [map_add, map_mul, map_pow, map_neg, map_one, AlgHom.commutes] at h1 h2 h3`. Rewrite using `[map_add, map_mul, hL, hR, hR]`. Rewrite `h3` using `[← h1, ← h2]`.

Take the linear combination `h3`.
-/
theorem neg_one_norm_finiteAdele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1 := by
  intro F E _ _ _ _ _ _ cm
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  obtain ⟨θ, t, n, ht, hn, hd⟩ := cm_exists_unit_disc cm M hM
  have hd0 : t ^ 2 - 4 * n ≠ 0 := fun h => hd (h ▸ M.zero_mem)
  have hθ : (θ : E) - star (θ : E) ≠ 0 := by
    intro h
    apply hd0
    apply RingOfIntegers.coe_injective
    apply (algebraMap F E).injective
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_zero]
    change algebraMap F E t ^ 2 - 4 * algebraMap F E n = 0
    rw [← ht, ← hn]
    linear_combination ((θ : E) - star (θ : E)) * h
  choose A B hAB hint using cm_local_neg_one cm θ t n ht hn hθ
  have hfin : {v : HeightOneSpectrum (𝓞 F) | t ^ 2 - 4 * n ∈ v.asIdeal}.Finite := by
    have := Ideal.finite_factors (R := 𝓞 F) (I := Ideal.span {t ^ 2 - 4 * n})
      (by simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)
    simpa only [Ideal.dvd_span_singleton] using this
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, t ^ 2 - 4 * n ∉ v.asIdeal := by
    simpa only [Filter.eventually_cofinite, not_not] using hfin
  let a : FiniteAdeleRing (𝓞 F) F := ⟨A, hev.mono fun v hv => (hint v hv).1⟩
  let b : FiniteAdeleRing (𝓞 F) F := ⟨B, hev.mono fun v hv => (hint v hv).2⟩
  have hab : a ^ 2 + a * b * algebraMap F (FiniteAdeleRing (𝓞 F) F) t +
      b ^ 2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) n = -1 := by
    apply FiniteAdeleRing.ext
    intro v
    have := hAB v
    rw [sq, sq] at this ⊢
    exact this
  let L : E →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F := Algebra.TensorProduct.includeLeft
  let Rr : FiniteAdeleRing (𝓞 F) F →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
    Algebra.TensorProduct.includeRight
  refine ⟨Rr a + L θ * Rr b, ?_⟩
  have hL : ∀ x, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) (L x) = L (star x) := fun x => by
    simp [Formalism.UG.sigR, L, CMData.sig, starRingEnd_apply]
  have hR : ∀ x, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) (Rr x) = Rr x := fun x => by
    simp [Formalism.UG.sigR, Rr]
  have h1 := congrArg L ht
  have h2 := congrArg L hn
  have h3 := congrArg Rr hab
  simp only [map_add, map_mul, map_pow, map_neg, map_one, AlgHom.commutes] at h1 h2 h3
  rw [map_add, map_mul, hL, hR, hR]
  rw [← h1, ← h2] at h3
  linear_combination h3

end GlobalTheory
