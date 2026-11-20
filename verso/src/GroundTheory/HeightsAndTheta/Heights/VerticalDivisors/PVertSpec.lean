import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

/- English proof (translation)
Establish `h1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hmin`. Establish `hsurj : Function.Surjective (Ideal.Quotient.mk P)` using `Ideal.Quotient.mk_surjective`. Establish `hker : RingHom.ker (Ideal.Quotient.mk P) = P` using `Ideal.mk_ker`. Establish `prime_map : ∀ J : Ideal A, J.IsPrime → P ≤ J → (J.map (Ideal.Quotient.mk P)).IsPrime` using `fun J _ hPJ => Ideal.map_isPrime_of_surjective hsurj (hker.trans_le hPJ)`. Establish `strict : ∀ J₁ J₂ : Ideal A, P ≤ J₁ → J₁ < J₂ → J₁.map (Ideal.Quotient.mk P) < J₂.map (Ideal.Quotient.mk P)`.

Introduce `J₁ J₂ h₁ h₁₂`. Use `lt_of_le_of_ne (Ideal.map_mono h₁₂.le) fun h => h₁₂.ne ?_` and prove the remaining obligations. Use `congrArg (Ideal.comap (Ideal.Quotient.mk P)) h` as an intermediate fact. Rewrite `this` using `[Ideal.comap_map_of_surjective' _ hsurj, Ideal.comap_map_of_surjective' _ hsurj, hker, sup_eq_left.mpr h₁, sup_eq_left.mpr (h₁.trans h₁₂.le)]`. Then use the resulting hypothesis. Use `prime_map P hP le_rfl` as an intermediate fact.

Use `prime_map Q hQ hPQ.le` as an intermediate fact. Use `prime_map W hW (hPQ.le.trans hQW.le)` as an intermediate fact. Establish `a` using `Ideal.height_add_one_le_of_lt_of_isPrime (strict P Q le_rfl hPQ)`. Establish `b` using `Ideal.height_add_one_le_of_lt_of_isPrime (strict Q W hPQ.le hQW)`. Establish `: (2 : ℕ∞) ≤ 1`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd this (by norm_num)`.
-/
theorem not_lt_lt_of_mem_minimalPrimes_sup_span {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [hP : P.IsPrime] [hQ : Q.IsPrime] [hW : W.IsPrime] {x : A}
    (hmin : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P < Q) (hQW : Q < W) : False := by
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hsurj : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have prime_map : ∀ J : Ideal A, J.IsPrime → P ≤ J → (J.map (Ideal.Quotient.mk P)).IsPrime :=
    fun J _ hPJ => Ideal.map_isPrime_of_surjective hsurj (hker.trans_le hPJ)
  have strict : ∀ J₁ J₂ : Ideal A, P ≤ J₁ → J₁ < J₂ →
      J₁.map (Ideal.Quotient.mk P) < J₂.map (Ideal.Quotient.mk P) := by
    intro J₁ J₂ h₁ h₁₂
    refine lt_of_le_of_ne (Ideal.map_mono h₁₂.le) fun h => h₁₂.ne ?_
    have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) h
    rwa [Ideal.comap_map_of_surjective' _ hsurj, Ideal.comap_map_of_surjective' _ hsurj, hker,
      sup_eq_left.mpr h₁, sup_eq_left.mpr (h₁.trans h₁₂.le)] at this
  have := prime_map P hP le_rfl
  have := prime_map Q hQ hPQ.le
  have := prime_map W hW (hPQ.le.trans hQW.le)
  have a := Ideal.height_add_one_le_of_lt_of_isPrime (strict P Q le_rfl hPQ)
  have b := Ideal.height_add_one_le_of_lt_of_isPrime (strict Q W hPQ.le hQW)
  have : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (P.map (Ideal.Quotient.mk P)).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (Q.map (Ideal.Quotient.mk P)).height + 1 := by gcongr
      _ ≤ (W.map (Ideal.Quotient.mk P)).height := b
      _ ≤ 1 := h1
  exact absurd this (by norm_num)

variable {K : Type*} [Field K] {n : ℕ}

/- English proof (translation)
Assume the negation of the conclusion as `h`. Apply `hI.ne_top` to reduce the goal to its premises. Simplify using `only [integralModel, Ideal.mem_comap, map_C] at hc`. Establish `hu : IsUnit (C (algebraMap (𝓞 K) K c) : MvPolynomial (Fin n) K)` using `(isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr h)).map C`. Conclude with `Ideal.eq_top_of_isUnit_mem _ hc hu`.
-/
theorem eq_zero_of_C_mem_integralModel {I : Ideal (MvPolynomial (Fin n) K)} (hI : I.IsPrime)
    {c : 𝓞 K} (hc : C c ∈ integralModel I) : c = 0 := by
  by_contra h
  apply hI.ne_top
  simp only [integralModel, Ideal.mem_comap, map_C] at hc
  have hu : IsUnit (C (algebraMap (𝓞 K) K c) : MvPolynomial (Fin n) K) :=
    (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr h)).map C
  exact Ideal.eq_top_of_isUnit_mem _ hc hu

/- English proof (translation)
Simplify using `only [integralModel, Ideal.mem_comap] at h`. Use `h using 1` and compare the differences between its conclusion and the goal. Simplify using `[linForm, map_sum, map_mul, map_C, map_X]`.
-/
theorem linForm_mem_integralModel {I : Ideal (MvPolynomial (Fin n) K)} {u : Fin n → 𝓞 K}
    (h : linForm u ∈ integralModel I) : linForm (fun j => (u j : K)) ∈ I := by
  simp only [integralModel, Ideal.mem_comap] at h
  convert h using 1
  simp [linForm, map_sum, map_mul, map_C, map_X]

/- English proof (translation)
Introduce `K _ _ n e I f u v hI _ hu`. Establish `: I.IsPrime` using `hI.isPrime`. Establish `hP : (integralModel I).IsPrime` using `by unfold integralModel; infer_instance`. Establish `hl : linForm u ∉ integralModel I` using `fun h => hu (linForm_mem_integralModel h)`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`.

Establish `hCa : C a ∉ integralModel I` using `fun h => ha0 (eq_zero_of_C_mem_integralModel hI.isPrime h)`. Use extensionality with `W`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hWmin, hWrel⟩, hWv⟩`. Establish `: W.IsPrime` using `Ideal.IsMinimalPrime.isPrime hWmin`.

Establish `hvW : Ideal.map C v.asIdeal ≤ W` using `Ideal.map_le_iff_le_comap.mpr hWv.ge`. Use `⟨⟨⟨⟨inferInstance, sup_le (le_sup_left.trans hWmin.1.2) hvW⟩, fun Q hQ hQW => ?_⟩, hWrel⟩, hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hWQ`. Use `hQ.1` as an intermediate fact. Establish `hPQ : integralModel I < Q` using `lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h => hCa (by rw [h]; exact hQ.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem C ha)))`.

Conclude with `not_lt_lt_of_mem_minimalPrimes_sup_span hWmin hPQ (lt_of_le_of_ne hQW fun h => hWQ h.ge)`. Introduce and unpack `⟨⟨hWmin, hWrel⟩, hlW⟩`. Establish `: W.IsPrime` using `Ideal.IsMinimalPrime.isPrime hWmin`. Establish `hvW : Ideal.map C v.asIdeal ≤ W` using `le_sup_right.trans hWmin.1.2`. Establish `hPW : integralModel I ≤ W` using `le_sup_left.trans hWmin.1.2`.

Establish `hcomap : W.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = v.asIdeal` using `(v.isMaximal.eq_of_le (Ideal.IsPrime.comap C).ne_top (Ideal.map_le_iff_le_comap.mp hvW)).symm`. Establish `hWa : W ∈ (integralModel I ⊔ Ideal.span {C a}).minimalPrimes`. Use `⟨⟨inferInstance, sup_le hPW (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hvW (Ideal.mem_map_of_mem C ha))))⟩, fun Q hQ hQW => ?_⟩` and prove the remaining obligations. Use `hQ.1` as an intermediate fact. Establish `hQv : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = v.asIdeal`.

Establish `hle : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) ≤ v.asIdeal` using `hcomap ▸ Ideal.comap_mono hQW`. Establish `hmem : a ∈ Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K))` using `hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hne : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) ≠ ⊥` using `fun h => ha0 (by rwa [h, Ideal.mem_bot] at hmem)`. Conclude with `(Ideal.IsPrime.isMaximal (Ideal.IsPrime.comap C) hne).eq_of_le v.isPrime.ne_top hle`. Conclude with `hWmin.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) (Ideal.map_le_iff_le_comap.mpr hQv.ge)⟩ hQW`.

Use `⟨⟨⟨⟨inferInstance, sup_le hPW (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hlW))⟩, fun Q hQ hQW => ?_⟩, hWrel⟩, hcomap⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hWQ`. Use `hQ.1` as an intermediate fact. Establish `hPQ : integralModel I < Q` using `lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h => hl (by rw [h]; exact hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))`. Conclude with `not_lt_lt_of_mem_minimalPrimes_sup_span hWa hPQ (lt_of_le_of_ne hQW fun h => hWQ h.ge)`.
-/
theorem VertSpec.proof : VertSpec.Statement := by
  intro K _ _ n e I f u v hI _ hu
  have : I.IsPrime := hI.isPrime
  have hP : (integralModel I).IsPrime := by unfold integralModel; infer_instance
  have hl : linForm u ∉ integralModel I := fun h => hu (linForm_mem_integralModel h)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hCa : C a ∉ integralModel I := fun h => ha0 (eq_zero_of_C_mem_integralModel hI.isPrime h)
  ext W
  constructor
  · rintro ⟨⟨hWmin, hWrel⟩, hWv⟩
    have : W.IsPrime := Ideal.IsMinimalPrime.isPrime hWmin
    have hvW : Ideal.map C v.asIdeal ≤ W := Ideal.map_le_iff_le_comap.mpr hWv.ge
    refine ⟨⟨⟨⟨inferInstance, sup_le (le_sup_left.trans hWmin.1.2) hvW⟩, fun Q hQ hQW => ?_⟩,
      hWrel⟩, hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
    by_contra hWQ
    have := hQ.1
    have hPQ : integralModel I < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
      hCa (by rw [h]; exact hQ.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem C ha)))
    exact not_lt_lt_of_mem_minimalPrimes_sup_span hWmin hPQ
      (lt_of_le_of_ne hQW fun h => hWQ h.ge)
  · rintro ⟨⟨hWmin, hWrel⟩, hlW⟩
    have : W.IsPrime := Ideal.IsMinimalPrime.isPrime hWmin
    have hvW : Ideal.map C v.asIdeal ≤ W := le_sup_right.trans hWmin.1.2
    have hPW : integralModel I ≤ W := le_sup_left.trans hWmin.1.2
    have hcomap : W.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = v.asIdeal :=
      (v.isMaximal.eq_of_le (Ideal.IsPrime.comap C).ne_top
        (Ideal.map_le_iff_le_comap.mp hvW)).symm
    have hWa : W ∈ (integralModel I ⊔ Ideal.span {C a}).minimalPrimes := by
      refine ⟨⟨inferInstance, sup_le hPW (Ideal.span_le.mpr
        (Set.singleton_subset_iff.mpr (hvW (Ideal.mem_map_of_mem C ha))))⟩, fun Q hQ hQW => ?_⟩
      have := hQ.1
      have hQv : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = v.asIdeal := by
        have hle : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) ≤ v.asIdeal :=
          hcomap ▸ Ideal.comap_mono hQW
        have hmem : a ∈ Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) :=
          hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        have hne : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) ≠ ⊥ := fun h =>
          ha0 (by rwa [h, Ideal.mem_bot] at hmem)
        exact (Ideal.IsPrime.isMaximal (Ideal.IsPrime.comap C) hne).eq_of_le
          v.isPrime.ne_top hle
      exact hWmin.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2)
        (Ideal.map_le_iff_le_comap.mpr hQv.ge)⟩ hQW
    refine ⟨⟨⟨⟨inferInstance, sup_le hPW (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hlW))⟩,
      fun Q hQ hQW => ?_⟩, hWrel⟩, hcomap⟩
    by_contra hWQ
    have := hQ.1
    have hPQ : integralModel I < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
      hl (by rw [h]; exact hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact not_lt_lt_of_mem_minimalPrimes_sup_span hWa hPQ
      (lt_of_le_of_ne hQW fun h => hWQ h.ge)

end

end GroundTheory.Heights₂.Heights.Vertical
