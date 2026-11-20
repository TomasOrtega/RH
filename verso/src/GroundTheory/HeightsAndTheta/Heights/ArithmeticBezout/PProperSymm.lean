import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Ideal

/- English proof (translation)
Establish `hPp : P.IsPrime` using `hP.1.1`. Unfold `localMult`. Rewrite using `[dif_pos hPp]`. Set `R` to `Localization.AtPrime P`. Set `I : Ideal R` to `J.map (algebraMap A R)`.

Establish `hmin : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes`. Rewrite using `[IsLocalization.minimalPrimes_map P.primeCompl R J, Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]`. Conclude with `hP`. Use `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin` as an intermediate fact. Establish `: IsArtinian R (R ⧸ I)` using `isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))`.

Establish `: IsNoetherian R (R ⧸ I)` using `isNoetherian_quotient I`. Establish `hI : I ≠ ⊤` using `ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmin.1.2`. Establish `: Nontrivial (R ⧸ I)` using `Ideal.Quotient.nontrivial_iff.mpr hI`. Rewrite using `[Ne, ENat.toNat_eq_zero, not_or]`. Conclude with `⟨(Module.length_pos (R := R) (M := R ⧸ I)).ne', Module.length_ne_top⟩`.
-/
theorem localMult_ne_zero_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    {J P : Ideal A} (hP : P ∈ J.minimalPrimes) : localMult J P ≠ 0 := by
  have hPp : P.IsPrime := hP.1.1
  unfold localMult
  rw [dif_pos hPp]
  let R := Localization.AtPrime P
  let I : Ideal R := J.map (algebraMap A R)
  have hmin : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map P.primeCompl R J, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact hP
  have := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin
  have : IsArtinian R (R ⧸ I) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  have : IsNoetherian R (R ⧸ I) := isNoetherian_quotient I
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmin.1.2
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [Ne, ENat.toNat_eq_zero, not_or]
  exact ⟨(Module.length_pos (R := R) (M := R ⧸ I)).ne', Module.length_ne_top⟩

/- English proof (translation)
Introduce `n W u u' hW hu hu' hadm W'' hW'' hlu`. Establish `hval` using `Finsupp.mem_support_iff.mp hW''`. Simplify using `only [divCycle, fundCycle, Finsupp.onFinset_apply] at hval`. Establish `hrel : W'' ∈ relComps (W ⊔ span {linForm u'})`. Assume the negation of the conclusion as `h`.

Conclude with `hval (if_neg h)`. Take `⟨hmin'', hrel''⟩` from `hrel`. Establish `: W''.IsPrime` using `hmin''.1.1`. Establish `hle : W ⊔ span {linForm u} ≤ W''` using `sup_le (le_sup_left.trans hmin''.1.2) ((span_singleton_le_iff_mem _).mpr hlu)`. Take `⟨W', hW', hW'le⟩` from `Ideal.exists_minimalPrimes_le hle`.

Establish `hrel' : IsRelevant W'`. Take `⟨j, hj⟩` from `hrel''`. Conclude with `⟨j, fun h => hj (hW'le h)⟩`. Establish `hsupp : W' ∈ (divCycle W u).support`. Rewrite using `[Finsupp.mem_support_iff]`.

Simplify using `only [divCycle, fundCycle, Finsupp.onFinset_apply]`. Rewrite using `[if_pos ⟨hW', hrel'⟩]`. Conclude with `localMult_ne_zero_of_mem_minimalPrimes hW'`. Establish `hu'W' : linForm u' ∉ W'` using `hadm W' hsupp`. Establish `: W'.IsPrime` using `hW'.1.1`.

Establish `: W.IsPrime` using `hW.isPrime`. Establish `hWW' : W ≤ W'` using `le_sup_left.trans hW'.1.2`. Establish `huW' : linForm u ∈ W'` using `hW'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hu'W'' : linForm u' ∈ W''` using `hmin''.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Set `f` to `Ideal.Quotient.mk W`.

Establish `hf : Function.Surjective f` using `Ideal.Quotient.mk_surjective`. Establish `hker : RingHom.ker f = W` using `Ideal.mk_ker`. Establish `: (W'.map f).IsPrime` using `Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hWW')`. Establish `: (W''.map f).IsPrime` using `Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hWW'.trans hW'le)`. Establish `: IsDomain (MvPolynomial (Fin n) ℂ ⧸ W)` using `Ideal.Quotient.isDomain W`.

Establish `: (⊥ : Ideal (MvPolynomial (Fin n) ℂ ⧸ W)).IsPrime` using `Ideal.isPrime_bot`. Establish `h0 : (⊥ : Ideal (MvPolynomial (Fin n) ℂ ⧸ W)) < W'.map f`. Use `bot_lt_iff_ne_bot.mpr fun h => hu ?_` and prove the remaining obligations. Establish `hm` using `Ideal.mem_map_of_mem f huW'`. Rewrite `hm` using `[h, Ideal.mem_bot]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp hm`. Establish `h1 : W'.map f < W''.map f`. Use `lt_of_le_of_ne (Ideal.map_mono hW'le) fun h => hu'W' ?_` and prove the remaining obligations. Establish `hm` using `Ideal.mem_map_of_mem f hu'W''`. Rewrite `hm` using `[← h, ← Ideal.mem_comap, Ideal.comap_map_of_surjective' f hf, hker, sup_eq_left.mpr hWW']`.

Conclude with `hm`. Establish `e1` using `Ideal.height_add_one_le_of_lt_of_isPrime h0`. Establish `e2` using `Ideal.height_add_one_le_of_lt_of_isPrime h1`. Establish `e3 : (W''.map f).height ≤ 1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hmin''`. Rewrite `e1` using `[Ideal.height_bot, zero_add]`.

Establish `h2 : (2 : ℕ∞) ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd h2 (by norm_num)`.
-/
theorem ProperSymm.proof : ProperSymm.Statement := by
  intro n W u u' hW hu hu' hadm W'' hW'' hlu
  classical
  have hval := Finsupp.mem_support_iff.mp hW''
  simp only [divCycle, fundCycle, Finsupp.onFinset_apply] at hval
  have hrel : W'' ∈ relComps (W ⊔ span {linForm u'}) := by
    by_contra h
    exact hval (if_neg h)
  obtain ⟨hmin'', hrel''⟩ := hrel
  have : W''.IsPrime := hmin''.1.1
  have hle : W ⊔ span {linForm u} ≤ W'' :=
    sup_le (le_sup_left.trans hmin''.1.2) ((span_singleton_le_iff_mem _).mpr hlu)
  obtain ⟨W', hW', hW'le⟩ := Ideal.exists_minimalPrimes_le hle
  have hrel' : IsRelevant W' := by
    obtain ⟨j, hj⟩ := hrel''
    exact ⟨j, fun h => hj (hW'le h)⟩
  have hsupp : W' ∈ (divCycle W u).support := by
    rw [Finsupp.mem_support_iff]
    simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
    rw [if_pos ⟨hW', hrel'⟩]
    exact localMult_ne_zero_of_mem_minimalPrimes hW'
  have hu'W' : linForm u' ∉ W' := hadm W' hsupp
  have : W'.IsPrime := hW'.1.1
  have : W.IsPrime := hW.isPrime
  have hWW' : W ≤ W' := le_sup_left.trans hW'.1.2
  have huW' : linForm u ∈ W' := hW'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hu'W'' : linForm u' ∈ W'' :=
    hmin''.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  let f := Ideal.Quotient.mk W
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = W := Ideal.mk_ker
  have : (W'.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hWW')
  have : (W''.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hWW'.trans hW'le)
  have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ W) := Ideal.Quotient.isDomain W
  have : (⊥ : Ideal (MvPolynomial (Fin n) ℂ ⧸ W)).IsPrime := Ideal.isPrime_bot
  have h0 : (⊥ : Ideal (MvPolynomial (Fin n) ℂ ⧸ W)) < W'.map f := by
    refine bot_lt_iff_ne_bot.mpr fun h => hu ?_
    have hm := Ideal.mem_map_of_mem f huW'
    rw [h, Ideal.mem_bot] at hm
    exact Ideal.Quotient.eq_zero_iff_mem.mp hm
  have h1 : W'.map f < W''.map f := by
    refine lt_of_le_of_ne (Ideal.map_mono hW'le) fun h => hu'W' ?_
    have hm := Ideal.mem_map_of_mem f hu'W''
    rw [← h, ← Ideal.mem_comap, Ideal.comap_map_of_surjective' f hf, hker,
      sup_eq_left.mpr hWW'] at hm
    exact hm
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e3 : (W''.map f).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin''
  rw [Ideal.height_bot, zero_add] at e1
  have h2 : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (W'.map f).height + 1 := by gcongr
      _ ≤ (W''.map f).height := e2
      _ ≤ 1 := e3
  exact absurd h2 (by norm_num)

end GroundTheory.Heights₂.Heights
