import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Avoid

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

/- English proof (translation)
Use `set T := S.filter (fun W => ∀ W' ∈ S, W ≤ W' → W' = W) with hT`. Establish `hTS : ∀ W ∈ T, W ∈ S` using `fun W hW => (Finset.mem_filter.mp hW).1`. Establish `hTmax : ∀ W ∈ T, ∀ W' ∈ S, W ≤ W' → W' = W` using `fun W hW => (Finset.mem_filter.mp hW).2`. Establish `hle : ∀ W ∈ S, ∃ W' ∈ T, W ≤ W'`. Introduce `W hW`.

Take `⟨W', hWW', hW'⟩` from `(S.finite_toSet).exists_le_maximal hW`. Conclude with `⟨W', Finset.mem_filter.mpr ⟨hW'.prop, fun W'' hW'' h => le_antisymm (hW'.2 hW'' h) h⟩, hWW'⟩`. Establish `hsep : ∀ W ∈ T, ∃ (a : MRing ι R) (A : K → ℕ), IsMultiHomog a A ∧ a ∉ W ∧ ∀ W' ∈ T.erase W, a ∈ W'`. Introduce `W hW`. Use `(hS W (hTS W hW)).1` as an intermediate fact.

Use `exists_form_separator (T.erase W) fun W' hW' => ⟨(hS W' (hTS W' (Finset.mem_of_mem_erase hW'))).2.1, fun hle' => Finset.ne_of_mem_erase hW' ?_⟩` and prove the remaining obligations. Conclude with `(hTmax W' (Finset.mem_of_mem_erase hW') W (hTS W hW) hle').symm`. Use `choose! a A haH haW haMem using hsep`. Use `set e : K → ℕ := e₀ + ∑ W ∈ T, A W with he`. Establish `hAe : ∀ W ∈ T, A W ≤ e` using `fun W hW => le_add_left (Finset.single_le_sum (f := A) (fun _ _ => fun _ => Nat.zero_le _) hW)`.

Establish `hmon : ∀ W ∈ T, ∃ m : MRing ι R, IsMultiHomog m (e - A W) ∧ m ∉ W`. Introduce `W hW`. Use `(hS W (hTS W hW)).1` as an intermediate fact. Conclude with `exists_form_not_mem_of_isRelevant (hS W (hTS W hW)).2.2 _`. Use `choose! m hmH hmW using hmon`.

Use `⟨e, ∑ W ∈ T, a W * m W, ?_, le_self_add, ?_⟩` and prove the remaining obligations. Use `IsWeightedHomogeneous.sum _ _ _ fun W hW => ?_` and prove the remaining obligations. Use `(haH W hW).mul (hmH W hW)` as an intermediate fact. Rewrite `this` using `[add_tsub_cancel_of_le (hAe W hW)]`. Then use the resulting hypothesis. Establish `key : ∀ W₀ ∈ T, (∑ W ∈ T, a W * m W) ∉ W₀`.

Introduce `W₀ hW₀ hmem`. Establish `hp` using `(hS W₀ (hTS W₀ hW₀)).1`. Rewrite `hmem` using `[← Finset.add_sum_erase _ _ hW₀]`. Establish `hrest : (∑ W ∈ T.erase W₀, a W * m W) ∈ W₀` using `Ideal.sum_mem _ fun W hW => Ideal.mul_mem_right _ _ (haMem W (Finset.mem_of_mem_erase hW) W₀ (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hW).symm, hW₀⟩))`. Break down `hp.mem_or_mem ((Ideal.add_mem_iff_left _ hrest).mp hmem) with h2 | h2` into its components or cases.

Conclude with `haW W₀ hW₀ h2`. Conclude with `hmW W₀ hW₀ h2`. Introduce `W hW hmem`. Take `⟨W', hW', hle'⟩` from `hle W hW`. Conclude with `key W' hW' (hle' hmem)`.
-/
theorem exists_form_avoid_primes (S : Finset (Ideal (MRing ι R)))
    (hS : ∀ W ∈ S, W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W) (e₀ : K → ℕ) :
    ∃ (e : K → ℕ) (h : MRing ι R), IsMultiHomog h e ∧ e₀ ≤ e ∧ ∀ W ∈ S, h ∉ W := by
  classical
  set T := S.filter (fun W => ∀ W' ∈ S, W ≤ W' → W' = W) with hT
  have hTS : ∀ W ∈ T, W ∈ S := fun W hW => (Finset.mem_filter.mp hW).1
  have hTmax : ∀ W ∈ T, ∀ W' ∈ S, W ≤ W' → W' = W := fun W hW => (Finset.mem_filter.mp hW).2
  have hle : ∀ W ∈ S, ∃ W' ∈ T, W ≤ W' := by
    intro W hW
    obtain ⟨W', hWW', hW'⟩ := (S.finite_toSet).exists_le_maximal hW
    exact ⟨W', Finset.mem_filter.mpr ⟨hW'.prop, fun W'' hW'' h => le_antisymm (hW'.2 hW'' h) h⟩, hWW'⟩
  have hsep : ∀ W ∈ T, ∃ (a : MRing ι R) (A : K → ℕ), IsMultiHomog a A ∧ a ∉ W ∧
      ∀ W' ∈ T.erase W, a ∈ W' := by
    intro W hW
    have := (hS W (hTS W hW)).1
    refine exists_form_separator (T.erase W) fun W' hW' => ⟨(hS W' (hTS W' (Finset.mem_of_mem_erase hW'))).2.1,
      fun hle' => Finset.ne_of_mem_erase hW' ?_⟩
    exact (hTmax W' (Finset.mem_of_mem_erase hW') W (hTS W hW) hle').symm
  choose! a A haH haW haMem using hsep
  set e : K → ℕ := e₀ + ∑ W ∈ T, A W with he
  have hAe : ∀ W ∈ T, A W ≤ e := fun W hW =>
    le_add_left (Finset.single_le_sum (f := A) (fun _ _ => fun _ => Nat.zero_le _) hW)
  have hmon : ∀ W ∈ T, ∃ m : MRing ι R, IsMultiHomog m (e - A W) ∧ m ∉ W := by
    intro W hW
    have := (hS W (hTS W hW)).1
    exact exists_form_not_mem_of_isRelevant (hS W (hTS W hW)).2.2 _
  choose! m hmH hmW using hmon
  refine ⟨e, ∑ W ∈ T, a W * m W, ?_, le_self_add, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun W hW => ?_
    have := (haH W hW).mul (hmH W hW)
    rwa [add_tsub_cancel_of_le (hAe W hW)] at this
  · have key : ∀ W₀ ∈ T, (∑ W ∈ T, a W * m W) ∉ W₀ := by
      intro W₀ hW₀ hmem
      have hp := (hS W₀ (hTS W₀ hW₀)).1
      rw [← Finset.add_sum_erase _ _ hW₀] at hmem
      have hrest : (∑ W ∈ T.erase W₀, a W * m W) ∈ W₀ :=
        Ideal.sum_mem _ fun W hW => Ideal.mul_mem_right _ _ (haMem W (Finset.mem_of_mem_erase hW) W₀
          (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hW).symm, hW₀⟩))
      rcases hp.mem_or_mem ((Ideal.add_mem_iff_left _ hrest).mp hmem) with h2 | h2
      · exact haW W₀ hW₀ h2
      · exact hmW W₀ hW₀ h2
    intro W hW hmem
    obtain ⟨W', hW', hle'⟩ := hle W hW
    exact key W' hW' (hle' hmem)

end Avoid

/- English proof (translation)
Establish `: H.IsPrime` using `hH.1.1`. Establish `hPH : P ≤ H` using `le_sup_left.trans hH.1.2`. Take `⟨Q, hQ, hQH⟩` from `Ideal.exists_minimalPrimes_le (sup_le hPH ((Ideal.span_singleton_le_iff_mem _).mpr hyH))`. Establish `: Q.IsPrime` using `hQ.1.1`. Establish `hPQ : P ≤ Q` using `le_sup_left.trans hQ.1.2`.

Establish `hyQ : y ∈ Q` using `hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))`. It suffices to establish `hQH' : Q = H by rw [← hQH']; exact hQ`. Assume the negation of the conclusion as `hne`. Establish `hlt : Q < H` using `lt_of_le_of_ne hQH hne`. Set `φ` to `Ideal.Quotient.mk P`.

Establish `hφ : Function.Surjective φ` using `Ideal.Quotient.mk_surjective`. Establish `hHm : (H.map φ).IsPrime` using `Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])`. Establish `hQm : (Q.map φ).IsPrime` using `Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])`. Establish `hcomap : ∀ I : Ideal A, P ≤ I → (I.map φ).comap φ = I` using `fun I hI => by`. Rewrite using `[Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI]`.

Establish `h_lt : Q.map φ < H.map φ` using `(Ideal.map_mono hlt.le).lt_of_not_ge fun h => hlt.not_ge (by`. Simplify `Ideal.comap_mono (f := φ) h)` using `only [hcomap Q hPQ, hcomap H hPH]`. Establish `h1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hH`. Establish `: (H.map φ).FiniteHeight` using `⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩`. Establish `h0` using `(Ideal.height_strict_mono_of_isPrime_of_isPrime h_lt).trans_le h1`.

Rewrite `h0` using `[Order.lt_one_iff, Ideal.height_eq_zero_iff]`. Establish `: (⊥ : Ideal (A ⧸ P)).IsPrime` using `Ideal.isPrime_bot`. Establish `h0' : Q.map φ ∈ (⊥ : Ideal (A ⧸ P)).minimalPrimes` using `h0`. Rewrite `h0'` using `[Ideal.minimalPrimes_eq_subsingleton_self]`. Establish `: φ y ∈ Q.map φ` using `Ideal.mem_map_of_mem φ hyQ`.

Rewrite `this` using `[show Q.map φ = ⊥ from h0', Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hy this`.
-/
theorem mem_minimalPrimes_sup_span_of_mem {A : Type*} [CommRing A] [IsNoetherianRing A] {P H : Ideal A}
    [hP : P.IsPrime] {x y : A} (hH : H ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hy : y ∉ P)
    (hyH : y ∈ H) : H ∈ (P ⊔ Ideal.span {y}).minimalPrimes := by
  have : H.IsPrime := hH.1.1
  have hPH : P ≤ H := le_sup_left.trans hH.1.2
  obtain ⟨Q, hQ, hQH⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPH ((Ideal.span_singleton_le_iff_mem _).mpr hyH))
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hyQ : y ∈ Q := hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
  suffices hQH' : Q = H by rw [← hQH']; exact hQ
  by_contra hne
  have hlt : Q < H := lt_of_le_of_ne hQH hne
  let φ := Ideal.Quotient.mk P
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hHm : (H.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])
  have hQm : (Q.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])
  have hcomap : ∀ I : Ideal A, P ≤ I → (I.map φ).comap φ = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI]
  have h_lt : Q.map φ < H.map φ := (Ideal.map_mono hlt.le).lt_of_not_ge fun h => hlt.not_ge (by
    simpa only [hcomap Q hPQ, hcomap H hPH] using Ideal.comap_mono (f := φ) h)
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hH
  have : (H.map φ).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime h_lt).trans_le h1
  rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
  have : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have h0' : Q.map φ ∈ (⊥ : Ideal (A ⧸ P)).minimalPrimes := h0
  rw [Ideal.minimalPrimes_eq_subsingleton_self] at h0'
  have : φ y ∈ Q.map φ := Ideal.mem_map_of_mem φ hyQ
  rw [show Q.map φ = ⊥ from h0', Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact hy this

/- English proof (translation)
Unfold `divCycle at h`. Use `split_ifs at h with hW`. Conclude with `hW`. Conclude with `absurd rfl h`.
-/
theorem relevant_minimal_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P W : Ideal (MRing ι R)} {x : MRing ι R} (h : divCycle P x W ≠ 0) :
    W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW
  · exact absurd rfl h

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD e₀`. Establish `hPp : P.IsPrime` using `hP.multiProj.isPrime`. Establish `hD1` using `hD.1`. Take `⟨bf, bg, hf, hg, -⟩` from `hD1.degrees`. Establish `hfin : ∀ x : MRing ι O, {W | W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W}.Finite` using `fun x => (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun W hW => hW.1`.

Establish `hmin : ∀ (x : MRing ι O) (c : K → ℕ), IsMultiHomog x c → ∀ W ∈ {W | W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W}, W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W` using `fun x c hx W hW => ⟨hW.1.1.1, MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hx) hW.1, hW.2⟩`. Take `⟨e, h, hh, he, hS⟩` from `exists_form_avoid_primes (insert P ((hfin f).toFinset ∪ (hfin g).toFinset)) (by`. Introduce `W hW`. Break down `Finset.mem_insert.mp hW with rfl | hW` into its components or cases. Conclude with `⟨hPp, hP.multiProj.multiHomog, hP.multiProj.relevant⟩`.

Break down `Finset.mem_union.mp hW with hW | hW` into its components or cases. Conclude with `hmin f bf hf W ((hfin f).mem_toFinset.mp hW)`. Conclude with `hmin g bg hg W ((hfin g).mem_toFinset.mp hW)) e₀`. Establish `hhP : h ∉ P` using `hS P (Finset.mem_insert_self _ _)`. Establish `hhf : ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes, IsRelevant W → h ∉ W` using `fun W hW hr => hS W (Finset.mem_insert_of_mem (Finset.mem_union_left _ ((hfin f).mem_toFinset.mpr ⟨hW, hr⟩)))`.

Establish `hhg : ∀ W ∈ (P ⊔ Ideal.span {g}).minimalPrimes, IsRelevant W → h ∉ W` using `fun W hW hr => hS W (Finset.mem_insert_of_mem (Finset.mem_union_right _ ((hfin g).mem_toFinset.mpr ⟨hW, hr⟩)))`. Establish `hG : ∀ G, ratDiv P f g G ≠ 0 → divCycle P h G = 0`. Introduce `G hG`. Assume the negation of the conclusion as `hhG`. Establish `hhG' : h ∈ G` using `(relevant_minimal_of_divCycle_ne_zero hhG).1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))`.

Distinguish the cases in `hfG : divCycle P f G = 0`. Establish `hgG : divCycle P g G ≠ 0` using `fun h0 => hG (by unfold ratDiv; rw [hfG, h0, sub_zero])`. Take `⟨hm, hr⟩` from `relevant_minimal_of_divCycle_ne_zero hgG`. Conclude with `hhg G hm hr hhG'`. Take `⟨hm, hr⟩` from `relevant_minimal_of_divCycle_ne_zero hfG`.

Conclude with `hhf G hm hr hhG'`. Establish `hterm : ∀ s : MRing ι O, ∀ G, ratDiv P f g G ≠ 0 → divCycle P (s * h) G = divCycle P s G ∨ s ∈ P`. Introduce `s G hr`. Distinguish the cases in `hsP : s ∈ P`. Conclude with `Or.inr hsP`.

Use `left`. Rewrite using `[DivCycleMul.proof O K ι P s h hPp hsP hhP, Pi.add_apply, hG G hr, add_zero]`. Use `⟨e, h, hh, hhP, he, ?_, fun G _ hr => hG G hr, ?_, ?_⟩` and prove the remaining obligations. Introduce `H hH _`. Take `⟨hm, hr⟩` from `relevant_minimal_of_divCycle_ne_zero hH`.

Establish `: H.IsPrime` using `hm.1.1`. Establish `hPH : P ≤ H` using `le_sup_left.trans hm.1.2`. Establish `hhH : h ∈ H` using `hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))`. Use `IsVerticalDivisor.of_unit_off_special hD1.degrees (fun hfH => hhf H (mem_minimalPrimes_sup_span_of_mem hm hD1.num_not_mem hfH) hr hhH) (fun hgH => hhg H (mem_minimalPrimes_sup_span_of_mem hm hD1.den_not_mem hgH) hr hhH) ?_` and prove the remaining obligations. Introduce `W hW hHW hrW hϖW`.

Take `⟨u, v, hu, hv, huv⟩` from `hD1.unit_off_special W hW (hPH.trans hHW) hrW hϖW`. Conclude with `⟨u, v, hu, hv, hPH huv⟩`. Use `Nat.le_zero.mp (ciSup_le' fun G => ?_)` and prove the remaining obligations. Distinguish the cases in `hr : ratDiv P f g G.1 = 0`. Simplify using `[hr]`.

Simplify using `[hG G.1 hr]`. Introduce `s hsP`. Unfold `commonExcess`. Use `congr 1`. Use function extensionality and compare the values at `G`.

Distinguish the cases in `hr : ratDiv P f g G.1 = 0`. Simplify using `[hr]`. Break down `hterm s G.1 hr with h1 | h1` into its components or cases. Rewrite using `[h1]`. Conclude with `absurd h1 hsP`.
-/
theorem AvoidingFormExists.proof : AvoidingFormExists.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD e₀
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hD1 := hD.1
  obtain ⟨bf, bg, hf, hg, -⟩ := hD1.degrees

  have hfin : ∀ x : MRing ι O, {W | W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W}.Finite :=
    fun x => (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun W hW => hW.1
  have hmin : ∀ (x : MRing ι O) (c : K → ℕ), IsMultiHomog x c →
      ∀ W ∈ {W | W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W},
        W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W := fun x c hx W hW =>
    ⟨hW.1.1.1, MinimalPrimeMultiHomog.proof O K ι _ W
      (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hx) hW.1, hW.2⟩
  obtain ⟨e, h, hh, he, hS⟩ := exists_form_avoid_primes
    (insert P ((hfin f).toFinset ∪ (hfin g).toFinset)) (by
      intro W hW
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hPp, hP.multiProj.multiHomog, hP.multiProj.relevant⟩
      rcases Finset.mem_union.mp hW with hW | hW
      · exact hmin f bf hf W ((hfin f).mem_toFinset.mp hW)
      · exact hmin g bg hg W ((hfin g).mem_toFinset.mp hW)) e₀
  have hhP : h ∉ P := hS P (Finset.mem_insert_self _ _)
  have hhf : ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes, IsRelevant W → h ∉ W := fun W hW hr =>
    hS W (Finset.mem_insert_of_mem (Finset.mem_union_left _ ((hfin f).mem_toFinset.mpr ⟨hW, hr⟩)))
  have hhg : ∀ W ∈ (P ⊔ Ideal.span {g}).minimalPrimes, IsRelevant W → h ∉ W := fun W hW hr =>
    hS W (Finset.mem_insert_of_mem (Finset.mem_union_right _ ((hfin g).mem_toFinset.mpr ⟨hW, hr⟩)))

  have hG : ∀ G, ratDiv P f g G ≠ 0 → divCycle P h G = 0 := by
    intro G hG
    by_contra hhG
    have hhG' : h ∈ G := (relevant_minimal_of_divCycle_ne_zero hhG).1.1.2
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    by_cases hfG : divCycle P f G = 0
    · have hgG : divCycle P g G ≠ 0 := fun h0 => hG (by unfold ratDiv; rw [hfG, h0, sub_zero])
      obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hgG
      exact hhg G hm hr hhG'
    · obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hfG
      exact hhf G hm hr hhG'
  have hterm : ∀ s : MRing ι O, ∀ G, ratDiv P f g G ≠ 0 →
      divCycle P (s * h) G = divCycle P s G ∨ s ∈ P := by
    intro s G hr
    by_cases hsP : s ∈ P
    · exact Or.inr hsP
    · left
      rw [DivCycleMul.proof O K ι P s h hPp hsP hhP, Pi.add_apply, hG G hr, add_zero]
  refine ⟨e, h, hh, hhP, he, ?_, fun G _ hr => hG G hr, ?_, ?_⟩
  ·
    intro H hH _
    obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hH
    have : H.IsPrime := hm.1.1
    have hPH : P ≤ H := le_sup_left.trans hm.1.2
    have hhH : h ∈ H := hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    refine IsVerticalDivisor.of_unit_off_special hD1.degrees
      (fun hfH => hhf H (mem_minimalPrimes_sup_span_of_mem hm hD1.num_not_mem hfH) hr hhH)
      (fun hgH => hhg H (mem_minimalPrimes_sup_span_of_mem hm hD1.den_not_mem hgH) hr hhH) ?_
    intro W hW hHW hrW hϖW
    obtain ⟨u, v, hu, hv, huv⟩ := hD1.unit_off_special W hW (hPH.trans hHW) hrW hϖW
    exact ⟨u, v, hu, hv, hPH huv⟩
  ·
    refine Nat.le_zero.mp (ciSup_le' fun G => ?_)
    by_cases hr : ratDiv P f g G.1 = 0
    · simp [hr]
    · simp [hG G.1 hr]
  ·
    intro s hsP
    unfold commonExcess
    congr 1
    funext G
    by_cases hr : ratDiv P f g G.1 = 0
    · simp [hr]
    · rcases hterm s G.1 hr with h1 | h1
      · rw [h1]
      · exact absurd h1 hsP

end GroundTheory.Heights₂.Heights.NumbersDVR
