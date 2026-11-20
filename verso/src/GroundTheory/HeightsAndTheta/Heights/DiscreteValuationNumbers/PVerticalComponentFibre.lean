import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalComponentFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP f b hf hfP W hW hrel hϖW`. Establish `hWp : W.IsPrime` using `hW.1.1`. Establish `hPp : P.IsPrime` using `hP.multiProj.isPrime`. Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.2`. Establish `hϖP : (C ϖ : MRing ι O) ∉ P`.

Introduce `hmem`. Establish `: ϖ ∈ P.comap (C : O →+* MRing ι O)` using `hmem`. Rewrite `this` using `[hP.noTorsion, Ideal.mem_bot]`. Conclude with `hϖ.ne_zero this`. Establish `hmin : W ∈ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).minimalPrimes`.

Use `⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hϖW)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `Q ⟨hQ, hQle⟩ hQW`. Assume the negation of the conclusion as `hWQ`. Establish `hlt : Q < W` using `lt_of_le_of_ne hQW (fun e => hWQ (e ▸ le_rfl))`. Establish `hPQ : P ≤ Q` using `le_sup_left.trans hQle`.

Establish `hϖQ : (C ϖ : MRing ι O) ∈ Q` using `hQle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Set `π` to `Ideal.Quotient.mk P`. Establish `hsurj : Function.Surjective π` using `Ideal.Quotient.mk_surjective`. Establish `: (W.map π).IsPrime` using `Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPW)`. Establish `: (Q.map π).IsPrime` using `Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPQ)`.

Establish `hle1 : (W.map π).height ≤ 1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hW`. Establish `hlt' : Q.map π < W.map π`. Use `(Ideal.map_mono hlt.le).lt_of_not_ge fun e => hlt.not_ge ?_` and prove the remaining obligations. Use `Ideal.comap_mono (f := π) e` as an intermediate fact. Rewrite `this` using `[Ideal.comap_map_of_surjective' π hsurj, Ideal.comap_map_of_surjective' π hsurj, Ideal.mk_ker, sup_eq_left.mpr hPW, sup_eq_left.mpr hPQ]`. Then use the resulting hypothesis.

Establish `: (W.map π).FiniteHeight` using `⟨Or.inr (hle1.trans_lt (WithTop.coe_lt_top 1)).ne⟩`. Establish `h0` using `(Ideal.height_strict_mono_of_isPrime_of_isPrime hlt').trans_le hle1`. Rewrite `h0` using `[Order.lt_one_iff, Ideal.height_eq_zero_iff]`. Establish `hbot : Q.map π ≤ ⊥` using `h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le`. Establish `: π (C ϖ) ∈ (⊥ : Ideal (MRing ι O ⧸ P))` using `hbot (Ideal.mem_map_of_mem π hϖQ)`.

Rewrite `this` using `[Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hϖP this`. Establish `hdiv : divCycle P (C ϖ) W ≠ 0`. Unfold `divCycle`. Rewrite using `[dif_pos ⟨hmin, hrel⟩]`.

Establish `hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈ ((P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map (algebraMap (MRing ι O) (Localization.AtPrime W))).minimalPrimes`. Rewrite using `[IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W), Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]`. Conclude with `hmin`. Establish `hne` using `ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm`. Establish `: Nontrivial (Localization.AtPrime W ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map (algebraMap (MRing ι O) (Localization.AtPrime W)))` using `Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)`.

Establish `hpos` using `Module.length_pos (R := Localization.AtPrime W) (M := Localization.AtPrime W ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map (algebraMap (MRing ι O) (Localization.AtPrime W)))`. Rewrite using `[multAt, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]`. Conclude with `(ENat.toNat_pos hpos.ne' hne).ne'` after adjusting the coercions. Conclude with `(h O ϖ hϖ K ι P d hP).2 W hdiv`.
-/
theorem VerticalComponentFibre.proof (h : FibreVarieties.Statement.{0}) :
    VerticalComponentFibre.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP f b hf hfP W hW hrel hϖW
  have hWp : W.IsPrime := hW.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro hmem
    have : ϖ ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hP.noTorsion, Ideal.mem_bot] at this
    exact hϖ.ne_zero this

  have hmin : W ∈ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).minimalPrimes := by
    refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hϖW)⟩, ?_⟩
    rintro Q ⟨hQ, hQle⟩ hQW
    by_contra hWQ
    have hlt : Q < W := lt_of_le_of_ne hQW (fun e => hWQ (e ▸ le_rfl))
    have hPQ : P ≤ Q := le_sup_left.trans hQle
    have hϖQ : (C ϖ : MRing ι O) ∈ Q := hQle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    let π := Ideal.Quotient.mk P
    have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
    have : (W.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPW)
    have : (Q.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPQ)
    have hle1 : (W.map π).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
    have hlt' : Q.map π < W.map π := by
      refine (Ideal.map_mono hlt.le).lt_of_not_ge fun e => hlt.not_ge ?_
      have := Ideal.comap_mono (f := π) e
      rwa [Ideal.comap_map_of_surjective' π hsurj, Ideal.comap_map_of_surjective' π hsurj,
        Ideal.mk_ker, sup_eq_left.mpr hPW, sup_eq_left.mpr hPQ] at this
    have : (W.map π).FiniteHeight := ⟨Or.inr (hle1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
    have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt').trans_le hle1
    rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
    have hbot : Q.map π ≤ ⊥ := h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    have : π (C ϖ) ∈ (⊥ : Ideal (MRing ι O ⧸ P)) := hbot (Ideal.mem_map_of_mem π hϖQ)
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hϖP this

  have hdiv : divCycle P (C ϖ) W ≠ 0 := by
    unfold divCycle
    rw [dif_pos ⟨hmin, hrel⟩]
    have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
        ((P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map
          (algebraMap (MRing ι O) (Localization.AtPrime W))).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W),
        Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
      exact hmin
    have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
    have : Nontrivial (Localization.AtPrime W ⧸
        (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map
          (algebraMap (MRing ι O) (Localization.AtPrime W))) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
    have hpos := Module.length_pos (R := Localization.AtPrime W)
      (M := Localization.AtPrime W ⧸
        (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map (algebraMap (MRing ι O) (Localization.AtPrime W)))
    rw [multAt, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
    exact_mod_cast (ENat.toNat_pos hpos.ne' hne).ne'
  exact (h O ϖ hϖ K ι P d hP).2 W hdiv

end GroundTheory.Heights₂.Heights.NumbersDVR
