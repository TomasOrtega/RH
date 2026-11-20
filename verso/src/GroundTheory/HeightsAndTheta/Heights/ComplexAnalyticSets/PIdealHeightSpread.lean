import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIdealHeightSpread
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `R _ _ I P _ _`. Establish `hF` using `I.finite_minimalPrimes_of_isNoetherianRing R`. Set `a : Ideal R → R` to `fun p => if h : ¬ (p : Set R) ⊆ P then Classical.choose (Set.not_subset.mp h) else 1`. Establish `ha : ∀ p : Ideal R, ¬ p ≤ P → a p ∈ p ∧ a p ∉ P`. Introduce `p h`.

Establish `h' : ¬ (p : Set R) ⊆ P` using `h`. Simplify using `only [a, dif_pos h']`. Conclude with `Classical.choose_spec (Set.not_subset.mp h')`. Set `s : Finset (Ideal R)` to `hF.toFinset.filter (fun p => ¬ p ≤ P)`. Use `⟨∏ p ∈ s, a p, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.IsPrime.prod_mem_iff]`. Introduce and unpack `⟨p, hp, hpP⟩`. Conclude with `(ha p (Finset.mem_filter.mp hp).2).2 hpP`. Introduce `Q _ _ hgQ`. Rewrite using `[Ideal.height_eq_inf_minimalPrimes (I.map (algebraMap R (Localization.AtPrime Q)))]`.

Use `le_iInf₂ fun J hJ => ?_` and prove the remaining obligations. Establish `hJp : J.IsPrime` using `hJ.isPrime`. Establish `hmin : J.comap (algebraMap R (Localization.AtPrime Q)) ∈ I.minimalPrimes`. Rewrite `hJ` using `[IsLocalization.minimalPrimes_map Q.primeCompl]`. Conclude with `hJ`.

Use `set p := J.comap (algebraMap R (Localization.AtPrime Q)) with hpdef`. Establish `hpp : p.IsPrime` using `hmin.1.1`. Establish `hpQ : p ≤ Q`. Introduce `x hx`. Assume the negation of the conclusion as `hxQ`.

Establish `hu` using `IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hxQ⟩ : Q.primeCompl)`. Conclude with `hJp.ne_top (Ideal.eq_top_of_isUnit_mem J hx hu)`. Establish `hpP : p ≤ P`. Assume the negation of the conclusion as `hnot`. Apply `hgQ` to reduce the goal to its premises.

Apply `hpQ` to reduce the goal to its premises. Establish `hps : p ∈ s` using `Finset.mem_filter.mpr ⟨hF.mem_toFinset.mpr hmin, hnot⟩`. Conclude with `Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hps) (ha p hnot).1`. Establish `hdisj : Disjoint (P.primeCompl : Set R) (p : Set R)`. Rewrite using `[Set.disjoint_left]`.

Introduce `x hx hxp`. Conclude with `hx (hpP hxp)`. Establish `hJh : J.height = p.height` using `(IsLocalization.height_under Q.primeCompl J).symm`. Rewrite using `[hJh, ← IsLocalization.height_map_of_disjoint P.primeCompl (S := Localization.AtPrime P) p hdisj]`. Conclude with `Ideal.height_mono (Ideal.map_mono hmin.1.2)`.
-/
theorem IdealHeightSpread.proof : IdealHeightSpread.Statement := by
  intro R _ _ I P _ _
  classical
  have hF := I.finite_minimalPrimes_of_isNoetherianRing R

  let a : Ideal R → R := fun p =>
    if h : ¬ (p : Set R) ⊆ P then Classical.choose (Set.not_subset.mp h) else 1
  have ha : ∀ p : Ideal R, ¬ p ≤ P → a p ∈ p ∧ a p ∉ P := by
    intro p h
    have h' : ¬ (p : Set R) ⊆ P := h
    simp only [a, dif_pos h']
    exact Classical.choose_spec (Set.not_subset.mp h')
  let s : Finset (Ideal R) := hF.toFinset.filter (fun p => ¬ p ≤ P)
  refine ⟨∏ p ∈ s, a p, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hpP⟩
    exact (ha p (Finset.mem_filter.mp hp).2).2 hpP
  · intro Q _ _ hgQ
    rw [Ideal.height_eq_inf_minimalPrimes (I.map (algebraMap R (Localization.AtPrime Q)))]
    refine le_iInf₂ fun J hJ => ?_
    have hJp : J.IsPrime := hJ.isPrime
    have hmin : J.comap (algebraMap R (Localization.AtPrime Q)) ∈ I.minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl] at hJ
      exact hJ
    set p := J.comap (algebraMap R (Localization.AtPrime Q)) with hpdef
    have hpp : p.IsPrime := hmin.1.1

    have hpQ : p ≤ Q := by
      intro x hx
      by_contra hxQ
      have hu := IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hxQ⟩ : Q.primeCompl)
      exact hJp.ne_top (Ideal.eq_top_of_isUnit_mem J hx hu)

    have hpP : p ≤ P := by
      by_contra hnot
      apply hgQ
      apply hpQ
      have hps : p ∈ s := Finset.mem_filter.mpr ⟨hF.mem_toFinset.mpr hmin, hnot⟩
      exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hps) (ha p hnot).1
    have hdisj : Disjoint (P.primeCompl : Set R) (p : Set R) := by
      rw [Set.disjoint_left]
      intro x hx hxp
      exact hx (hpP hxp)
    have hJh : J.height = p.height := (IsLocalization.height_under Q.primeCompl J).symm
    rw [hJh, ← IsLocalization.height_map_of_disjoint P.primeCompl (S := Localization.AtPrime P) p hdisj]
    exact Ideal.height_mono (Ideal.map_mono hmin.1.2)

end GroundTheory.Heights₂.Heights
