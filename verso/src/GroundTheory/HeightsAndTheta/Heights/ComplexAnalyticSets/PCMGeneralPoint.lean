import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMGeneralPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLocusOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets IsLocalRing

/- English proof (translation)
Use `set S := Localization.AtPrime W`. Use `set J := I.map (algebraMap (MvPolynomial (Fin n) ℂ) S)`. Establish `hJm : J ≤ maximalIdeal S`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`. Conclude with `Ideal.map_mono hW.1.2`.

Establish `hJ : J ≠ ⊤` using `fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))`. Establish `: Nontrivial (S ⧸ J)` using `Ideal.Quotient.nontrivial_iff.mpr hJ`. Establish `: IsLocalRing (S ⧸ J)` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective`. Establish `hdim : Ring.KrullDimLE 0 (S ⧸ J)`. Rewrite using `[Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]`.

Introduce `K hK`. Establish `: K.IsPrime` using `hK.1.1`. Establish `hKm : K ≤ maximalIdeal S` using `IsLocalRing.le_maximalIdeal hK.1.1.ne_top`. Establish `hI : I ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S)` using `Ideal.map_le_iff_le_comap.mp hK.1.2`. Establish `hKW : K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) ≤ W`.

Establish `h` using `Ideal.comap_mono (f := algebraMap (MvPolynomial (Fin n) ℂ) S) hKm`. Rewrite `h` using `[show (maximalIdeal S).comap (algebraMap (MvPolynomial (Fin n) ℂ) S) = W from Localization.AtPrime.under_maximalIdeal]`. Then use the resulting hypothesis. Establish `hWK : W ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S)` using `hW.2 ⟨Ideal.IsPrime.comap _, hI⟩ hKW`. Establish `hmK : maximalIdeal S ≤ K`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`.

Conclude with `Ideal.map_le_iff_le_comap.mpr hWK`. Rewrite using `[le_antisymm hKm hmK]`. Conclude with `maximalIdeal.isMaximal S`. Establish `h0 : ringKrullDim (S ⧸ J) = 0` using `ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdim`. Conclude with `{ exists_isWeaklyRegular := ⟨[], by simp, RingTheory.Sequence.IsWeaklyRegular.nil _ _, by simpa using h0⟩ }`.
-/
theorem isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes {n : ℕ}
    {I W : Ideal (MvPolynomial (Fin n) ℂ)} [W.IsPrime] (hW : W ∈ I.minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime W))) := by
  set S := Localization.AtPrime W
  set J := I.map (algebraMap (MvPolynomial (Fin n) ℂ) S)
  have hJm : J ≤ maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hW.1.2
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hdim : Ring.KrullDimLE 0 (S ⧸ J) := by
    rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
    intro K hK
    have : K.IsPrime := hK.1.1
    have hKm : K ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal hK.1.1.ne_top
    have hI : I ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      Ideal.map_le_iff_le_comap.mp hK.1.2
    have hKW : K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) ≤ W := by
      have h := Ideal.comap_mono (f := algebraMap (MvPolynomial (Fin n) ℂ) S) hKm
      rwa [show (maximalIdeal S).comap (algebraMap (MvPolynomial (Fin n) ℂ) S) = W from
        Localization.AtPrime.under_maximalIdeal] at h
    have hWK : W ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      hW.2 ⟨Ideal.IsPrime.comap _, hI⟩ hKW
    have hmK : maximalIdeal S ≤ K := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_le_iff_le_comap.mpr hWK
    rw [le_antisymm hKm hmK]
    exact maximalIdeal.isMaximal S
  have h0 : ringKrullDim (S ⧸ J) = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdim
  exact
    { exists_isWeaklyRegular := ⟨[], by simp, RingTheory.Sequence.IsWeaklyRegular.nil _ _, by simpa using h0⟩ }

/- English proof (translation)
Introduce `n I W hW`. Establish `: W.IsPrime` using `hW.1.1`. Take `⟨g, hgW, hg⟩` from `hOpen n I W hW.1.2 (isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes hW)`. Establish `hfin : (I.minimalPrimes \ {W}).Finite` using `(Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset Set.sdiff_subset`. Establish `hsel : ∀ W' ∈ I.minimalPrimes \ {W}, ∃ h, h ∈ W' ∧ h ∉ W`.

Introduce and unpack `W' ⟨hW', hne⟩`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hne (le_antisymm hc (hW.2 hW'.1 hc))`. Use `choose! h hh using hsel`.

Use `⟨g * ∏ W' ∈ hfin.toFinset, h W', ?_, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Break down `Ideal.IsPrime.mem_or_mem ‹W.IsPrime› hmem with h1 | h1` into its components or cases. Conclude with `hgW h1`. Take `⟨W', hW', h2⟩` from `Ideal.IsPrime.prod_mem_iff.mp h1`.

Conclude with `(hh W' (hfin.mem_toFinset.mp hW')).2 h2`. Introduce `q hq hf`. Rewrite `hf` using `[map_mul, map_prod]`. Establish `hg0 : eval q g ≠ 0` using `left_ne_zero_of_mul hf`. Establish `hp0` using `right_ne_zero_of_mul hf`.

Use `⟨fun W' hW' hqW' => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hmem : W' ∈ I.minimalPrimes \ {W}` using `⟨hW', hne⟩`. Conclude with `hp0 (Finset.prod_eq_zero (hfin.mem_toFinset.mpr hmem) (hqW' _ (hh W' hmem).1))`. Establish `hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)` using `fun x hx => RingHom.mem_ker.mpr (hq x hx)`.

Conclude with `hg _ (hW.1.2.trans hWq) fun hk => hg0 (RingHom.mem_ker.mp hk)`.
-/
theorem CMGeneralPoint.proof (hOpen : CMLocusOpen.Statement) : CMGeneralPoint.Statement := by
  intro n I W hW
  have : W.IsPrime := hW.1.1
  obtain ⟨g, hgW, hg⟩ :=
    hOpen n I W hW.1.2 (isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes hW)
  have hfin : (I.minimalPrimes \ {W}).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset Set.sdiff_subset
  have hsel : ∀ W' ∈ I.minimalPrimes \ {W}, ∃ h, h ∈ W' ∧ h ∉ W := by
    rintro W' ⟨hW', hne⟩
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hc (hW.2 hW'.1 hc))
  choose! h hh using hsel
  refine ⟨g * ∏ W' ∈ hfin.toFinset, h W', ?_, ?_⟩
  · intro hmem
    rcases Ideal.IsPrime.mem_or_mem ‹W.IsPrime› hmem with h1 | h1
    · exact hgW h1
    · obtain ⟨W', hW', h2⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact (hh W' (hfin.mem_toFinset.mp hW')).2 h2
  · intro q hq hf
    rw [map_mul, map_prod] at hf
    have hg0 : eval q g ≠ 0 := left_ne_zero_of_mul hf
    have hp0 := right_ne_zero_of_mul hf
    refine ⟨fun W' hW' hqW' => ?_, ?_⟩
    · by_contra hne
      have hmem : W' ∈ I.minimalPrimes \ {W} := ⟨hW', hne⟩
      exact hp0 (Finset.prod_eq_zero (hfin.mem_toFinset.mpr hmem) (hqW' _ (hh W' hmem).1))
    · have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
        fun x hx => RingHom.mem_ker.mpr (hq x hx)
      exact hg _ (hW.1.2.trans hWq) fun hk => hg0 (RingHom.mem_ker.mp hk)

end GroundTheory.Heights₂.Heights
