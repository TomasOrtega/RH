import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel`. Use `hP.multiProj.isPrime` as an intermediate fact. Introduce `W' hW' hW'rel hW'W`. Establish `hW'p : W'.IsPrime` using `hW'.1.1`. Establish `hbl : blowUpOf P u ≤ W'` using `le_trans le_sup_left hW'.1.2`.

Establish `hmh : IsMultiHomogIdeal W'` using `MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W' (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c) (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'`. Establish `hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W'` using `iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩`. Establish `: (blowUpOf P u).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨φ, hφ⟩` from `hiso O K ι J P u W' hbl`. Take `⟨hlocT, hunitT⟩` from `HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl`.

Establish `: IsLocalRing (blowUpLocRing P u W')` using `φ.isLocalRing`. Establish `hPW : P ≤ W` using `le_sup_left.trans hWmin.1.2`. Establish `hWp : W.IsPrime` using `hWmin.1.1`. Take `⟨hlocA, hunitA⟩` from `HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW`. Set `𝔫 : Ideal (blowUpOverLoc P W u)` to `(IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)`.

Establish `hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal`. Establish `hle : IsLocalRing.maximalIdeal (homLocRing P W) ≤ 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))`. Introduce and unpack `⟨z, hz⟩ ha`. Rewrite `ha` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Take `⟨b, f, g, hf, hg, hgW, rfl⟩` from `(HomLocRingMem.proof O K ι P W hWp hPW z).mp hz`.

Establish `hfW : f ∈ W`. Assume the negation of the conclusion as `hfW`. Conclude with `ha ((hunitA b f g hf hg hgW hz).mpr hfW)`. Establish `hgW' : liftForm (J` using `J) g ∉ W' := fun h => hgW (by rw [← hW'W]; exact h)`. Establish `hfW' : liftForm (J` using `J) f ∈ W' := by rw [← hW'W] at hfW; exact hfW`.

Establish `hlf` using `isMultiHomog_liftForm (J := J) hf`. Establish `hlg` using `isMultiHomog_liftForm (J := J) hg`. Establish `hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u) (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm f)) / algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u) (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g) …` using `Subring.subset_closure ⟨liftMDeg b, _, _, hlf, hlg, hgW', rfl⟩`. Establish `hnu : ¬ IsUnit (⟨_, hz'⟩ : homLocRing (blowUpOf P u) W')` using `fun h => (hunitT _ _ _ hlf hlg hgW' hz').mp h hfW'`. Establish `hφz : Subring.inclusion hBR (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩) = φ ⟨_, hz'⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hφ _ _ _ hlf hlg hgW', blowUpEval_liftForm, blowUpEval_liftForm]`. Both sides reduce to the same expression. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, hφz, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]`. Conclude with `hnu`.

Establish `hne : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) ≠ ⊤` using `Ideal.comap_ne_top _ (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)`. Rewrite using `[le_antisymm (IsLocalRing.le_maximalIdeal hne) hle]`. Use `infer_instance`. Take `⟨hfinite, -⟩` from `hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel`. Establish `h𝔫 : 𝔫.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔫 hcomapA`.

Use `⟨hBR, 𝔫, h𝔫, ?_⟩` and prove the remaining obligations. Use `letI := (Subring.inclusion hBR).toAlgebra`. Use `h𝔫.isPrime` as an intermediate fact. Use `(isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨s, hs⟩`.

Assume the negation of the conclusion as `h`. Conclude with `hs ((IsLocalRing.mem_maximalIdeal _).mpr h)`. Introduce and unpack `⟨z, hz⟩`. Take `⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩` from `hfrac O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hW' hW'rel hW'W z hz`. Use `⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩` and prove the remaining obligations.

Introduce `hm`. Establish `hm'` using `(IsLocalRing.mem_maximalIdeal _).mp hm`. Conclude with `hm' (IsUnit.of_mul_eq_one (⟨t, ht⟩ : blowUpLocRing P u W') (Subtype.ext hst))`. Introduce `a a' h`. Conclude with `⟨1, by rw [Subring.inclusion_injective hBR h]⟩`.
-/
theorem BlowUpOverLocPointMax.proof (hfin : BlowUpOverLocFinite.Statement.{u})
    (hiso : BlowUpLocRingIso.Statement.{u}) (hfrac : BlowUpLocRingFrac.Statement.{u}) : BlowUpOverLocPointMax.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW' hW'rel hW'W
  have hW'p : W'.IsPrime := hW'.1.1
  have hbl : blowUpOf P u ≤ W' := le_trans le_sup_left hW'.1.2
  have hmh : IsMultiHomogIdeal W' :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' :=
    iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u W' hbl
  obtain ⟨hlocT, hunitT⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hWp : W.IsPrime := hWmin.1.1
  obtain ⟨hlocA, hunitA⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  let 𝔫 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)

  have hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (homLocRing P W) ≤
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rintro ⟨z, hz⟩ ha
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
      obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (HomLocRingMem.proof O K ι P W hWp hPW z).mp hz
      have hfW : f ∈ W := by
        by_contra hfW
        exact ha ((hunitA b f g hf hg hgW hz).mpr hfW)
      have hgW' : liftForm (J := J) g ∉ W' := fun h => hgW (by rw [← hW'W]; exact h)
      have hfW' : liftForm (J := J) f ∈ W' := by rw [← hW'W] at hfW; exact hfW
      have hlf := isMultiHomog_liftForm (J := J) hf
      have hlg := isMultiHomog_liftForm (J := J) hg
      have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm f)) /
          algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
          homLocRing (blowUpOf P u) W' :=
        Subring.subset_closure ⟨liftMDeg b, _, _, hlf, hlg, hgW', rfl⟩
      have hnu : ¬ IsUnit (⟨_, hz'⟩ : homLocRing (blowUpOf P u) W') :=
        fun h => (hunitT _ _ _ hlf hlg hgW' hz').mp h hfW'
      have hφz : Subring.inclusion hBR (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩) =
          φ ⟨_, hz'⟩ := by
        apply Subtype.ext
        rw [hφ _ _ _ hlf hlg hgW', blowUpEval_liftForm, blowUpEval_liftForm]
        rfl
      rw [Ideal.mem_comap, Ideal.mem_comap, hφz, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_map_iff]
      exact hnu
    have hne : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) ≠ ⊤ :=
      Ideal.comap_ne_top _ (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hne) hle]
    infer_instance
  obtain ⟨hfinite, -⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have h𝔫 : 𝔫.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔫 hcomapA
  refine ⟨hBR, 𝔫, h𝔫, ?_⟩
  letI := (Subring.inclusion hBR).toAlgebra
  have := h𝔫.isPrime
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)
  · rintro ⟨z, hz⟩
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ :=
      hfrac O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hW' hW'rel hW'W z hz
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    intro hm
    have hm' := (IsLocalRing.mem_maximalIdeal _).mp hm
    exact hm' (IsUnit.of_mul_eq_one (⟨t, ht⟩ : blowUpLocRing P u W') (Subtype.ext hst))
  · intro a a' h
    exact ⟨1, by rw [Subring.inclusion_injective hBR h]⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
