import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCentreCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel`. Use `hP.multiProj.isPrime` as an intermediate fact. Introduce `𝔫 h𝔫`. Take `⟨W', hW'p, hW'h, hW'r, hW'le, hW'c, h, hdom⟩` from `h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫`. Take `⟨h', 𝔭, h𝔭, hl⟩` from `h₂ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c`.

Set `_` to `(Subring.inclusion h).toAlgebra`. Establish `hl' : IsLocalization.AtPrime (blowUpLocRing P u W') 𝔭` using `hl`. Establish `hn𝔭 : 𝔫 ≤ 𝔭` using `fun b hb => by`. Assume the negation of the conclusion as `hb𝔭`. Conclude with `hdom b hb ((IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔭 b).2 hb𝔭)`.

Take `rfl : 𝔫 = 𝔭` from `h𝔫.eq_of_le h𝔭.ne_top hn𝔭`. Use `⟨W', hW'p, hW'h, hW'r, hW'le, le_antisymm hW'c ?_, h, hl'⟩` and prove the remaining obligations. Establish `hWp : W.IsPrime` using `hWmin.1.1`. Establish `hPW : P ≤ W` using `le_trans le_sup_left hWmin.1.2`. Establish `hWmh : IsMultiHomogIdeal W` using `MinimalPrimeMultiHomog.full O K ι _ W (SupSpanMultiHomog.full O K ι P x c hP.multiProj.multiHomog hx) hWmin`.

Take `⟨hAloc, hAunit⟩` from `HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW`. Take `⟨hfin, -⟩` from `h₃ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel`. Establish `: Algebra.IsIntegral (homLocRing P W) (blowUpOverLoc P W u)` using `Algebra.IsIntegral.of_finite _ _`. Establish `hmax : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫`. Establish `hcomap : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) = IsLocalRing.maximalIdeal (homLocRing P W)` using `IsLocalRing.eq_maximalIdeal hmax`.

Establish `: (blowUpOf P u).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨φ, hφ⟩` from `h₄ O K ι J P u W' hW'le`. Take `⟨-, hBunit⟩` from `HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hW'le`. Establish `key : ∀ (b : K → ℕ) (w : MRing ι O), IsMultiHomog w b → w ∈ W → liftForm (J` using `J) w ∈ W' := by`. Introduce `b w hw hwW`.

Assume the negation of the conclusion as `hwW'`. Take `⟨i, hi⟩` from `powMonomial_not_mem hWp hWrel b`. Establish `hg` using `isMultiHomog_powMonomial (R := O) b i`. Establish `hgW' : liftForm (J` using `J) (powMonomial b i) ∉ W' := fun hg' => hi (hW'c hg')`. Establish `hzA` using `Subring.subset_closure (s := {z | ∃ (b : K → ℕ) (f g : MRing ι O), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧ z = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P f) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P …`.

Establish `hm : (⟨_, hzA⟩ : homLocRing P W) ∈ 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))`. Rewrite using `[hcomap]`. Conclude with `fun hu => (hAunit b w _ hw hg hi hzA).1 hu hwW`. Establish `hzB : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u) (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk (blowUpOf P u) (liftForm w)) / algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u) (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk ( …`. Unfold `homLocRing`.

Conclude with `Subring.subset_closure ⟨liftMDeg b, liftForm w, liftForm (powMonomial b i), isMultiHomog_liftForm hw, isMultiHomog_liftForm hg, hgW', rfl⟩`. Establish `hU` using `((hBunit (liftMDeg b) (liftForm w) (liftForm (powMonomial b i)) (isMultiHomog_liftForm hw) (isMultiHomog_liftForm hg) hgW' hzB).2 hwW').map φ`. Establish `hval : φ ⟨_, hzB⟩ = algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hzA⟩)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hφ (liftMDeg b) _ _ (isMultiHomog_liftForm hw) (isMultiHomog_liftForm hg) hgW', blowUpEval_liftForm, blowUpEval_liftForm]`.

Both sides reduce to the same expression. Rewrite `hU` using `[hval, IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔫]`. Conclude with `hU hm`. Introduce `w hwW`. Rewrite using `[Ideal.mem_comap, ← sum_weightedHomogeneousComponent (w := blockWeight ι) w, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp _), map_sum]`.

Conclude with `Ideal.sum_mem _ fun b _ => key b _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hWmh w hwW b)`.
-/
theorem BlowUpOverLocMaxCentre.proof (h₁ : BlowUpOverLocCentreDom.Statement.{u})
    (h₂ : BlowUpOverLocLocalization.Statement.{u}) (h₃ : BlowUpOverLocFinite.Statement.{u})
    (h₄ : BlowUpLocRingIso.Statement.{u}) :
    BlowUpOverLocMaxCentre.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  obtain ⟨W', hW'p, hW'h, hW'r, hW'le, hW'c, h, hdom⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  obtain ⟨h', 𝔭, h𝔭, hl⟩ :=
    h₂ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  let _ := (Subring.inclusion h).toAlgebra
  have hl' : IsLocalization.AtPrime (blowUpLocRing P u W') 𝔭 := hl
  have hn𝔭 : 𝔫 ≤ 𝔭 := fun b hb => by
    by_contra hb𝔭
    exact hdom b hb ((IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔭 b).2 hb𝔭)
  obtain rfl : 𝔫 = 𝔭 := h𝔫.eq_of_le h𝔭.ne_top hn𝔭
  refine ⟨W', hW'p, hW'h, hW'r, hW'le, le_antisymm hW'c ?_, h, hl'⟩
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_trans le_sup_left hWmin.1.2
  have hWmh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.full O K ι _ W
      (SupSpanMultiHomog.full O K ι P x c hP.multiProj.multiHomog hx) hWmin
  obtain ⟨hAloc, hAunit⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  obtain ⟨hfin, -⟩ := h₃ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have : Algebra.IsIntegral (homLocRing P W) (blowUpOverLoc P W u) := Algebra.IsIntegral.of_finite _ _
  have hmax : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
  have hcomap : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) =
      IsLocalRing.maximalIdeal (homLocRing P W) := IsLocalRing.eq_maximalIdeal hmax
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := h₄ O K ι J P u W' hW'le
  obtain ⟨-, hBunit⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J)
    (blowUpOf P u) W' hW'p hW'le
  have key : ∀ (b : K → ℕ) (w : MRing ι O), IsMultiHomog w b → w ∈ W →
      liftForm (J := J) w ∈ W' := by
    intro b w hw hwW
    by_contra hwW'
    obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hWrel b
    have hg := isMultiHomog_powMonomial (R := O) b i
    have hgW' : liftForm (J := J) (powMonomial b i) ∉ W' := fun hg' => hi (hW'c hg')
    have hzA := Subring.subset_closure (s := {z | ∃ (b : K → ℕ) (f g : MRing ι O), IsMultiHomog f b ∧
      IsMultiHomog g b ∧ g ∉ W ∧
      z = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P f) /
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g)})
      ⟨b, w, powMonomial b i, hw, hg, hi, rfl⟩
    have hm : (⟨_, hzA⟩ : homLocRing P W) ∈
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rw [hcomap]
      exact fun hu => (hAunit b w _ hw hg hi hzA).1 hu hwW
    have hzB : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
          (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
          (Ideal.Quotient.mk (blowUpOf P u) (liftForm w)) /
        algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
          (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
          (Ideal.Quotient.mk (blowUpOf P u) (liftForm (powMonomial b i))) ∈
        homLocRing (blowUpOf P u) W' := by
      unfold homLocRing
      exact Subring.subset_closure ⟨liftMDeg b, liftForm w, liftForm (powMonomial b i),
        isMultiHomog_liftForm hw, isMultiHomog_liftForm hg, hgW', rfl⟩
    have hU := ((hBunit (liftMDeg b) (liftForm w) (liftForm (powMonomial b i))
      (isMultiHomog_liftForm hw) (isMultiHomog_liftForm hg) hgW' hzB).2 hwW').map φ
    have hval : φ ⟨_, hzB⟩ =
        algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W')
          (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hzA⟩) := by
      apply Subtype.ext
      rw [hφ (liftMDeg b) _ _ (isMultiHomog_liftForm hw) (isMultiHomog_liftForm hg) hgW',
        blowUpEval_liftForm, blowUpEval_liftForm]
      rfl
    rw [hval, IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔫] at hU
    exact hU hm
  intro w hwW
  rw [Ideal.mem_comap, ← sum_weightedHomogeneousComponent (w := blockWeight ι) w,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp _), map_sum]
  exact Ideal.sum_mem _ fun b _ =>
    key b _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hWmh w hwW b)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
