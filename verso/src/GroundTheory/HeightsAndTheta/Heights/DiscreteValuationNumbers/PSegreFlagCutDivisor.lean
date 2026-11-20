import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutSpecialize
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtOfSaturated
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

open FlagBundleSectionDivProof GenericProjClosureDivisor in

/- English proof (translation)
Establish `hModel : SegreFlagClosureModel.Statement` using `SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)`. Establish `hSat : MultAtOfSaturated.Statement.{0}` using `MultAtOfSaturated.proof`. Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht k hk cs ch s h hs hh hdeg hsP hhP hval W hW`. Establish `hPp : (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))).IsPrime` using `RingHom.ker_isPrime _`. Establish `hQp : (pointIdeal O (flagClosurePt y w e φ φ' t k)).IsPrime` using `RingHom.ker_isPrime _`.

Take `⟨hPQ, hspec⟩` from `hSpec O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk`. Establish `hτ : flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ ≠ 0`. Introduce `h0`. Conclude with `hsP (mem_of_homog hs (by rw [hval, h0, zero_mul]))`. Distinguish the cases in `hWc : W.IsPrime ∧ IsRelevant W ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W`.

Take `⟨hWp, hWrel, hPW⟩` from `hWc`. Take `⟨cl, cm, l, μ, u, hl, hμ, hdl, hμW, huW, hlv, hl0, hsat⟩` from `hChart O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk W hWp hWrel hPW hW`. Establish `hμP : μ ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))` using `fun h' => hμW (hPW h')`. Establish `hlP : l ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))`. Introduce `h'`.

Establish `h0` using `aeval_eq_zero_of_mem h'`. Rewrite `h0` using `[hlv]`. Conclude with `hμP (mem_of_homog hμ ((mul_eq_zero.mp h0).resolve_left hτ))`. Establish `huW' : ∀ n : ℕ, u ^ n ∉ W` using `fun n h' => huW (hWp.mem_of_pow_mem n h')`. Establish `hdeg' : cs + cm = cl + ch`.

Use function extensionality and compare the values at `o`. Establish `h1` using `congrFun hdeg o`. Establish `h2` using `congrFun hdl o`. Simplify using `only [Pi.add_apply] at h1 h2 ⊢`. Use linear arithmetic over natural numbers and integers.

Establish `hdiff : s * μ - l * h ∈ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))`. Establish `h2` using `hl.mul hh`. Rewrite `h2` using `[← hdeg']`. Use `mem_of_homog (b := cs + cm) ((mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hs.mul hμ)) ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))) ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_mul, hval, hlv]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ratDiv_eq_of_sub_mem hsP hhP hlP hμP hdiff]`. Unfold `ratDiv`. Rewrite using `[divCycle_eq_zero_of_not_mem hμW, sub_zero]`. Establish `hlQ : 0 < k → l ∈ pointIdeal O (flagClosurePt y w e φ φ' t k)` using `fun _ => mem_of_homog hl (hspec l μ hlv)`.

Use `split_ifs with hc`. Take `⟨hkpos, rfl⟩` from `hc`. Take `⟨hmin, hmult⟩` from `hSat O (Option (Option K)) (bundleIdx (bundleIdx ι M) M') _ _ (sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr (hlQ hkpos))) (fun q hq => by`. Take `⟨n, hn⟩` from `hsat hkpos q hq`. Conclude with `⟨_, huW' n, hn⟩)`.

Unfold `divCycle`. Rewrite using `[dif_pos ⟨hmin, hWrel⟩, hmult]`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`. Establish `hmin : W ∈ (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l}).minimalPrimes`.

Unfold `divCycle at hne`. Use `split_ifs at hne with h'`. Conclude with `h'.1`. Conclude with `absurd rfl hne`. Establish `hlW : l ∈ W` using `hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self l))`.

Break down `Nat.eq_zero_or_pos k with hk0 | hkpos` into its components or cases. Conclude with `hl0 hk0 hlW`. Establish `hQW : pointIdeal O (flagClosurePt y w e φ φ' t k) ≤ W` using `fun q hq => by`. Take `⟨n, hn⟩` from `hsat hkpos q hq`. Conclude with `(hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (huW' n)`.

Establish `hPQ' : pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) < pointIdeal O (flagClosurePt y w e φ φ' t k)` using `lt_of_le_of_ne hPQ (fun h' => hlP (by rw [h']; exact hlQ hkpos))`. Conclude with `hc ⟨hkpos, (eq_of_lt_of_le_of_mem_minimalPrimes hmin hPQ' hQW).symm⟩`. Establish `h0 : ∀ z, divCycle (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) z W = 0` using `fun z => by`. Unfold `divCycle`. Rewrite using `[dif_neg]`.

Introduce and unpack `⟨h', hr⟩`. Conclude with `hWc ⟨h'.1.1, hr, le_sup_left.trans h'.1.2⟩`. Establish `hWQ : ¬ (0 < k ∧ W = pointIdeal O (flagClosurePt y w e φ φ' t k))`. Introduce and unpack `⟨hkpos, rfl⟩`. Conclude with `hWc ⟨hQp, (hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hkpos hk.le).1.multiProj.relevant, hPQ⟩`.

Rewrite using `[if_neg hWQ]`. Simplify using `[ratDiv, h0]`.
-/
theorem SegreFlagCutDivisor.proof (hSpec : SegreFlagCutSpecialize.Statement)
    (hChart : SegreFlagCutChart.Statement) : SegreFlagCutDivisor.Statement := by
  have hModel : SegreFlagClosureModel.Statement :=
    SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)
  have hSat : MultAtOfSaturated.Statement.{0} := MultAtOfSaturated.proof
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk cs ch s h hs hh hdeg hsP hhP hval W hW
  classical
  have hPp : (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))).IsPrime := RingHom.ker_isPrime _
  have hQp : (pointIdeal O (flagClosurePt y w e φ φ' t k)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨hPQ, hspec⟩ := hSpec O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  have hτ : flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ ≠ 0 := by
    intro h0
    exact hsP (mem_of_homog hs (by rw [hval, h0, zero_mul]))
  by_cases hWc : W.IsPrime ∧ IsRelevant W ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W
  · obtain ⟨hWp, hWrel, hPW⟩ := hWc
    obtain ⟨cl, cm, l, μ, u, hl, hμ, hdl, hμW, huW, hlv, hl0, hsat⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk W
        hWp hWrel hPW hW
    have hμP : μ ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := fun h' => hμW (hPW h')
    have hlP : l ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := by
      intro h'
      have h0 := aeval_eq_zero_of_mem h'
      rw [hlv] at h0
      exact hμP (mem_of_homog hμ ((mul_eq_zero.mp h0).resolve_left hτ))
    have huW' : ∀ n : ℕ, u ^ n ∉ W := fun n h' => huW (hWp.mem_of_pow_mem n h')
    have hdeg' : cs + cm = cl + ch := by
      funext o
      have h1 := congrFun hdeg o
      have h2 := congrFun hdl o
      simp only [Pi.add_apply] at h1 h2 ⊢
      omega
    have hdiff : s * μ - l * h ∈ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := by
      have h2 := hl.mul hh
      rw [← hdeg'] at h2
      refine mem_of_homog (b := cs + cm) ((mem_weightedHomogeneousSubmodule _ _ _ _).mp
        (Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hs.mul hμ))
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))) ?_
      rw [map_sub, map_mul, map_mul, hval, hlv]
      ring
    rw [ratDiv_eq_of_sub_mem hsP hhP hlP hμP hdiff]
    unfold ratDiv
    rw [divCycle_eq_zero_of_not_mem hμW, sub_zero]
    have hlQ : 0 < k → l ∈ pointIdeal O (flagClosurePt y w e φ φ' t k) := fun _ =>
      mem_of_homog hl (hspec l μ hlv)
    split_ifs with hc
    · obtain ⟨hkpos, rfl⟩ := hc
      obtain ⟨hmin, hmult⟩ := hSat O (Option (Option K)) (bundleIdx (bundleIdx ι M) M') _ _
        (sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr (hlQ hkpos)))
        (fun q hq => by
          obtain ⟨n, hn⟩ := hsat hkpos q hq
          exact ⟨_, huW' n, hn⟩)
      unfold divCycle
      rw [dif_pos ⟨hmin, hWrel⟩, hmult]
      rfl
    · by_contra hne
      have hmin : W ∈ (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l}).minimalPrimes := by
        unfold divCycle at hne
        split_ifs at hne with h'
        · exact h'.1
        · exact absurd rfl hne
      have hlW : l ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self l))
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exact hl0 hk0 hlW
      · have hQW : pointIdeal O (flagClosurePt y w e φ φ' t k) ≤ W := fun q hq => by
          obtain ⟨n, hn⟩ := hsat hkpos q hq
          exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (huW' n)
        have hPQ' : pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) <
            pointIdeal O (flagClosurePt y w e φ φ' t k) :=
          lt_of_le_of_ne hPQ (fun h' => hlP (by rw [h']; exact hlQ hkpos))
        exact hc ⟨hkpos, (eq_of_lt_of_le_of_mem_minimalPrimes hmin hPQ' hQW).symm⟩
  · have h0 : ∀ z, divCycle (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) z W = 0 := fun z => by
      unfold divCycle
      rw [dif_neg]
      rintro ⟨h', hr⟩
      exact hWc ⟨h'.1.1, hr, le_sup_left.trans h'.1.2⟩
    have hWQ : ¬ (0 < k ∧ W = pointIdeal O (flagClosurePt y w e φ φ' t k)) := by
      rintro ⟨hkpos, rfl⟩
      exact hWc ⟨hQp, (hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
        Φ e t ht k hkpos hk.le).1.multiProj.relevant, hPQ⟩
    rw [if_neg hWQ]
    simp [ratDiv, h0]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
