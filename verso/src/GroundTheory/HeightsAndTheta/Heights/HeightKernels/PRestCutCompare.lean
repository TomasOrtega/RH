import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Unfold `RestTerms.flagIntegral`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_sub, coeff_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RestCutCompare.flagIntegral_sub_C_mul (f N : ℕ) (P Q : RestTerms.RootRing f N) (b : ℚ) :
    RestTerms.flagIntegral f N (P - C b * Q) =
      RestTerms.flagIntegral f N P - b * RestTerms.flagIntegral f N Q := by
  unfold RestTerms.flagIntegral
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_sub, coeff_C_mul]
  ring

/- English proof (translation)
Introduce `f j k N e I hI hs H hH`. Establish `hN : N = j + k`. Use `Fintype.card_congr e` as an intermediate fact. Simplify using `using this`. Establish `hD : flagDim f j k = RestTerms.topDegree f N`.

Substitute `hN` using the available equality. Both sides reduce to the same expression. Rewrite `hH` using `[hD]`. Take `⟨b, hb⟩` from `h₁ f N H hH`. Express the relevant statement in the definitionally equal form `H - C b * restStair f N ∈ restPsumIdeal f N at hb`.

Establish `hAh : (H - C b * restStair f N).IsHomogeneous (flagDim f j k)`. Rewrite using `[hD]`. Conclude with `hH.sub ((h₂ f N).C_mul b)`. Establish `hflag : RestTerms.flagIntegral f N H = b * RestTerms.flagIntegral f N (restStair f N)`. Establish `h` using `h₃ f N _ hb`.

Rewrite `h` using `[RestCutCompare.flagIntegral_sub_C_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC : restTransport f j k N e (C b) = C (b : ℝ)`. Simplify using `[restTransport, restRename]`. Establish `hIH : I (restTransport f j k N e H) = (b : ℝ) * I (restTransport f j k N e (restStair f N))`.

Establish `h` using `h₄ f j k N e I hI _ hb hAh`. Rewrite `h` using `[map_sub, map_mul, hC, C_mul', map_sub, map_smul, smul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs' : (RestTerms.flagIntegral f N (restStair f N) : ℝ) ≠ 0` using `by exact_mod_cast hs`. Unfold `restCompareConst`.

Rewrite using `[hIH, hflag]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem RestCutCompare.proof (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestCutStairHom.Statement) (h₃ : RestCutFlagKillsIdeal.Statement)
    (h₄ : RestCutIKillsIdeal.Statement) : RestCutCompare.Statement := by
  intro f j k N e I hI hs H hH
  have hN : N = j + k := by
    have := Fintype.card_congr e
    simpa using this
  have hD : flagDim f j k = RestTerms.topDegree f N := by
    subst hN
    rfl
  rw [hD] at hH
  obtain ⟨b, hb⟩ := h₁ f N H hH
  change H - C b * restStair f N ∈ restPsumIdeal f N at hb
  have hAh : (H - C b * restStair f N).IsHomogeneous (flagDim f j k) := by
    rw [hD]
    exact hH.sub ((h₂ f N).C_mul b)
  have hflag : RestTerms.flagIntegral f N H = b * RestTerms.flagIntegral f N (restStair f N) := by
    have h := h₃ f N _ hb
    rw [RestCutCompare.flagIntegral_sub_C_mul] at h
    linarith
  have hC : restTransport f j k N e (C b) = C (b : ℝ) := by
    simp [restTransport, restRename]
  have hIH : I (restTransport f j k N e H) =
      (b : ℝ) * I (restTransport f j k N e (restStair f N)) := by
    have h := h₄ f j k N e I hI _ hb hAh
    rw [map_sub, map_mul, hC, C_mul', map_sub, map_smul, smul_eq_mul] at h
    linarith
  have hs' : (RestTerms.flagIntegral f N (restStair f N) : ℝ) ≠ 0 := by exact_mod_cast hs
  unfold restCompareConst
  rw [hIH, hflag]
  push_cast
  field_simp

end GroundTheory.Heights₂.Heights
