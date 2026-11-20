import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneUnitHilbertNinetyStatement

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨-, hcc, hv, hns, -⟩` from `GlobalTheory.T.placeConjugation_properties_cmField E hU w`. Take `⟨-, ⟨ϖ, q, hUI, -⟩, -⟩` from `hns hw`. Take `⟨-, -, hϖc, hϖv, ⟨x, -, hx⟩, -⟩` from `hUI`. Establish `key : ∀ y, u * cj w (y + u * cj w y) = y + u * cj w y`. Introduce `y`.

Rewrite using `[map_add, map_mul, hcc, mul_add, ← mul_assoc, hu, one_mul, add_comm]`. Choose the witnesses or unpack the hypotheses as in `⟨v0, hv0, hkey⟩ : ∃ v0, v0 ≠ 0 ∧ u * cj w v0 = v0 := by`. Distinguish the cases in `h1 : (1 : w.adicCompletion E) + u * cj w 1 = 0`. Use `⟨x + u * cj w x, ?_, key x⟩` and prove the remaining obligations. Establish `hu1 : u = -1`.

Rewrite `h1` using `[map_one, mul_one]`. Take the linear combination `h1`. Introduce `h`. Establish `h2 : cj w x - x = 0` using `by rw [hu1] at h; linear_combination -h`. Rewrite `hx` using `[h2, map_zero]`.

Conclude with `zero_ne_one hx`. Conclude with `⟨_, h1, key 1⟩`. Establish `h0 : Valued.v v0 ≠ 0` using `(Valuation.ne_zero_iff _).2 hv0`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h`.

Rewrite `hϖv` using `[h, map_zero]`. Conclude with `WithZero.zero_ne_coe hϖv`. Use `⟨v0 * ϖ ^ WithZero.log (Valued.v v0), ?_, ?_⟩` and prove the remaining obligations. Establish `h2 : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hϖv`. Rewrite using `[map_mul, map_zpow₀, h2, ← WithZero.exp_zsmul, ← WithZero.exp_log h0, ← WithZero.exp_add]`.

Simplify using the standard rewrite rules. Rewrite using `[map_mul, map_zpow₀, hϖc, ← mul_assoc, hkey]`.
-/
theorem norm_one_eq_unit_div_conj (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (u : w.adicCompletion E) (hu : u * cj w u = 1) :
    ∃ z, Valued.v z = 1 ∧ u * cj w z = z := by
  obtain ⟨-, hcc, hv, hns, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, -⟩, -⟩ := hns hw
  obtain ⟨-, -, hϖc, hϖv, ⟨x, -, hx⟩, -⟩ := hUI
  have key : ∀ y, u * cj w (y + u * cj w y) = y + u * cj w y := by
    intro y
    rw [map_add, map_mul, hcc, mul_add, ← mul_assoc, hu, one_mul, add_comm]
  obtain ⟨v0, hv0, hkey⟩ : ∃ v0, v0 ≠ 0 ∧ u * cj w v0 = v0 := by
    by_cases h1 : (1 : w.adicCompletion E) + u * cj w 1 = 0
    · refine ⟨x + u * cj w x, ?_, key x⟩
      have hu1 : u = -1 := by
        rw [map_one, mul_one] at h1
        linear_combination h1
      intro h
      have h2 : cj w x - x = 0 := by rw [hu1] at h; linear_combination -h
      rw [h2, map_zero] at hx
      exact zero_ne_one hx
    · exact ⟨_, h1, key 1⟩
  have h0 : Valued.v v0 ≠ 0 := (Valuation.ne_zero_iff _).2 hv0
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  refine ⟨v0 * ϖ ^ WithZero.log (Valued.v v0), ?_, ?_⟩
  · have h2 : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖv
    rw [map_mul, map_zpow₀, h2, ← WithZero.exp_zsmul, ← WithZero.exp_log h0, ← WithZero.exp_add]
    simp
  · rw [map_mul, map_zpow₀, hϖc, ← mul_assoc, hkey]

/- English proof (translation)
Use `⟨fun u hu hcu => ?_, norm_one_eq_unit_div_conj hU w hw⟩` and prove the remaining obligations. Take `⟨s, hs, hs'⟩` from `GlobalTheory.T.norm_one_unit_hilbert_ninety E hU w hw u hcu hu`. Conclude with `⟨s, hs, by rw [mul_comm]; exact hs'⟩`.
-/
theorem hilbert90_norm_one_units_of_unr_of_not_split (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) :
    (∀ u : w.adicCompletion E, Valued.v u = 1 → cj w u = u → ∃ z, Valued.v z = 1 ∧ z * cj w z = u) ∧
    (∀ u : w.adicCompletion E, u * cj w u = 1 → ∃ z, Valued.v z = 1 ∧ u * cj w z = z) := by
  refine ⟨fun u hu hcu => ?_, norm_one_eq_unit_div_conj hU w hw⟩
  obtain ⟨s, hs, hs'⟩ := GlobalTheory.T.norm_one_unit_hilbert_ninety E hU w hw u hcu hu
  exact ⟨s, hs, by rw [mul_comm]; exact hs'⟩

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
