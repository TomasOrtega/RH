import Formalism.LocalToGlobal.GlobalTheory.GL6.PowSmulLatticeLeWeightLatticeTop
import Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfHeckeRamified
import Formalism.LocalToGlobal.GlobalTheory.GL6.SlopeFormulaOfCharacterFinite

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

section Parts

variable (D : D7) (u : D.what₂.Word)

def BranchLatticeLengths : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    (0 ≤ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift →
      ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
          ((D.duS u : ℚ) * (wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) / (D.R.k : ℚ))) ∧
    (0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ)))

def SeenPlaceLatticeLengthFormula : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ))

end Parts

variable {D : D7} {u : D.what₂.Word}

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem second_branch_incl_length_of_second (Tt : Formalism.L2.Forms.FormsTied D u) (hL : SeenPlaceLatticeLengthFormula D u) : SecondBranchInclusionLength D u :=
  fun w hw hs v hb => ⟨(weight_lattice_inclusions D u Tt w hw hs v).2 hb, hL w hw hs v hb⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem lattice_length_of_formulas (Tt : Formalism.L2.Forms.FormsTied D u) (h4 : HeckeIntegralLevelZero D u) (h9 : HeckeRamifiedLevelZero D u) (hL : BranchLatticeLengths D u) :
    LatticeInclusionLength D u := by
  intro w hw hs v
  have hR : Rat0 D u := rational_level_zero_of_integral w hw hs h4
  obtain ⟨hUB, hDS⟩ := h4 w hw hs v
  have ram := h9 v
  obtain ⟨hI1, hI2⟩ := weight_lattice_inclusions D u Tt w hw hs v
  obtain ⟨hL1, hL2⟩ := hL w hw hs v
  exact ⟨fun hd => ⟨hI1 hd, hL1 hd, LemmaC_one hR w hw v (hI1 hd) hUB hDS ram⟩,
    fun hb => ⟨hI2 hb, hL2 hb, LemmaC_two hR w hw v _ hb (hI2 hb) hUB hDS ram⟩⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem second_branch_incl_length_of_lengths (Tt : Formalism.L2.Forms.FormsTied D u) (hL : BranchLatticeLengths D u) : SecondBranchInclusionLength D u := second_branch_incl_length_of_second Tt fun w hw hs v hb => (hL w hw hs v).2 hb

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ramified_lattice_family_of_clauses
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → admS D u →
      HeckeIntegralLevelZero D u ∧ HeckeRamifiedLevelZero D u ∧ BranchLatticeLengths D u) : RamifiedLatticeFamily :=
  ramified_lattice_of_length fun D u hF hS hA => by
    obtain ⟨h4, h9, hL⟩ := h D u hF hS hA
    obtain ⟨Tf, -⟩ := hF
    exact lattice_length_of_formulas Tf h4 h9 hL

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem congruence_no_kernel_of_lengths
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → admS D u →
      HeckeIntegralLevelZero D u ∧ HeckeRamifiedLevelZero D u ∧ BranchLatticeLengths D u) : CongruenceLatticeLengthBoundFamily := by
  refine congruence_no_kernel_family_minimal fun D u hF hS hA => ?_
  obtain ⟨h4, h9, hL⟩ := h D u hF hS hA
  obtain ⟨T, _⟩ := hF
  exact ⟨h4, h9, second_branch_incl_length_of_lengths T hL⟩

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
