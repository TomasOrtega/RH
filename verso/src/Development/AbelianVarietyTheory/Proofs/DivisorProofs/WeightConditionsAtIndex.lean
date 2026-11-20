import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.HodgeGapBounds

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}

/- English proof (translation)
Use linear arithmetic over natural numbers and integers.
-/
theorem bar_lt (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem one_le_gap_uMinus (P : WtPar Dw) (τ : Psi H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q)
    (hs : StrictAnti (P.u₁ τ)) : 1 ≤ gap (P.uMinus τ) (Dw.p - 1) := by
  have hk := bar_lt hp hq
  have h1 := P.gap_u₁ τ hk
  have hT : 0 < P.T₁ := by unfold WtPar.T₁; positivity
  have hg : 1 ≤ gap (P.u₁ τ) (Dw.p - 1) := by
    rw [gap, dif_pos hk]
    have := hs (show (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p - 1 + 1, hk⟩ from by
      rw [Fin.mk_lt_mk]; omega)
    omega
  rw [h1, Int.le_ediv_iff_mul_le hT, one_mul] at hg
  have hkap : gap (FlagTan.kap Dw τ) (Dw.p - 1) = 2 * ((Dw.p : ℤ) + Dw.q) - 2 := by
    simp only [gap, dif_pos hk, FlagTan.kap, Fin.val_mk]
    have := Nat.cast_sub (R := ℤ) hp
    split_ifs <;> push_cast at * <;> omega
  have hsub : gap ((P.uMinus - FlagTan.kap Dw) τ) (Dw.p - 1) =
      gap (P.uMinus τ) (Dw.p - 1) - gap (FlagTan.kap Dw τ) (Dw.p - 1) := by
    simp only [gap, dif_pos hk, Pi.sub_apply]; ring
  have hT1 : 1 ≤ P.T₁ := hT
  omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem laOf_add_smul (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (c0 s : ℤ) :
    laOf Dw a n + s • hodgeWt Dw =
      uMinus Dw a n kc c0 + (s + c0) • hodgeWt Dw + FlatLine.parWt Dw (anchor Dw a n kc) := by
  rw [← uWt_add_anchor Dw a n kc]
  simp only [uMinus, add_smul]
  abel

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem gap_add_smul_hodge (v : AllWt.Weight Dw) (x : ℤ) (w : Psi H → ℤ) (τ : Psi H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) :
    gap ((v + x • hodgeWt Dw + FlatLine.parWt Dw w) τ) (Dw.p - 1) = gap (v τ) (Dw.p - 1) + x := by
  have hk := bar_lt hp hq
  simp only [gap, dif_pos hk, Pi.add_apply, Pi.smul_apply, hodgeWt, CompHt.barWt, FlatLine.parWt, Fin.val_mk, smul_eq_mul]
  split_ifs <;> first | omega | ring

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem antitone_add_par (v : AllWt.Weight Dw) (w : Psi H → ℤ) (τ : Psi H) (h : Antitone (v τ)) :
    Antitone ((v + FlatLine.parWt Dw w) τ) :=
  fun _ _ hab => add_le_add (h hab) le_rfl

end Weights

end GlobalTheory.CovTop.HodgeGapBounds

namespace GlobalTheory.CovTop.HodgeGapBounds

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Supply the required witnesses or components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem evidence : Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → LawsJ p.T ∧ 1 ≤ (dat p i).p ∧
    1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ Even (p.κ i).n ∧
    (∀ τ, Antitone (uM p i τ)) ∧ (∀ τ, 1 ≤ gap (uM p i τ) ((dat p i).p - 1)) ∧
    ∀ s : ℤ, (s = -(cZero (Fm.D x ι) ((i : ℕ) + 1)) ∨ s = 0 ∨ s = cZero (Fm.D x ι) ((i : ℕ) + 1)) →
      (∀ τ, Antitone ((laOf (dat p i) (wtA (p.κ i)) (p.κ i).n + s • hodgeWt (dat p i)) τ)) ∧
      ∀ τ, 1 ≤ gap ((laOf (dat p i) (wtA (p.κ i)) (p.κ i).n + s • hodgeWt (dat p i)) τ) ((dat p i).p - 1) := by
  have hA := GlobalTheory.T.weight_parameter_strict_antitone GlobalTheory.T.size_bound_statement
  have hB := GlobalTheory.CovTop.WtShape.wtN
  unfold WtN at hB
  unfold Lifts at hA hB ⊢
  refine (hA.and hB).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩ := h
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi => ?_⟩
  have a := h1 x hx ((le_max_left _ _).trans hle) ι p hp i hi
  have b := h2 x hx ((le_max_right _ _).trans hle) ι p hp i
  obtain ⟨hp1, hq1, hdeg, -, hSA, -, hanti⟩ := a
  have hc0 : 0 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := Int.natCast_nonneg _
  have hgap : ∀ τ, 1 ≤ gap (uM p i τ) ((dat p i).p - 1) := fun τ =>
    one_le_gap_uMinus _ τ hp1 hq1 (hSA τ).1
  have hant0 : ∀ τ, Antitone (uM p i τ) := fun τ => by simpa using (hanti 0 (by norm_num) τ).1
  refine ⟨p.fw.laws, hp1, hq1, hdeg, ⟨by omega, i.2⟩, b.dom.2, hant0, hgap, fun s hs => ?_⟩
  obtain ⟨t, ht3, hts⟩ : ∃ t : ℕ, t ≤ 3 ∧ s + cZero (Fm.D x ι) ((i : ℕ) + 1) = (t : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1) := by
    rcases hs with hs | hs | hs
    · exact ⟨0, by norm_num, by rw [hs]; ring⟩
    · exact ⟨1, by norm_num, by rw [hs]; ring⟩
    · exact ⟨2, by norm_num, by rw [hs]; ring⟩
  rw [laOf_add_smul (kc := (Fm.D x ι).R.k - 1) (c0 := cZero (Fm.D x ι) ((i : ℕ) + 1))]
  refine ⟨fun τ => antitone_add_par _ _ τ ?_, fun τ => ?_⟩
  · rw [hts]; exact (hanti t ht3 τ).1
  · rw [gap_add_smul_hodge _ _ _ τ hp1 hq1]
    have := hgap τ
    have h2 : 0 ≤ s + cZero (Fm.D x ι) ((i : ℕ) + 1) := by rw [hts]; positivity
    exact le_add_of_le_of_nonneg this h2

end GlobalTheory.CovTop.HodgeGapBounds
