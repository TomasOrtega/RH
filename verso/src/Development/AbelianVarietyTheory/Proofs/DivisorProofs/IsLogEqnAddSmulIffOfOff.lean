import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem isLogEqn_add_smul_iff_of_off {p : X ⟶ Sp k} {n : ℕ} {Γ B : X → ℚ} (c : ℚ) {x : X}
    (hB : Off B x) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ) :
    IsLogEqn p (Γ + c • B) η x m g ↔ IsLogEqn p Γ η x m g := by
  refine forall_congr' fun z => forall_congr' fun hz => ?_
  have : (Γ + c • B) z = Γ z := by simp [hB z hz]
  rw [this]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem off_add_smul (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ)
    (n : ℕ) (Γ B : X → ℚ) (c : ℚ) (x : X) (hB : Off B x) :
    (KltAt p n (Γ + c • B) x ↔ KltAt p n Γ x) ∧ (LcAt p n (Γ + c • B) x ↔ LcAt p n Γ x) ∧
      (IsNkltCentre p n (Γ + c • B) x ↔ IsNkltCentre p n Γ x) ∧ ∀ z, z ⤳ x → Off B z := by
  have e := isLogEqn_add_smul_iff_of_off (p := p) (n := n) (Γ := Γ) c hB
  refine ⟨?_, ?_, ?_, fun z hz w hw => hB w (hw.trans hz)⟩
  · unfold KltAt
    simp only [e]
  · unfold LcAt
    simp only [e]
  · unfold IsNkltCentre
    simp only [e]

end GlobalTheory.PairStep

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
example : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ B : X → ℚ) (c : ℚ) (x : X), Off B x → (KltAt p n (Γ + c • B) x ↔ KltAt p n Γ x) ∧ (LcAt p n (Γ + c • B) x ↔ LcAt p n Γ x) ∧ (IsNkltCentre p n (Γ + c • B) x ↔ IsNkltCentre p n Γ x) ∧ ∀ z, z ⤳ x → Off B z :=
  fun X _ _ p n Γ B c x hB => GlobalTheory.PairStep.off_add_smul X p n Γ B c x hB
