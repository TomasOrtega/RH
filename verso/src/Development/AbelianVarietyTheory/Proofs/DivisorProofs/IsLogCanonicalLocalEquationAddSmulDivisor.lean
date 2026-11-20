import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem divOver_ord_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (f : X.functionFieldˣ) (r : ℤ) : E.ord (f ^ r) = r * E.ord f := by
  rcases Int.eq_nat_or_neg r with ⟨s, rfl | rfl⟩
  · rw [zpow_natCast, E.ord_pow]
  · rw [zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem isLogEqn_add_smul : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ D : X → ℚ) (η : RatForms p n) (x : X) (m m' : ℕ) (g f : X.functionFieldˣ) (c : ℚ), 0 < m → 0 < m' → IsLogEqn p Γ η x m g → (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m') → ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + c • D) η x m'' g'' ∧ ∀ E : DivOver p, discrep E η m'' g'' = discrep E η m g - c * ((E.ord f : ℚ) / m') := by
  intro X _ _ p n Γ D η x m m' g f c hm hm' hg hD
  have hb : 0 < c.den := c.den_pos
  have hc : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
  have h₁ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h₂ : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have h₃ : (c.den : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  refine ⟨m * m' * c.den, g ^ (m' * c.den) * f ^ (c.num * m), Nat.mul_pos (Nat.mul_pos hm hm') hb,
    fun z hz E hE => ?_, fun E => ?_⟩
  · have e₁ := hg z hz E hE
    have e₂ := hD z hz E hE
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [E.ord_mul, E.ord_pow, divOver_ord_zpow, e₂]
    push_cast
    rw [← e₁]
    field_simp
    linear_combination (E.ord f : ℚ) * hc
  · simp only [discrep]
    rw [E.ord_mul, E.ord_pow, divOver_ord_zpow]
    push_cast
    field_simp
    linear_combination ((m : ℚ) * (E.ord f : ℚ)) * hc

end GlobalTheory.PairStep
