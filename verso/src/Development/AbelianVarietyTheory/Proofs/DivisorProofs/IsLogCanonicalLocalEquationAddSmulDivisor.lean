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
Break down `Int.eq_nat_or_neg r with ⟨s, rfl | rfl⟩` into its components or cases. Rewrite using `[zpow_natCast, E.ord_pow]`. Rewrite using `[zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem divOver_ord_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (f : X.functionFieldˣ) (r : ℤ) : E.ord (f ^ r) = r * E.ord f := by
  rcases Int.eq_nat_or_neg r with ⟨s, rfl | rfl⟩
  · rw [zpow_natCast, E.ord_pow]
  · rw [zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]
    ring

/- English proof (translation)
Introduce `X _ _ p n Γ D η x m m' g f c hm hm' hg hD`. Establish `hb : 0 < c.den` using `c.den_pos`. Establish `hc : c * (c.den : ℚ) = c.num` using `Rat.mul_den_eq_num c`. Establish `h₁ : (m : ℚ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `h₂ : (m' : ℚ) ≠ 0` using `by exact_mod_cast hm'.ne'`.

Establish `h₃ : (c.den : ℚ) ≠ 0` using `by exact_mod_cast hb.ne'`. Use `⟨m * m' * c.den, g ^ (m' * c.den) * f ^ (c.num * m), Nat.mul_pos (Nat.mul_pos hm hm') hb, fun z hz E hE => ?_, fun E => ?_⟩` and prove the remaining obligations. Establish `e₁` using `hg z hz E hE`. Establish `e₂` using `hD z hz E hE`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[E.ord_mul, E.ord_pow, divOver_ord_zpow, e₂]`. Use `push_cast`. Rewrite using `[← e₁]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(E.ord f : ℚ) * hc`.

Simplify using `only [discrep]`. Rewrite using `[E.ord_mul, E.ord_pow, divOver_ord_zpow]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `((m : ℚ) * (E.ord f : ℚ)) * hc`.
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
