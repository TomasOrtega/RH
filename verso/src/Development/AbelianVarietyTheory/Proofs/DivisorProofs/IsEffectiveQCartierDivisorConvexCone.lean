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
namespace GlobalTheory.QCartCone

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem mult_zero' (z : X) : (0 : CartierDiv X).mult z = 0 := by
  have := CartierDiv.mult_add (0 : CartierDiv X) 0 z
  rw [add_zero] at this
  omega

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mult_nsmul' (D : CartierDiv X) (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero']; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem eff_nsmul' {D : CartierDiv X} (h : D.Eff) (n : ℕ) : (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isQCart_cone : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (D B : X → ℚ) (c : ℚ),
    IsQCart D → IsQCart B → 0 ≤ c → IsQCart (D + B) ∧ IsQCart (c • D) ∧ IsQCart (0 : X → ℚ) := by
  intro X _ _ D B c hD hB hc
  obtain ⟨m, D₀, hm, hD₀, rfl⟩ := hD
  obtain ⟨n, B₀, hn, hB₀, rfl⟩ := hB
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨m * n, n • D₀ + m • B₀, Nat.mul_pos hm hn, (eff_nsmul' hD₀ n).add (eff_nsmul' hB₀ m), ?_⟩,
    ⟨c.den * m, c.num.toNat • D₀, Nat.mul_pos c.den_pos hm, eff_nsmul' hD₀ _, ?_⟩,
    ⟨1, 0, one_pos, CartierDiv.eff_zero, ?_⟩⟩
  · funext z
    simp only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul']
    push_cast
    field_simp
  · funext z
    have hnum : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by
      have h1 : ((c.num.toNat : ℤ) : ℚ) = (c.num : ℚ) := by
        rw [Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)]
      exact_mod_cast h1
    have hden : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
    simp only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul']
    push_cast
    rw [hnum]
    conv_lhs => rw [← Rat.num_div_den c]
    field_simp
  · funext z
    simp [qWeil, mult_zero']

end GlobalTheory.QCartCone
