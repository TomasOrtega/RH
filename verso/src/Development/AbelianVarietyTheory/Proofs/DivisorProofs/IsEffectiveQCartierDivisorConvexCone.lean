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
Use `CartierDiv.mult_add (0 : CartierDiv X) 0 z` as an intermediate fact. Rewrite `this` using `[add_zero]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mult_zero' (z : X) : (0 : CartierDiv X).mult z = 0 := by
  have := CartierDiv.mult_add (0 : CartierDiv X) 0 z
  rw [add_zero] at this
  omega

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, mult_zero']`. Simplify using the standard rewrite rules. Consider the case `succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mult_nsmul' (D : CartierDiv X) (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero']; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul]`. Conclude with `CartierDiv.eff_zero`. Consider the case `succ n ih => rw [succ_nsmul]`. Conclude with `ih.add h`.
-/
theorem eff_nsmul' {D : CartierDiv X} (h : D.Eff) (n : ℕ) : (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

/- English proof (translation)
Introduce `X _ _ D B c hD hB hc`. Take `⟨m, D₀, hm, hD₀, rfl⟩` from `hD`. Take `⟨n, B₀, hn, hB₀, rfl⟩` from `hB`. Establish `hm' : (m : ℚ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hn' : (n : ℚ) ≠ 0` using `by exact_mod_cast hn.ne'`.

Use `⟨⟨m * n, n • D₀ + m • B₀, Nat.mul_pos hm hn, (eff_nsmul' hD₀ n).add (eff_nsmul' hB₀ m), ?_⟩, ⟨c.den * m, c.num.toNat • D₀, Nat.mul_pos c.den_pos hm, eff_nsmul' hD₀ _, ?_⟩, ⟨1, 0, one_pos, CartierDiv.eff_zero, ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Simplify using `only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Use function extensionality and compare the values at `z`. Establish `hnum : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ)`. Establish `h1 : ((c.num.toNat : ℤ) : ℚ) = (c.num : ℚ)`. Rewrite using `[Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)]`. Conclude with `h1` after adjusting the coercions.

Establish `hden : (c.den : ℚ) ≠ 0` using `by exact_mod_cast c.den_pos.ne'`. Simplify using `only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul']`. Use `push_cast`. Rewrite using `[hnum]`. Use `conv_lhs => rw [← Rat.num_div_den c]`.

Clear the denominators using the available nonvanishing facts. Use function extensionality and compare the values at `z`. Simplify using `[qWeil, mult_zero']`.
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
