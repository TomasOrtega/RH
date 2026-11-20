import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PairStep

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `CartierDiv.mult_add (0 : CartierDiv X) 0 z`. Rewrite `h` using `[add_zero]`. Rewrite using `[zero_nsmul]`.

Use `push_cast`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mult_nsmul' {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X) (n : ℕ) (z : X) :
    (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    have h := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h
    rw [zero_nsmul]; push_cast; omega
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul]`. Conclude with `CartierDiv.eff_zero`. Consider the case `succ n ih => rw [succ_nsmul]`. Conclude with `ih.add h`.
-/
theorem eff_nsmul' {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

/- English proof (translation)
Introduce `X _ _ p hp N a c D hc hD`. Use `letI := algebraΓOfHom p`. Take `⟨m, D₀, hm, hE, rfl, hI⟩` from `hD`. Choose the witnesses or unpack the hypotheses as in `⟨u, v, hv, rfl⟩ : ∃ u v : ℕ, 0 < v ∧ c = (u : ℚ) / v := by`. Use `⟨c.num.toNat, c.den, c.den_pos, ?_⟩` and prove the remaining obligations.

Establish `h0 : ((c.num.toNat : ℕ) : ℤ) = c.num` using `Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)`. Establish `hd : (c.den : ℚ) ≠ 0` using `by exact_mod_cast c.den_pos.ne'`. Rewrite using `[eq_div_iff hd, Rat.mul_den_eq_num]`. Conclude with `h0.symm` after adjusting the coercions. Establish `hv' : (v : ℚ) ≠ 0` using `by exact_mod_cast hv.ne'`.

Establish `hm' : (m : ℚ) ≠ 0` using `by exact_mod_cast hm.ne'`. Use `⟨v * m, u • D₀, Nat.mul_pos hv hm, eff_nsmul' hE u, ?_, fun C hC => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Simplify using `only [qWeil, Pi.smul_apply, smul_eq_mul, mult_nsmul']`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Establish `e` using `interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB (u • D₀)) (toLB D₀) (toLB D₀) (isLB_toLB _) (isLB_toLB _) (isLB_toLB _) u 0 C hC (by rw [← toPic_apply, ← toPic_apply, map_nsmul, zero_nsmul, add_zero])`. Rewrite using `[e, Nat.cast_zero, zero_mul, add_zero]`. Establish `h1` using `hI C hC`. Use `push_cast`.

Rewrite using `[mul_assoc, ← h1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem qNum_smul : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (a c : ℚ) (D : X → ℚ), 0 ≤ c → QNum p N a D → QNum p N (c * a) (c • D) := by
  intro X _ _ p hp N a c D hc hD
  letI := algebraΓOfHom p
  obtain ⟨m, D₀, hm, hE, rfl, hI⟩ := hD
  obtain ⟨u, v, hv, rfl⟩ : ∃ u v : ℕ, 0 < v ∧ c = (u : ℚ) / v := by
    refine ⟨c.num.toNat, c.den, c.den_pos, ?_⟩
    have h0 : ((c.num.toNat : ℕ) : ℤ) = c.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)
    have hd : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
    rw [eq_div_iff hd, Rat.mul_den_eq_num]
    exact_mod_cast h0.symm
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨v * m, u • D₀, Nat.mul_pos hv hm, eff_nsmul' hE u, ?_, fun C hC => ?_⟩
  · funext z
    simp only [qWeil, Pi.smul_apply, smul_eq_mul, mult_nsmul']
    push_cast
    field_simp
  · have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB (u • D₀)) (toLB D₀) (toLB D₀)
      (isLB_toLB _) (isLB_toLB _) (isLB_toLB _) u 0 C hC
      (by rw [← toPic_apply, ← toPic_apply, map_nsmul, zero_nsmul, add_zero])
    rw [e, Nat.cast_zero, zero_mul, add_zero]
    have h1 := hI C hC
    push_cast
    rw [mul_assoc, ← h1]
    field_simp

end GlobalTheory.PairStep
