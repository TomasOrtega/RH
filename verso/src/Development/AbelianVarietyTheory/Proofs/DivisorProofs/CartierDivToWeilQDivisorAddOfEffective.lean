import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltLocusFibre
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.QDivSum

/- English proof (translation)
Introduce `X _ _ p hp`. Use `letI := algebraΓOfHom p`. Introduce `D E a b ha hb hD hE`. Use `⟨(BoundaryFibre.eff_nsmul hD b).add (BoundaryFibre.eff_nsmul hE a), ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`.

Simplify using `only [qWeil, Pi.add_apply, CartierDiv.mult_add, SmallSecHeight.mult_nsmul]`. Establish `ha' : (a : ℚ) ≠ 0` using `by exact_mod_cast ha.ne'`. Establish `hb' : (b : ℚ) ≠ 0` using `by exact_mod_cast hb.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Introduce `C hC`. Establish `e : cls (toLB (b • D + a • E)) (isLB_toLB _) = b • cls (toLB D) (isLB_toLB D) + a • cls (toLB E) (isLB_toLB E)`. Rewrite using `[← toPic_apply, ← toPic_apply, ← toPic_apply, map_add, map_nsmul, map_nsmul]`. Rewrite using `[interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ _ _ (isLB_toLB _) (isLB_toLB D) (isLB_toLB E) b a C hC e]`. Establish `ha' : (a : ℚ) ≠ 0` using `by exact_mod_cast ha.ne'`.

Establish `hb' : (b : ℚ) ≠ 0` using `by exact_mod_cast hb.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem sum_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (D E : CartierDiv X) (a b : ℕ), 0 < a → 0 < b → D.Eff → E.Eff → (b • D + a • E).Eff ∧ qWeil (b • D + a • E) (a * b) = qWeil D a + qWeil E b ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB (b • D + a • E)] : ℚ) / ((a * b : ℕ) : ℚ) = (interNumRed ℂ C ![toLB D] : ℚ) / a + (interNumRed ℂ C ![toLB E] : ℚ) / b := by
  intro X _ _ p hp
  letI := algebraΓOfHom p
  intro D E a b ha hb hD hE
  refine ⟨(BoundaryFibre.eff_nsmul hD b).add (BoundaryFibre.eff_nsmul hE a), ?_, ?_⟩
  · funext z
    simp only [qWeil, Pi.add_apply, CartierDiv.mult_add, SmallSecHeight.mult_nsmul]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp
  · intro C hC
    have e : cls (toLB (b • D + a • E)) (isLB_toLB _) = b • cls (toLB D) (isLB_toLB D) + a • cls (toLB E) (isLB_toLB E) := by
      rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add, map_nsmul, map_nsmul]
    rw [interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ _ _ (isLB_toLB _) (isLB_toLB D) (isLB_toLB E) b a C hC e]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp

end GlobalTheory.QDivSum
