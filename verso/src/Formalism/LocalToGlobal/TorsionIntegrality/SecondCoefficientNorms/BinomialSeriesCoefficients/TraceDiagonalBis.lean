import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.GramFormula
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareEqDiagOfQuadraticEven
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.CharacterExistsAllEmbeddings

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

namespace Gram

open Pts Calc Formalism.HermitianLattices.IntegralLatticeDensity

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem coe_sum_nm {O : Type} [CommRing O] [StarRing O] {n : Type} [Fintype n] (a : n → O) :
    ((∑ i, nm (a i) : saRing O) : O) = ∑ i, star (a i) * a i := by
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl

end Gram

open Pts Calc Gram Formalism.HermitianLattices.IntegralLatticeDensity in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem gram_formula : GramFormula := by
  intro K _ _ R l linv ph hFr O _ _ τ hE hB hF1 hN hA n _ k A σ u hu
  have D : Data R l linv τ := ⟨hFr.1, hFr.2.1, hE, hB⟩
  have key := Formalism.HermitianLattices.WeilRepresentation.gram_expansion (saRing O) O (ptsSub D σ) (Ser τ σ ⧸ lgSub D σ)
    (phi D ph) nm (cob_add D hF1) (fun α a b => cob_adj D (hA α) a b)
    (fun α u => phi_norm D (hN α) u) n k A (fun j => toM D (u j) (hu j))
  simp only [cob_phi, pt_smul, pt_toM] at key
  unfold phi at key
  simp only [pt_sum, pt_toM, ← cls_smul, coe_sum_nm] at key
  simp only [← cls_sum] at key
  rw [← cls_add, cls_eq] at key
  exact key

namespace Gram

section Rat

open USideA IntegralMvPolynomialLemmas Pts

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_lam (e : PowerSeries K) (s2 : K) :
    PowerSeries.constantCoeff (lam e s2) = 0 := by
  unfold lam dblInt
  rw [map_add, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  simp

end Rat

end Gram

end Formalism.L2.Th1.C
