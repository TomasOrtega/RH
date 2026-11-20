import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNLowerBoundBaseChange
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Introduce a local definition for the expression. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem nuLocC_le_nuPlE_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.DescentSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ T io y C3 C _ _ V ι hι k Y hY a n
  obtain ⟨hint, hval⟩ := GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι
  unfold FBChart.nuPlE
  refine le_iInf₂ ?_
  rintro x ⟨P, hP, f, hf, rfl⟩
  have hh : MvPowerSeries.constantCoeff (a3h C3) = 0 := by
    let _ := io.toAlgebra
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis _ C3.ch.gauge.ax0 0 fun _ => rfl
  unfold FBChart.nab
  rw [hY.h, hY.w0, hY.k]
  refine GlobalTheory.nabValN_lower_bound_baseChange T C V.v ι V.RR (fun x => Iff.rfl) hint _ (𝓞 E) (a3B C3) Y.B hY.F hY.act (a3h C3) hh H.w0 k (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) (fun ℓ => ℓ.2.2) (fun ℓ => chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩) (nuLocC C3 (eOf T V) k a n) ?_ P hP f hf
  intro Q hQ g hg
  rw [← hval]
  unfold nuLocC
  exact iInf_le_of_le Q (iInf_le_of_le hQ (iInf_le_of_le g (iInf_le_of_le hg le_rfl)))

end GlobalTheory
