import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrBCField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Semichar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigenLiftsOfDirectionsBiext
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBaseChangeEigenBasis
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify by unfolding definitions. Substitute using the available equality.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Substitute using the available equality. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem framedPoint_bcGenR (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) : BcGenRSt Xo c := by
  intro p T _ _ ψ y
  obtain ⟨z, hx, -, pm, h1, h2, h3⟩ :=
    GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c p.R T ψ y
  obtain ⟨x, _, _, _, _, _, s, gen⟩ := z
  dsimp only at hx pm h1 h2 h3
  subst hx
  have hpm : pm = bcPm ψ.toRingHom y.x := by
    apply pullback.hom_ext
    · exact h2.trans (bcPm_fst _ _).symm
    · exact h1.trans (bcPm_snd _ _).symm
  subst hpm
  exact ⟨s, h3, gen⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem framedPoint_baseChange_clauses :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), BcLieAnySt Xo c ∧ BcLieRSt Xo c ∧ BcGenRSt Xo c ∧ FrBCFieldSt Xo c := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨?_, ?_, framedPoint_bcGenR E H Dw l Xo c, ?_⟩
  · intro S _ _ K _ _ ψ y τ w hw he
    exact GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c S K ψ y τ w hw he
  · intro p T _ _ ψ y τ w hw he
    exact GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c p.R T ψ y τ w hw he
  · intro S _ _ y K _ _ ψ
    exact GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c S K ψ y

end GlobalTheory
