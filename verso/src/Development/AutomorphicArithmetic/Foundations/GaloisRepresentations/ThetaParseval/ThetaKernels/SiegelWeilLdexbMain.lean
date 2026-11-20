import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.EpsNegUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsStandardHermitianSpace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexbUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexbVal

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Substitute using the available equality.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Simplify using the standard rewrite rules.
-/
theorem hgtPull_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k := by
  intro F E _ _ _ _ _ σ d n h Y b j hn hs hb hJ
  have hB := d.ok.good
  have hσ : ∀ z, σ (σ z) = z := UnitA.sig_sig hB.cm
  refine ⟨fun x => ?_, _root_.PositivityTheory.SiegelWeilFormula.Ldexb.val_pull_k h hJ hb⟩
  obtain ⟨Y₀, b₀, K₀, a₀, hb₀, he₀, hK₀, ha₀⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.exists_standard_hermitian_space hB hn
  obtain ⟨ε, he⟩ := hb.1
  have hK : IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j) := _root_.PositivityTheory.SiegelWeilFormula.Ald.kStd_k F E σ d n h Y b j hb hJ
  rcases hs with ⟨-, hY⟩ | ⟨-, hY⟩
  ·
    have hε : ε = -1 := eps_neg_unit (eps_neg hn hσ hY he)
    subst hε
    obtain ⟨r, hr, hrf, hri⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.exists_skewUnit_k hB
    refine iwa_transport (B := d.B) hσ hb hb₀ he he₀ r ?_ hrf hri hK₀ ha₀.iwa hK x
    rw [hr]; push_cast; ring
  ·
    have hε : ε = 1 := eps_unit (eps_one hn hσ hY he)
    subst hε
    refine iwa_transport (B := d.B) hσ hb hb₀ he he₀ 1 ?_ (fun v => ?_) (fun w => ?_) hK₀ ha₀.iwa hK x
    · simp
    · simp only [Units.val_one, inv_one, map_one]; exact ⟨one_mem _, one_mem _⟩
    · simp
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
