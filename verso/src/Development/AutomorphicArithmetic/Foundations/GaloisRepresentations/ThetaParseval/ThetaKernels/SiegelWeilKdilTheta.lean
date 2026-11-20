import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.ThetaPtOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilSteps

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem om_mem_k {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ hΦ
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem S_mem_k {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (h : UA σ d.A.J) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) : d.S h Φ ∈ d.sch :=
  d.ok.dbl.lin.pres h Φ hΦ
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem thetaPt_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaPt_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ x h
  obtain ⟨-, hTPar, -, hTT, -⟩ := hT
  have hx := _root_.PositivityTheory.SiegelWeilFormula.Kdil.om_mem_k d x hΦ
  rw [(hTT F E σ d Φ hΦ).2 x h, ← ((hTT F E σ d _ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.S_mem_k d h hx)).1).tsum_eq]
  congr 1
  funext X
  exact (hTPar F E σ d _ hx).2.2 h (incM F X)
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
