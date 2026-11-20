import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.EntryMul
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkFin

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Substitute using the available equality. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.kkCpt :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], KK F = (M.Ks F : Set (G1 F)) ∧ IsCompact (KK F) := by
  intro F _ _ _
  have h1 : KK F = (M.Ks F : Set (G1 F)) := by
    ext g
    change (InfOrth g ∧ ∀ v, IntAt v g) ↔ gl g ∈ Reduction.maxCompact (K := F) (n := 2)
    rw [Reduction.mem_maxCompact, UpperTheory.ConvolutionTheory.R2.M.kkInf F g]
    exact and_congr_right fun _ => forall_congr' fun v => UpperTheory.ConvolutionTheory.R2.M.kkFin F g v
  refine ⟨h1, ?_⟩
  have hC := Reduction.isCompact_maxCompact (K := F) (n := 2)
  have hD := hC.image (Units.continuous_val)
  have h2 := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hD
  have h3 : KK F = (fun g : G1 F => g.1) ⁻¹' (Units.val '' (Reduction.maxCompact (K := F) (n := 2) : Set (GL (Fin 2) (A F)))) := by
    rw [h1]
    ext g
    constructor
    · intro hg
      exact ⟨gl g, hg, rfl⟩
    · rintro ⟨u, hu, huv⟩
      have : u = gl g := Units.ext huv
      subst this
      exact hu
  rw [h3]
  exact h2
