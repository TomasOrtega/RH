import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.EntryMul
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkFin

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F _ _ _`. Establish `h1 : KK F = (M.Ks F : Set (G1 F))`. Use extensionality with `g`. Express the relevant statement in the definitionally equal form `(InfOrth g ∧ ∀ v, IntAt v g) ↔ gl g ∈ Reduction.maxCompact (K := F) (n := 2)`. Rewrite using `[Reduction.mem_maxCompact, UpperTheory.ConvolutionTheory.R2.M.kkInf F g]`.

Conclude with `and_congr_right fun _ => forall_congr' fun v => UpperTheory.ConvolutionTheory.R2.M.kkFin F g v`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hC` using `Reduction.isCompact_maxCompact (K := F) (n := 2)`. Establish `hD` using `hC.image (Units.continuous_val)`. Establish `h2` using `Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hD`.

Establish `h3 : KK F = (fun g : G1 F => g.1) ⁻¹' (Units.val '' (Reduction.maxCompact (K` using `F) (n := 2) : Set (GL (Fin 2) (A F)))) := by`. Rewrite using `[h1]`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`.

Conclude with `⟨gl g, hg, rfl⟩`. Introduce and unpack `⟨u, hu, huv⟩`. Establish `: u = gl g` using `Units.ext huv`. Substitute `this` using the available equality. Conclude with `hu`.

Rewrite using `[h3]`. Conclude with `h2`.
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
