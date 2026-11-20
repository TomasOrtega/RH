import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruenceOneMatricesMemNhdsOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCongruenceOneMatricesMemNhdsOne.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.congruenceOne_matrices_mem_nhds_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ N ∈ nhds (1 : GL (Fin n) (AfE F E)), ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → 0 < m →
      ∀ k : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k → GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k⁻¹ → k ∈ N := by
  first | exact @GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds | exact GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds | (intros; apply GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds <;> assumption)
