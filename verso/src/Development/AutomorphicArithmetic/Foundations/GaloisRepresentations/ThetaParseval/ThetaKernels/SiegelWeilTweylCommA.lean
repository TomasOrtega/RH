import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.DetWeylBlockNeZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylBase

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
/- English proof (translation)
Take `⟨⟨ε, hε⟩, -⟩` from `d.ok.frame`. Introduce `h0`. Establish `hd : (dbl d.Y.J).det = 0`. Rewrite using `[dbl, Matrix.det_fromBlocks_zero₁₂, h0, zero_mul]`. Establish `h` using `congrArg Matrix.det hε`.

Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, hd, mul_zero, zero_mul]`. Conclude with `det_weyl_block_ne_zero ε h.symm`.
-/
theorem detY_k : d.Y.J.det ≠ 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  intro h0
  have hd : (dbl d.Y.J).det = 0 := by
    rw [dbl, Matrix.det_fromBlocks_zero₁₂, h0, zero_mul]
  have h := congrArg Matrix.det hε
  rw [Matrix.det_mul, Matrix.det_mul, hd, mul_zero, zero_mul] at h
  exact det_weyl_block_ne_zero ε h.symm
/- English proof (translation)
Break down `d.ok.sign with ⟨-, h⟩ | ⟨-, h⟩` into its components or cases. Conclude with `⟨-1, fun i j => by rw [h]; simp⟩`. Conclude with `⟨1, fun i j => by rw [h]; simp⟩`.
-/
theorem signY_k : ∃ ε : ℤˣ, ∀ i j, σ (d.Y.J j i) = ((ε : ℤ) : E) * d.Y.J i j := by
  rcases d.ok.sign with ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨-1, fun i j => by rw [h]; simp⟩
  · exact ⟨1, fun i j => by rw [h]; simp⟩
/- English proof (translation)
Take `⟨φz, hφz, hφz0⟩` from `GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F d.κ`. Establish `hne : d.T φz ≠ 0` using `fun h => hφz0 (by rw [(hT F E σ d).2.2 φz hφz h]; rfl)`. Choose the witnesses or unpack the hypotheses as in `⟨X, hX⟩ : ∃ X, d.T φz X ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hne (funext h)`. Conclude with `⟨_, GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.tweyl.std_k d) _ φz hφz, hX⟩`.
-/
theorem exists_l_ne_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) : ∃ φ ∈ schA F d.κ, d.l φ ≠ 0 := by
  obtain ⟨φz, hφz, hφz0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F d.κ
  have hne : d.T φz ≠ 0 := fun h => hφz0 (by rw [(hT F E σ d).2.2 φz hφz h]; rfl)
  obtain ⟨X, hX⟩ : ∃ X, d.T φz X ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  exact ⟨_, GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.tweyl.std_k d) _ φz hφz, hX⟩
end PositivityTheory.SiegelWeilFormula.tweyl
end
end
