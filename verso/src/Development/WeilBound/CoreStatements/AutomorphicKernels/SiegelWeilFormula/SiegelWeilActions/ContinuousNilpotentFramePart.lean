import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def nilpotentFrameMatrix {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, Matrix.single L.i₀ (L.em j) (u j)

/- English proof (translation)
The claim follows from `((L.rng (L.em j)).2 ⟨j, rfl⟩)`.
-/
theorem em_ne {d : SD σ} (L : LD d) (j : Fin L.n) : L.em j ≠ L.i₀ := ((L.rng (L.em j)).2 ⟨j, rfl⟩)

/- English proof (translation)
Simplify using `only [nilpotentFrameMatrix, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.single_mul_single_of_ne]`. Conclude with `em_ne L _`.
-/
theorem nilpotent_frame_mul_zero {d : SD σ} (L : LD d) (u v : Fin L.n → AE F E) : nilpotentFrameMatrix L u * nilpotentFrameMatrix L v = 0 := by
  simp only [nilpotentFrameMatrix, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.single_mul_single_of_ne]
  exact em_ne L _

/- English proof (translation)
Use `continuous_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Establish `: (fun u : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (u j)) = fun u => u j • Matrix.single L.i₀ (L.em j) (1 : AE F E)`. Use function extensionality and compare the values at `u`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[this]`.

Conclude with `(continuous_apply j).smul continuous_const`.
-/
theorem continuous_nilpotentFramePart {d : SD σ} (L : LD d) : Continuous (nilpotentFrameMatrix L) := by
  refine continuous_finsetSum _ fun j _ => ?_
  have : (fun u : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (u j)) =
      fun u => u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact (continuous_apply j).smul continuous_const

def muF {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 + nilpotentFrameMatrix L u) 0 0 (((1 - nilpotentFrameMatrix L u)ᵀ).map (cA σ))

def muF' {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 - nilpotentFrameMatrix L u) 0 0 (((1 + nilpotentFrameMatrix L u)ᵀ).map (cA σ))

/- English proof (translation)
Rewrite using `[mul_sub, mul_one, add_mul, one_mul, nilpotent_frame_mul_zero, add_zero, add_sub_cancel_right]`.
-/
theorem one_add_mul_one_sub {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) :
    (1 + nilpotentFrameMatrix L u) * (1 - nilpotentFrameMatrix L u) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, nilpotent_frame_mul_zero, add_zero, add_sub_cancel_right]

/- English proof (translation)
Establish `e1` using `one_add_mul_one_sub L u`. Simplify using `only [muF, muF', Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]`. Rewrite using `[e1, ← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.fromBlocks_one]`.
-/
theorem muF_mul {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : muF L u * muF' L u = 1 := by
  have e1 := one_add_mul_one_sub L u
  simp only [muF, muF', Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [e1, ← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.fromBlocks_one]

/- English proof (translation)
Establish `hσ` using `kfour.sigma_sigma_of_good d.ok.good`. Take `⟨⟨ε, hε⟩, -⟩` from `d.ok.frame`. Take `⟨a', ha⟩` from `h.1 u`. Express the relevant statement in the definitionally equal form `inFrame d.b (uM u) = Matrix.fromBlocks (1 + nilpotentFrameMatrix L u) 0 0 a' at ha`. Establish `hf` using `kunf.frame_eq hε (uM u)`.

Rewrite `hf` using `[ha]`. Establish `h12` using `congrArg Matrix.toBlocks₁₂ hf`. Simplify using `only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12`. Establish `e2 : a'.map (cA σ) = (1 - nilpotentFrameMatrix L u)ᵀ`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Matrix.transpose_mul, one_add_mul_one_sub, Matrix.transpose_one, Matrix.one_mul]`. Use `_ = (1 - nilpotentFrameMatrix L u)ᵀ := by rw [Matrix.mul_assoc, h12, Matrix.mul_one]`. Establish `e3 : a' = ((1 - nilpotentFrameMatrix L u)ᵀ).map (cA σ)`. Rewrite using `[← e2]`. Use extensionality with `i j`.

Simplify using `[Matrix.map_apply, kfour.cA_cA' σ hσ]`. Rewrite using `[ha, e3]`. Both sides reduce to the same expression.
-/
theorem inFrame_uM {d : SD σ} (L : LD d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤)
    (u : Fin L.n → AE F E) : inFrame d.b (uM u) = muF L u := by
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨a', ha⟩ := h.1 u
  change inFrame d.b (uM u) = Matrix.fromBlocks (1 + nilpotentFrameMatrix L u) 0 0 a' at ha
  have hf := kunf.frame_eq hε (uM u)
  rw [ha] at hf
  have h12 := congrArg Matrix.toBlocks₁₂ hf
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12
  have e2 : a'.map (cA σ) = (1 - nilpotentFrameMatrix L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - nilpotentFrameMatrix L u)ᵀ * (1 + nilpotentFrameMatrix L u)ᵀ) * a'.map (cA σ) := by
          rw [← Matrix.transpose_mul, one_add_mul_one_sub, Matrix.transpose_one, Matrix.one_mul]
      _ = (1 - nilpotentFrameMatrix L u)ᵀ := by rw [Matrix.mul_assoc, h12, Matrix.mul_one]
  have e3 : a' = ((1 - nilpotentFrameMatrix L u)ᵀ).map (cA σ) := by
    rw [← e2]
    ext i j
    simp [Matrix.map_apply, kfour.cA_cA' σ hσ]
  rw [ha, e3]
  rfl

/- English proof (translation)
Establish `hN` using `continuous_nilpotentFramePart L`. Establish `hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ)` using `continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)`. Establish `hc : Continuous (muF (σ` using `σ) L) := Continuous.matrix_fromBlocks (continuous_const.add hN) continuous_const continuous_const (hcA.comp (continuous_const.sub hN).matrix_transpose)`. Establish `hc' : Continuous (muF' (σ` using `σ) L) := Continuous.matrix_fromBlocks (continuous_const.sub hN) continuous_const continuous_const (hcA.comp (continuous_const.add hN).matrix_transpose)`. Establish `h1 : Continuous fun u => incM F d.b.1 * muF L u * incM F (d.b⁻¹).1` using `(continuous_const.matrix_mul hc).matrix_mul continuous_const`.

Establish `h2 : Continuous fun u => incM F d.b.1 * muF' L u * incM F (d.b⁻¹).1` using `(continuous_const.matrix_mul hc').matrix_mul continuous_const`. Use `continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Use `h1.congr fun u => ?_ show _ = mat2 (uM u)` and prove the remaining obligations. Rewrite using `[kunf.matrix_eq_inFrame_conj d.b, inFrame_uM L h]`. Use `h2.congr fun u => ?_ show _ = mat2 (uM u)⁻¹` and prove the remaining obligations.

Rewrite using `[kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, inFrame_uM L h, Matrix.inv_eq_right_inv (muF_mul L u)]`.
-/
theorem continuous_uM {d : SD σ} (L : LD d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤) :
    Continuous uM := by
  have hN := continuous_nilpotentFramePart L
  have hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  have hc : Continuous (muF (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.add hN) continuous_const continuous_const
      (hcA.comp (continuous_const.sub hN).matrix_transpose)
  have hc' : Continuous (muF' (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.sub hN) continuous_const continuous_const
      (hcA.comp (continuous_const.add hN).matrix_transpose)
  have h1 : Continuous fun u => incM F d.b.1 * muF L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have h2 : Continuous fun u => incM F d.b.1 * muF' L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc').matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine h1.congr fun u => ?_
    show _ = mat2 (uM u)
    rw [kunf.matrix_eq_inFrame_conj d.b, inFrame_uM L h]
  · refine h2.congr fun u => ?_
    show _ = mat2 (uM u)⁻¹
    rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, inFrame_uM L h,
      Matrix.inv_eq_right_inv (muF_mul L u)]

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
