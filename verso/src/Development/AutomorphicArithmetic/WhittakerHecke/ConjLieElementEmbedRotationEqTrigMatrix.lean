import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NzCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CoordMk
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

/- English proof (translation)
Establish `h1` using `(UpperTheory.ConvolutionTheory.R2.Fo.coordMk ℚ E D).1 w.embedding ((rot t).val i j) 0`. Rewrite `h1` using `[FieldIso.coord_embedding]`. Establish `h2 : D.mkE ((rot t).val i j) 0 = AdeleBaseChange.adeleMap ℚ E ((rot t).val i j)`. Simplify using `[Dat.mkE]`. Establish `h3 : TR.pInf ℚ ((rot t).val i j) = (Nz.X t).val i j`.

Establish `h` using `congrArg (fun g : GL (Fin 2) (TR.Rinf ℚ) => g.val i j) (TR.pInf_infGL (Nz.X t))`. Rewrite `h` using `[← Nz.rot_eq]`. Conclude with `h`. Express the relevant statement in the definitionally equal form `pInf E (AdeleBaseChange.adeleMap ℚ E ((rot t).val i j)) w = _`. Rewrite using `[← h2, h1]`.

Simplify using `[Fo.cw, h3]`.
-/
private theorem kInf_val {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ)
    (i j : Fin 2) (w : InfinitePlace E) :
    (kInf (em E (rot t))).val i j w = (((Nz.X t).val i j (Fo.pl ℚ w.embedding) : ℝ) : ℂ) := by
  have h1 := (UpperTheory.ConvolutionTheory.R2.Fo.coordMk ℚ E D).1 w.embedding ((rot t).val i j) 0
  rw [FieldIso.coord_embedding] at h1
  have h2 : D.mkE ((rot t).val i j) 0 = AdeleBaseChange.adeleMap ℚ E ((rot t).val i j) := by
    simp [Dat.mkE]
  have h3 : TR.pInf ℚ ((rot t).val i j) = (Nz.X t).val i j := by
    have h := congrArg (fun g : GL (Fin 2) (TR.Rinf ℚ) => g.val i j) (TR.pInf_infGL (Nz.X t))
    rw [← Nz.rot_eq] at h
    exact h
  change pInf E (AdeleBaseChange.adeleMap ℚ E ((rot t).val i j)) w = _
  rw [← h2, h1]
  simp [Fo.cw, h3]

/- English proof (translation)
Use extensionality with `i j w`. Rewrite using `[kInf_val D]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Nz.X]`.
-/
private theorem kInf_rot {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ) :
    (kInf (em E (rot t))).val =
      !![fun _ => (Real.cos t : ℂ), fun _ => -(Real.sin t : ℂ); fun _ => (Real.sin t : ℂ), fun _ => (Real.cos t : ℂ)] := by
  ext i j w
  rw [kInf_val D]
  fin_cases i <;> fin_cases j <;> simp [Nz.X]

/- English proof (translation)
Introduce `E _ _ _ D t`. Establish `hinv : (kInf (em E (rot t)))⁻¹ = kInf (em E (rot (-t)))`. Rewrite using `[Nz.rot_neg, map_inv]`. Simplify using `[kInf, map_inv]`. Rewrite using `[XB, hinv, kInf_rot D, kInf_rot D]`.

Use extensionality with `i j w`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;> ring`.
-/
theorem UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ), XB D (em E (rot t)) = !![(Real.cos t * Real.sin t) • thInf D, (Real.cos t ^ 2) • thInf D; -((Real.sin t ^ 2) • thInf D), -((Real.cos t * Real.sin t) • thInf D)] := by
  intro E _ _ _ D t
  have hinv : (kInf (em E (rot t)))⁻¹ = kInf (em E (rot (-t))) := by
    rw [Nz.rot_neg, map_inv]
    simp [kInf, map_inv]
  rw [XB, hinv, kInf_rot D, kInf_rot D]
  ext i j w
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;> ring
