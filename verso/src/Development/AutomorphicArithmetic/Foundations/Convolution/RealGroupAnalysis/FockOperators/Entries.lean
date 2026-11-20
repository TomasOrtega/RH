import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.StepInv
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacAnn
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AnnVac

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Set `pw : A F →+* ℝ` to `(Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (TR.pInf F)`. Establish `hO : ∀ i j, pw ((k.1 * k.1ᵀ) i j) = pw ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j)` using `fun i j => congrFun (congrArg (TR.infEq F).symm (hk i j)) w`. Establish `h00` using `hO 0 0`. Establish `h01` using `hO 0 1`. Establish `hd : pw (k 0 0) * pw (k 1 1) - pw (k 0 1) * pw (k 1 0) = 1`.

Establish `h` using `k.det_coe`. Rewrite `h` using `[Matrix.det_fin_two]`. Use `congrArg pw h` as an intermediate fact. Simplify using `using this`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add, map_mul] at h00 h01`.

Simplify using `only [Matrix.one_apply_eq, map_one] at h00`. Simplify using `only [Matrix.one_apply_ne (zero_ne_one : (0 : Fin 2) ≠ 1), map_zero] at h01`. Express the relevant statement in the definitionally equal form `pw (k 0 0) * pw (k 0 0) + pw (k 0 1) * pw (k 0 1) = 1 at h00`. Establish `hc : pw (k 1 0) = -pw (k 0 1)`. Take the linear combination `(-pw (k 1 0)) * h00 + pw (k 0 0) * h01 - pw (k 0 1) * hd`.

Establish `he : pw (k 1 1) = pw (k 0 0)`. Take the linear combination `(-pw (k 1 1)) * h00 + pw (k 0 1) * h01 + pw (k 0 0) * hd`. Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `((pw (k 1 0) : ℝ) : ℂ) = -((pw (k 0 1) : ℝ) : ℂ)`. Rewrite using `[hc]`.

Use `push_cast`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `((pw (k 1 1) : ℝ) : ℂ) = ((pw (k 0 0) : ℝ) : ℂ)`. Rewrite using `[he]`.
-/
private theorem entries {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (k : G1 F) (hk : InfOrth k)
    (w : InfinitePlace F) : cw w (k 1 0) = -cw w (k 0 1) ∧ cw w (k 1 1) = cw w (k 0 0) := by
  let pw : A F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (TR.pInf F)
  have hO : ∀ i j, pw ((k.1 * k.1ᵀ) i j) = pw ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) := fun i j =>
    congrFun (congrArg (TR.infEq F).symm (hk i j)) w
  have h00 := hO 0 0
  have h01 := hO 0 1
  have hd : pw (k 0 0) * pw (k 1 1) - pw (k 0 1) * pw (k 1 0) = 1 := by
    have h := k.det_coe
    rw [Matrix.det_fin_two] at h
    have := congrArg pw h
    simpa using this
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add, map_mul] at h00 h01
  simp only [Matrix.one_apply_eq, map_one] at h00
  simp only [Matrix.one_apply_ne (zero_ne_one : (0 : Fin 2) ≠ 1), map_zero] at h01
  change pw (k 0 0) * pw (k 0 0) + pw (k 0 1) * pw (k 0 1) = 1 at h00
  have hc : pw (k 1 0) = -pw (k 0 1) := by
    linear_combination (-pw (k 1 0)) * h00 + pw (k 0 0) * h01 - pw (k 0 1) * hd
  have he : pw (k 1 1) = pw (k 0 0) := by
    linear_combination (-pw (k 1 1)) * h00 + pw (k 0 1) * h01 + pw (k 0 0) * hd
  constructor
  · change ((pw (k 1 0) : ℝ) : ℂ) = -((pw (k 0 1) : ℝ) : ℂ)
    rw [hc]; push_cast; rfl
  · change ((pw (k 1 1) : ℝ) : ℂ) = ((pw (k 0 0) : ℝ) : ℂ)
    rw [he]

/- English proof (translation)
Establish `e1` using `congrArg (fun T : Module.End ℂ (S4 F) => T φ) (Heisenberg₂ F E D W O k w i).1`. Establish `e2` using `congrArg (fun T : Module.End ℂ (S4 F) => T φ) (Heisenberg₂ F E D W O k w j).2`. Simplify using `only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul] at e1 e2`. Rewrite using `[e1, e2, hc, he, h1, h2]`. Simplify using `only [map_smul, smul_add, smul_smul]`.

Establish `: s * (-cw w (k 0 1) * s) = cw w (k 0 1)` using `by linear_combination (-cw w (k 0 1)) * hs`. Rewrite using `[this, add_comm]`. Use `congr 1`. Rewrite using `[mul_comm]`.
-/
private theorem step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (k : G1 F)
    (w : InfinitePlace F) (i j : Fin 4) (s : ℂ) (hs : s * s = -1)
    (hc : cw w (k 1 0) = -cw w (k 0 1)) (he : cw w (k 1 1) = cw w (k 0 0)) (φ : S4 F)
    (h1 : O.d w i φ = s • O.p D.δ w j φ) (h2 : O.d w j φ = s • O.p D.δ w i φ) :
    O.d w i (W.Om k φ) = s • O.p D.δ w j (W.Om k φ) := by
  have e1 := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (Heisenberg₂ F E D W O k w i).1
  have e2 := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (Heisenberg₂ F E D W O k w j).2
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul] at e1 e2
  rw [e1, e2, hc, he, h1, h2]
  simp only [map_smul, smul_add, smul_smul]
  have : s * (-cw w (k 0 1) * s) = cw w (k 0 1) := by linear_combination (-cw w (k 0 1)) * hs
  rw [this, add_comm]
  congr 1
  rw [mul_comm]

/- English proof (translation)
Establish `hI` using `Complex.I_mul_I`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;>`. Apply the tactic sequence `simp only [Ops.p, kap, cc, Matrix.cons_val, LinearMap.smul_apply, smul_smul] <;>`. Use `congr 1`. Take the linear combination `(-2 * (Real.pi : ℂ)) * hI`.

Take the linear combination `(-2 * (Real.pi : ℂ)) * hI`. Take the linear combination `(-4 * (Real.pi : ℂ)) * hI`. Take the linear combination `(4 * (Real.pi : ℂ) * cw w (rt δ)) * hI`.
-/
private theorem scal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F)
    (w : InfinitePlace F) (f : S4 F) :
    ((-2 * Real.pi * kap δ w 0 : ℂ) • O.x w 0 f = Complex.I • O.p δ w 1 f) ∧
    ((-2 * Real.pi * kap δ w 1 : ℂ) • O.x w 1 f = Complex.I • O.p δ w 0 f) ∧
    ((-2 * Real.pi * kap δ w 2 : ℂ) • O.x w 2 f = (-Complex.I) • O.p δ w 2 f) ∧
    ((-2 * Real.pi * kap δ w 3 : ℂ) • O.x w 3 f = (-Complex.I) • O.p δ w 3 f) := by
  have hI := Complex.I_mul_I
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Ops.p, kap, cc, Matrix.cons_val, LinearMap.smul_apply, smul_smul] <;>
    congr 1
  · linear_combination (-2 * (Real.pi : ℂ)) * hI
  · linear_combination (-2 * (Real.pi : ℂ)) * hI
  · linear_combination (-4 * (Real.pi : ℂ)) * hI
  · linear_combination (4 * (Real.pi : ℂ) * cw w (rt δ)) * hI

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W k hk φ hφ`. Take `⟨O⟩` from `opsEx F`. Establish `hv` using `vacAnn F D.δ O φ hφ`. Use `annVac F D.δ O (W.Om k φ) fun w i => ?_` and prove the remaining obligations. Take `⟨hc, he⟩` from `entries k hk w`.

Establish `hI : Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Establish `hJ : (-Complex.I) * (-Complex.I) = -1` using `by rw [neg_mul_neg, hI]`. Take `⟨s0, s1, s2, s3⟩` from `scal D.δ O w φ`. Take `⟨t0, t1, t2, t3⟩` from `scal D.δ O w (W.Om k φ)`. Establish `v0` using `(hv w 0).trans s0`.

Establish `v1` using `(hv w 1).trans s1`. Establish `v2` using `(hv w 2).trans s2`. Establish `v3` using `(hv w 3).trans s3`. Use `fin_cases i`. Conclude with `(step D W O k w 0 1 _ hI hc he φ v0 v1).trans t0.symm`.

Conclude with `(step D W O k w 1 0 _ hI hc he φ v1 v0).trans t1.symm`. Conclude with `(step D W O k w 2 2 _ hJ hc he φ v2 v2).trans t2.symm`. Conclude with `(step D W O k w 3 3 _ hJ hc he φ v3 v3).trans t3.symm`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.vacOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (k : G1 F), InfOrth k → ∀ φ ∈ Vac D.δ, W.Om k φ ∈ Vac D.δ := by
  intro F E _ _ _ _ _ _ _ D W k hk φ hφ
  obtain ⟨O⟩ := opsEx F
  have hv := vacAnn F D.δ O φ hφ
  refine annVac F D.δ O (W.Om k φ) fun w i => ?_
  obtain ⟨hc, he⟩ := entries k hk w
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hJ : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, hI]
  obtain ⟨s0, s1, s2, s3⟩ := scal D.δ O w φ
  obtain ⟨t0, t1, t2, t3⟩ := scal D.δ O w (W.Om k φ)
  have v0 := (hv w 0).trans s0
  have v1 := (hv w 1).trans s1
  have v2 := (hv w 2).trans s2
  have v3 := (hv w 3).trans s3
  fin_cases i
  · exact (step D W O k w 0 1 _ hI hc he φ v0 v1).trans t0.symm
  · exact (step D W O k w 1 0 _ hI hc he φ v1 v0).trans t1.symm
  · exact (step D W O k w 2 2 _ hJ hc he φ v2 v2).trans t2.symm
  · exact (step D W O k w 3 3 _ hJ hc he φ v3 v3).trans t3.symm
