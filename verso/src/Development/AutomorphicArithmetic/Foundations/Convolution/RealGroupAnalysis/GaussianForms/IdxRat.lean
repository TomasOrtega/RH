import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpFunctionalSymm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuadraticFormShiftExpand
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuaternaryFormUnitScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.FtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.TestEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpQ

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `map_mul _ _ _`.
-/
private theorem rt_mul (x y : F) : UpperTheory.ConvolutionTheory.R2.rt (x * y) = UpperTheory.ConvolutionTheory.R2.rt x * UpperTheory.ConvolutionTheory.R2.rt y :=
  map_mul _ _ _

/- English proof (translation)
The claim follows from `map_neg _ _`.
-/
private theorem rt_neg (x : F) : UpperTheory.ConvolutionTheory.R2.rt (-x) = -UpperTheory.ConvolutionTheory.R2.rt x :=
  map_neg _ _

/- English proof (translation)
Simplify using `[ψ, UpperTheory.ConvolutionTheory.R2.rt, adelicChar_algebraMap]`.
-/
private theorem psi_rt (x : F) : ψ (UpperTheory.ConvolutionTheory.R2.rt x) = 1 := by
  simp [ψ, UpperTheory.ConvolutionTheory.R2.rt, adelicChar_algebraMap]

/- English proof (translation)
Simplify using `only [q4, UpperTheory.ConvolutionTheory.R2.rt, map_sub, map_mul, map_pow]`.
-/
private theorem quadraticForm_rational_embed (δ : F) (ξ : Fin 4 → F) :
    q4 δ (fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i)) = UpperTheory.ConvolutionTheory.R2.rt (ξ 2 ^ 2 - δ * ξ 3 ^ 2 - ξ 1 * ξ 0) := by
  simp only [q4, UpperTheory.ConvolutionTheory.R2.rt, map_sub, map_mul, map_pow]

/- English proof (translation)
Set `e : (Fin 4 → F) ≃ (Fin 4 → F)` to `{ toFun := fun ξ i => t * ξ i invFun := fun ξ i => t⁻¹ * ξ i left_inv := fun ξ => by funext i; simp [ht] right_inv := fun ξ => by funext i; simp [ht] }`. Conclude with `e.tsum_eq (fun ξ => f fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i))`.
-/
private theorem th_scale (t : F) (ht : t ≠ 0) (f : V4 F → ℂ) :
    (∑' ξ : Fin 4 → F, f fun i => UpperTheory.ConvolutionTheory.R2.rt (t * ξ i)) = Th f := by
  let e : (Fin 4 → F) ≃ (Fin 4 → F) :=
    { toFun := fun ξ i => t * ξ i
      invFun := fun ξ i => t⁻¹ * ξ i
      left_inv := fun ξ => by funext i; simp [ht]
      right_inv := fun ξ => by funext i; simp [ht] }
  exact e.tsum_eq (fun ξ => f fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i))

/- English proof (translation)
The claim follows from `(Equiv.neg (Fin 4 → F)).tsum_eq (fun ξ => f fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i))`.
-/
private theorem th_neg (f : V4 F → ℂ) :
    (∑' ξ : Fin 4 → F, f fun i => UpperTheory.ConvolutionTheory.R2.rt (-ξ i)) = Th f :=
  (Equiv.neg (Fin 4 → F)).tsum_eq (fun ξ => f fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i))

/- English proof (translation)
Simplify using `only [Th]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Rewrite using `[quadraticForm_rational_embed, ← rt_mul, psi_rt, one_mul]`.
-/
private theorem th_chirp (δ t : F) (f : V4 F → ℂ) :
    Th (fun x => ψ (UpperTheory.ConvolutionTheory.R2.rt t * q4 δ x) * f x) = Th f := by
  simp only [Th]
  refine tsum_congr fun ξ => ?_
  rw [quadraticForm_rational_embed, ← rt_mul, psi_rt, one_mul]

/- English proof (translation)
Introduce `F _ _ _ δ hδ t ht`. Set `b : (A F)ˣ` to `Units.map (algebraMap F (A F)).toMonoidHom (Units.mk0 t ht)`. Establish `hb : (b : A F) = UpperTheory.ConvolutionTheory.R2.rt t` using `rfl`. Establish `hbi : ((b⁻¹ : (A F)ˣ) : A F) = UpperTheory.ConvolutionTheory.R2.rt t⁻¹` using `rfl`. Take `⟨c, hc, -⟩` from `idxEx F δ hδ b`.

Take `⟨g, hm, -, hne⟩` from `testEx F`. Generalize the expression as in `four (g1 g) = φ at hm hne`. Establish `hP : Pc δ (b : A F) φ ∈ schwartzBruhatPi F (Fin 4)` using `(pcMem F δ).2 hδ b φ hm`. Establish `hch : (fun x => ψ (UpperTheory.ConvolutionTheory.R2.rt t * q4 δ x) * φ x) ∈ schwartzBruhatPi F (Fin 4)`. Simplify `chirpQ F δ (UpperTheory.ConvolutionTheory.R2.rt t) 0 φ hm` using `[B4]`.

Establish `h1 : Th (Pc δ (b : A F) φ) = Th φ`. Establish `e : ∀ ξ : Fin 4 → F, Pc δ (b : A F) φ (fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i)) = ft4 δ (fun x => ψ (UpperTheory.ConvolutionTheory.R2.rt t * q4 δ x) * φ x) fun i => UpperTheory.ConvolutionTheory.R2.rt (t * ξ i)`. Introduce `ξ`. Rewrite using `[(pcMem F δ).1, hb, quadraticForm_rational_embed, ← rt_mul, psi_rt, one_mul]`. Simplify using `only [rt_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Th (ft4 δ (Pc δ (b : A F) φ)) = c * Th φ`. Establish `e : ∀ ξ : Fin 4 → F, ft4 δ (Pc δ (b : A F) φ) (fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i)) = c * ft4 δ φ fun i => UpperTheory.ConvolutionTheory.R2.rt (-ξ i)`. Introduce `ξ`. Establish `h` using `idxFt F δ b c hc (⟨φ, hm⟩ : S4 F) (fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i))`.

Establish `hn : (-fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i) : V4 F) = fun i => UpperTheory.ConvolutionTheory.R2.rt (-ξ i)`. Use function extensionality and compare the values at `i`. Simplify using `[rt_neg]`. Simplify using `only at h`. Rewrite using `[h, hbi, quadraticForm_rational_embed, ← rt_mul, ← rt_neg, psi_rt, mul_one, hn]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `(ftBasic F δ hδ _ hP).2.2`. Establish `hc1 : c = 1`. Establish `: c * Th φ = 1 * Th φ` using `by rw [← h2, h3, h1, one_mul]`. Conclude with `mul_right_cancel₀ hne this`.

Rewrite `hc` using `[hc1]`. Conclude with `hc`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.idxRat :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), δ ≠ 0 → ∀ t : F, t ≠ 0 → IsIdx δ (rt t) 1 := by
  intro F _ _ _ δ hδ t ht
  let b : (A F)ˣ := Units.map (algebraMap F (A F)).toMonoidHom (Units.mk0 t ht)
  have hb : (b : A F) = UpperTheory.ConvolutionTheory.R2.rt t := rfl
  have hbi : ((b⁻¹ : (A F)ˣ) : A F) = UpperTheory.ConvolutionTheory.R2.rt t⁻¹ := rfl
  obtain ⟨c, hc, -⟩ := idxEx F δ hδ b
  obtain ⟨g, hm, -, hne⟩ := testEx F
  generalize four (g1 g) = φ at hm hne
  have hP : Pc δ (b : A F) φ ∈ schwartzBruhatPi F (Fin 4) := (pcMem F δ).2 hδ b φ hm
  have hch : (fun x => ψ (UpperTheory.ConvolutionTheory.R2.rt t * q4 δ x) * φ x) ∈ schwartzBruhatPi F (Fin 4) := by
    simpa [B4] using chirpQ F δ (UpperTheory.ConvolutionTheory.R2.rt t) 0 φ hm
  have h1 : Th (Pc δ (b : A F) φ) = Th φ := by
    have e : ∀ ξ : Fin 4 → F, Pc δ (b : A F) φ (fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i)) =
        ft4 δ (fun x => ψ (UpperTheory.ConvolutionTheory.R2.rt t * q4 δ x) * φ x) fun i => UpperTheory.ConvolutionTheory.R2.rt (t * ξ i) := by
      intro ξ
      rw [(pcMem F δ).1, hb, quadraticForm_rational_embed, ← rt_mul, psi_rt, one_mul]
      simp only [rt_mul]
    calc Th (Pc δ (b : A F) φ)
        = ∑' ξ : Fin 4 → F, ft4 δ (fun x => ψ (UpperTheory.ConvolutionTheory.R2.rt t * q4 δ x) * φ x) fun i => UpperTheory.ConvolutionTheory.R2.rt (t * ξ i) := tsum_congr e
      _ = Th (ft4 δ fun x => ψ (UpperTheory.ConvolutionTheory.R2.rt t * q4 δ x) * φ x) := th_scale t ht _
      _ = Th (fun x => ψ (UpperTheory.ConvolutionTheory.R2.rt t * q4 δ x) * φ x) := (ftBasic F δ hδ _ hch).2.2
      _ = Th φ := th_chirp δ t φ
  have h2 : Th (ft4 δ (Pc δ (b : A F) φ)) = c * Th φ := by
    have e : ∀ ξ : Fin 4 → F, ft4 δ (Pc δ (b : A F) φ) (fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i)) =
        c * ft4 δ φ fun i => UpperTheory.ConvolutionTheory.R2.rt (-ξ i) := by
      intro ξ
      have h := idxFt F δ b c hc (⟨φ, hm⟩ : S4 F) (fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i))
      have hn : (-fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i) : V4 F) = fun i => UpperTheory.ConvolutionTheory.R2.rt (-ξ i) := by
        funext i
        simp [rt_neg]
      simp only at h
      rw [h, hbi, quadraticForm_rational_embed, ← rt_mul, ← rt_neg, psi_rt, mul_one, hn]
    calc Th (ft4 δ (Pc δ (b : A F) φ))
        = ∑' ξ : Fin 4 → F, c * ft4 δ φ fun i => UpperTheory.ConvolutionTheory.R2.rt (-ξ i) := tsum_congr e
      _ = c * ∑' ξ : Fin 4 → F, ft4 δ φ fun i => UpperTheory.ConvolutionTheory.R2.rt (-ξ i) := tsum_mul_left
      _ = c * Th φ := by rw [th_neg, (ftBasic F δ hδ φ hm).2.2]
  have h3 := (ftBasic F δ hδ _ hP).2.2
  have hc1 : c = 1 := by
    have : c * Th φ = 1 * Th φ := by rw [← h2, h3, h1, one_mul]
    exact mul_right_cancel₀ hne this
  rw [hc1] at hc
  exact hc
