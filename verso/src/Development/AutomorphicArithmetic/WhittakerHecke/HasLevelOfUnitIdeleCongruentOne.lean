import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Introduce `L _ t ht hD`. Establish `h1 : (t : A ℚ).1 = 1` using `ht.1`. Establish `hu : ∀ v : H.P ℚ, Valued.v (H.cp v (t : A ℚ)) = 1` using `ht.2`. Establish `hi : ∀ v : H.P ℚ, Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) = 1`. Introduce `v`.

Establish `hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Use `congrArg Valued.v hm` as an intermediate fact. Rewrite `this` using `[map_mul, hu v, one_mul, map_one]`. Then use the resulting hypothesis. Establish `hz : ∀ v : H.P ℚ, Dv L v 0`.

Introduce `v`. Simplify using `[Dv]`. Use `⟨fun i j => ?_, fun v => ⟨?_, fun i j => ?_⟩⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aE, h1] <;> rfl`. Rewrite using `[H.KAt, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]`.

Establish `e1 : (1 : H.Kv v) ∈ Formalism.UG.Ov ℚ v` using `one_mem _`. Establish `e0 : (0 : H.Kv v) ∈ Formalism.UG.Ov ℚ v` using `zero_mem _`. Establish `et : H.cp v (t : A ℚ) ∈ Formalism.UG.Ov ℚ v` using `(hu v).le`. Establish `ei : H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) ∈ Formalism.UG.Ov ℚ v` using `(hi v).le`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify `et` using `[aE, Matrix.GeneralLinearGroup.map]`. Simplify `e0` using `[aE, Matrix.GeneralLinearGroup.map]`. Simplify `e0` using `[aE, Matrix.GeneralLinearGroup.map]`. Simplify `e1` using `[aE, Matrix.GeneralLinearGroup.map]`.

Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `ei`. Simplify `e0` using `[aE, Matrix.GeneralLinearGroup.map]`. Simplify `e0` using `[aE, Matrix.GeneralLinearGroup.map]`. Simplify `e1` using `[aE, Matrix.GeneralLinearGroup.map]`.

Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify `hD v` using `[aE]`. Simplify `hz v` using `[aE]`. Simplify `hz v` using `[aE]`. Simplify `hz v` using `[aE]`.
-/
theorem UpperTheory.hasLevel_of_unitIdele_congruent_one :
    ∀ (L : ℕ), 0 < L → ∀ t : (A ℚ)ˣ, t ∈ UU → (∀ v, Dv L v ((t : A ℚ) - 1)) → Lev L (aE t) := by
  intro L _ t ht hD
  have h1 : (t : A ℚ).1 = 1 := ht.1
  have hu : ∀ v : H.P ℚ, Valued.v (H.cp v (t : A ℚ)) = 1 := ht.2
  have hi : ∀ v : H.P ℚ, Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) = 1 := by
    intro v
    have hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have := congrArg Valued.v hm
    rwa [map_mul, hu v, one_mul, map_one] at this
  have hz : ∀ v : H.P ℚ, Dv L v 0 := by
    intro v
    simp [Dv]
  refine ⟨fun i j => ?_, fun v => ⟨?_, fun i j => ?_⟩⟩
  · fin_cases i <;> fin_cases j <;> simp [aE, h1] <;> rfl
  · rw [H.KAt, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
    have e1 : (1 : H.Kv v) ∈ Formalism.UG.Ov ℚ v := one_mem _
    have e0 : (0 : H.Kv v) ∈ Formalism.UG.Ov ℚ v := zero_mem _
    have et : H.cp v (t : A ℚ) ∈ Formalism.UG.Ov ℚ v := (hu v).le
    have ei : H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) ∈ Formalism.UG.Ov ℚ v := (hi v).le
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa [aE, Matrix.GeneralLinearGroup.map] using et
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e1
    · fin_cases i <;> fin_cases j
      · exact ei
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e1
  · fin_cases i <;> fin_cases j
    · simpa [aE] using hD v
    · simpa [aE] using hz v
    · simpa [aE] using hz v
    · simpa [aE] using hz v
