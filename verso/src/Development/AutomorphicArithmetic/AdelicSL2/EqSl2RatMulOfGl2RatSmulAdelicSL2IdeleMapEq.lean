import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

/- English proof (translation)
Take `⟨h1, h2⟩` from `x.2`. Use `set t : IdeleGroup ℚ := (x : (A ℚ)ˣ) with ht`. Establish `hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1`. Introduce `v`. Rewrite using `[← map_mul]`.

Establish `h` using `congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))`. Establish `h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v * ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1` using `h`. Rewrite using `[h', map_one]`. Use `RationalIdeles.mem_positiveSubgroup.2 ⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ`.

Use `(mem_finiteIntegralUnits ℚ).2 fun v => ?_` and prove the remaining obligations. Establish `hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1` using `h2 v`. Establish `hi` using `hinv v`. Rewrite `hi` using `[hv, mul_one]`. Conclude with `⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩`.

Rewrite using `[RationalIdeles.coe_realPart]`. Establish `h1' : (t : NumberField.AdeleRing (𝓞 ℚ) ℚ).1 = 1` using `h1`. Rewrite using `[h1', map_one]`. Conclude with `one_pos`.
-/
private theorem us_pos (x : US) : ((x : (A ℚ)ˣ) : IdeleGroup ℚ) ∈ RationalIdeles.positiveSubgroup := by
  obtain ⟨h1, h2⟩ := x.2
  set t : IdeleGroup ℚ := (x : (A ℚ)ˣ) with ht
  have hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    intro v
    rw [← map_mul]
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))
    have h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
    rw [h', map_one]
  refine RationalIdeles.mem_positiveSubgroup.2 ⟨?_, ?_⟩
  · change IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ
    refine (mem_finiteIntegralUnits ℚ).2 fun v => ?_
    have hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := h2 v
    have hi := hinv v
    rw [hv, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  · rw [RationalIdeles.coe_realPart]
    have h1' : (t : NumberField.AdeleRing (𝓞 ℚ) ℚ).1 = 1 := h1
    rw [h1', map_one]
    exact one_pos

/- English proof (translation)
Introduce `γ p q h`. Take `⟨r, hr⟩` from `γ.2`. Establish `h1 : GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r * (gl p.1 * dM (p.2 : (A ℚ)ˣ)) = gl q.1 * dM (q.2 : (A ℚ)ˣ)`. Rewrite using `[hr]`. Conclude with `congrArg Subtype.val h`.

Establish `hdet : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r) = IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r)`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]`. Conclude with `(RingHom.map_det (algebraMap ℚ _) (r : Matrix (Fin 2) (Fin 2) ℚ)).symm`. Establish `h2 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) * (p.2 : (A ℚ)ˣ) = (q.2 : (A ℚ)ˣ)`.

Use `congrArg (GroundTheory.Automorphic.AdelicGLn.det ℚ 2) h1` as an intermediate fact. Rewrite `this` using `[map_mul, det_el, det_el, hdet]`. Then use the resulting hypothesis. Establish `h3 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) = ((q.2 * p.2⁻¹ : US) : (A ℚ)ˣ)`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, ← h2, mul_inv_cancel_right]`. Establish `h4 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) = 1`.

Establish `hm : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) ∈ RationalIdeles.positiveSubgroup ⊓ (IdeleGroup.diagonal ℚ).range` using `⟨h3 ▸ us_pos _, ⟨_, rfl⟩⟩`. Rewrite `hm` using `[RationalIdeles.positiveSubgroup_inf_diagonal_range]`. Conclude with `hm`. Establish `h5 : (q.2 : (A ℚ)ˣ) = (p.2 : (A ℚ)ˣ)` using `by rw [← h2, h4, one_mul]`. Establish `h6 : (r : Matrix (Fin 2) (Fin 2) ℚ).det = 1`.

Use `congrArg Units.val h4` as an intermediate fact. Rewrite `this` using `[IdeleGroup.coe_diagonal, Units.val_one]`. Apply `NumberField.AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ` to reduce the goal to its premises. Rewrite using `[map_one]`. Conclude with `this`.

Set `s : SpecialLinearGroup (Fin 2) ℚ` to `⟨r.val, h6⟩`. Establish `h7 : GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r = gl (ratS ℚ s)`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression.

Use `⟨Subtype.ext h5, s, ?_, hr.symm.trans h7⟩` and prove the remaining obligations. Rewrite `h1` using `[h5, h7, ← mul_assoc]`. Establish `h8 : gl (ratS ℚ s) * gl p.1 = gl q.1` using `mul_right_cancel h1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Units.val h8` as an intermediate fact.

Conclude with `this.symm`.
-/
theorem UpperTheory.eq_sl2Rat_mul_of_gl2Rat_smul_adelicSL2IdeleMap_eq :
    ∀ (γ : Ga) (p q : G1 ℚ × US), γ • pm p = pm q → q.2 = p.2 ∧ ∃ s : SpecialLinearGroup (Fin 2) ℚ, q.1 = ratS ℚ s * p.1 ∧ ((γ : GG) : GL (Fin 2) (A ℚ)) = gl (ratS ℚ s) := by
  intro γ p q h
  obtain ⟨r, hr⟩ := γ.2
  have h1 : GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r * (gl p.1 * dM (p.2 : (A ℚ)ˣ)) = gl q.1 * dM (q.2 : (A ℚ)ˣ) := by
    rw [hr]
    exact congrArg Subtype.val h
  have hdet : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r) =
      IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) := by
    refine Units.ext ?_
    rw [GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
    exact (RingHom.map_det (algebraMap ℚ _) (r : Matrix (Fin 2) (Fin 2) ℚ)).symm
  have h2 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) * (p.2 : (A ℚ)ˣ) = (q.2 : (A ℚ)ˣ) := by
    have := congrArg (GroundTheory.Automorphic.AdelicGLn.det ℚ 2) h1
    rwa [map_mul, det_el, det_el, hdet] at this
  have h3 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) = ((q.2 * p.2⁻¹ : US) : (A ℚ)ˣ) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← h2, mul_inv_cancel_right]
  have h4 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) = 1 := by
    have hm : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) ∈
        RationalIdeles.positiveSubgroup ⊓ (IdeleGroup.diagonal ℚ).range :=
      ⟨h3 ▸ us_pos _, ⟨_, rfl⟩⟩
    rw [RationalIdeles.positiveSubgroup_inf_diagonal_range] at hm
    exact hm
  have h5 : (q.2 : (A ℚ)ˣ) = (p.2 : (A ℚ)ˣ) := by rw [← h2, h4, one_mul]
  have h6 : (r : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    have := congrArg Units.val h4
    rw [IdeleGroup.coe_diagonal, Units.val_one] at this
    apply NumberField.AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ
    rw [map_one]
    exact this
  let s : SpecialLinearGroup (Fin 2) ℚ := ⟨r.val, h6⟩
  have h7 : GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r = gl (ratS ℚ s) := by
    apply Units.ext
    ext i j
    rfl
  refine ⟨Subtype.ext h5, s, ?_, hr.symm.trans h7⟩
  rw [h5, h7, ← mul_assoc] at h1
  have h8 : gl (ratS ℚ s) * gl p.1 = gl q.1 := mul_right_cancel h1
  apply Subtype.ext
  have := congrArg Units.val h8
  exact this.symm
