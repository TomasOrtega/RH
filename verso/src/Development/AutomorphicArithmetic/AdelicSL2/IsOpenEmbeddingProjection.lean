import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal
/- English proof (translation)
Use `Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩` and prove the remaining obligations. Establish `h : (fun g : G1 ℚ => (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) = fun g : G1 ℚ => ((g⁻¹ : G1 ℚ) : Matrix (Fin 2) (Fin 2) (A ℚ))`. Use function extensionality and compare the values at `g`. Establish `: (gl g)⁻¹ = gl g⁻¹`. Rewrite using `[inv_eq_iff_mul_eq_one]`.

Conclude with `Units.ext (by`. Express the relevant statement in the definitionally equal form `(g : Matrix (Fin 2) (Fin 2) (A ℚ)) * ((g⁻¹ : G1 ℚ) : Matrix (Fin 2) (Fin 2) (A ℚ)) = 1`. Rewrite using `[← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one])`. Rewrite using `[this]`. Both sides reduce to the same expression.

Rewrite using `[show (fun x : G1 ℚ => ((((gl x)⁻¹ : GL (Fin 2) (A ℚ))) : Matrix (Fin 2) (Fin 2) (A ℚ))) = _ from h]`. Conclude with `continuous_subtype_val.comp (continuous_inv : Continuous fun g : G1 ℚ => g⁻¹)`.
-/
private theorem continuous_gl' : Continuous (gl : G1 ℚ → GL (Fin 2) (A ℚ)) := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  have h : (fun g : G1 ℚ => (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun g : G1 ℚ => ((g⁻¹ : G1 ℚ) : Matrix (Fin 2) (Fin 2) (A ℚ)) := by
    funext g
    have : (gl g)⁻¹ = gl g⁻¹ := by
      rw [inv_eq_iff_mul_eq_one]
      exact Units.ext (by
        change (g : Matrix (Fin 2) (Fin 2) (A ℚ)) * ((g⁻¹ : G1 ℚ) : Matrix (Fin 2) (Fin 2) (A ℚ)) = 1
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one])
    rw [this]
    rfl
  rw [show (fun x : G1 ℚ => ((((gl x)⁻¹ : GL (Fin 2) (A ℚ))) : Matrix (Fin 2) (Fin 2) (A ℚ))) = _ from h]
  exact continuous_subtype_val.comp (continuous_inv : Continuous fun g : G1 ℚ => g⁻¹)

/- English proof (translation)
Rewrite using `[inv_eq_iff_mul_eq_one, ← dM_mul, mul_inv_cancel]`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `!![1, 0; 0, ((1 : (A ℚ)ˣ) : A ℚ)] = 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem dM_inv' (t : (A ℚ)ˣ) : (dM t)⁻¹ = dM t⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← dM_mul, mul_inv_cancel]
  apply Units.ext
  change !![1, 0; 0, ((1 : (A ℚ)ˣ) : A ℚ)] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Establish `h : (fun t : (A ℚ)ˣ => ((dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) = fun t : (A ℚ)ˣ => !![1, 0; 0, (t : A ℚ)]` using `rfl`. Rewrite using `[h]`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `continuous_const`.

Conclude with `continuous_const`. Conclude with `continuous_const`. Conclude with `Units.continuous_val`.
-/
private theorem continuous_dM_val : Continuous (fun t : (A ℚ)ˣ => ((dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) := by
  have h : (fun t : (A ℚ)ˣ => ((dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun t : (A ℚ)ˣ => !![1, 0; 0, (t : A ℚ)] := rfl
  rw [h]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact Units.continuous_val

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨continuous_dM_val, ?_⟩` and prove the remaining obligations. Establish `h : (fun t : (A ℚ)ˣ => (((dM t)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) = fun t : (A ℚ)ˣ => ((dM t⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))`. Use function extensionality and compare the values at `t`. Rewrite using `[dM_inv']`. Conclude with `h ▸ (continuous_dM_val.comp continuous_inv)`.
-/
private theorem continuous_dM' : Continuous (dM : (A ℚ)ˣ → GL (Fin 2) (A ℚ)) := by
  refine Units.continuous_iff.2 ⟨continuous_dM_val, ?_⟩
  have h : (fun t : (A ℚ)ˣ => (((dM t)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun t : (A ℚ)ˣ => ((dM t⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) := by
    funext t
    rw [dM_inv']
  exact h ▸ (continuous_dM_val.comp continuous_inv)

/- English proof (translation)
Establish `h` using `det_el 1 t`. Simplify using `using h`.
-/
private theorem det_dM' (t : (A ℚ)ˣ) : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (dM t) = t := by
  have h := det_el 1 t
  simpa using h

/- English proof (translation)
Establish `h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹) = 1`. Rewrite using `[map_mul, map_inv, det_dM', mul_inv_cancel]`. Use `congrArg Units.val h` as an intermediate fact. Rewrite `this` using `[GroundTheory.Automorphic.AdelicGLn.coe_det]`. Then use the resulting hypothesis.
-/
private theorem det_rest (x : GL (Fin 2) (A ℚ)) :
    Matrix.det (((x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹ : GL (Fin 2) (A ℚ))) : Matrix (Fin 2) (Fin 2) (A ℚ)) = 1 := by
  have h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹) = 1 := by
    rw [map_mul, map_inv, det_dM', mul_inv_cancel]
  have := congrArg Units.val h
  rwa [GroundTheory.Automorphic.AdelicGLn.coe_det] at this

private noncomputable def rt (x : GL (Fin 2) (A ℚ)) : G1 ℚ × (A ℚ)ˣ :=
  (⟨((x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)), det_rest x⟩,
    GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x)

/- English proof (translation)
Establish `hd` using `GroundTheory.Automorphic.AdelicGLn.continuous_det ℚ 2`. Use `Continuous.prodMk (Continuous.subtype_mk ?_ _) hd` and prove the remaining obligations. Conclude with `Units.continuous_val.comp (continuous_id.mul (continuous_dM'.comp hd).inv)`.
-/
private theorem continuous_rt : Continuous rt := by
  have hd := GroundTheory.Automorphic.AdelicGLn.continuous_det ℚ 2
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hd
  exact Units.continuous_val.comp (continuous_id.mul (continuous_dM'.comp hd).inv)

/- English proof (translation)
Introduce and unpack `⟨g, t⟩`. Use `Prod.ext (Subtype.ext ?_) (det_el g t)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(((gl g * dM t) * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (gl g * dM t)))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = (g : Matrix (Fin 2) (Fin 2) (A ℚ))`. Rewrite using `[det_el, mul_inv_cancel_right]`. Both sides reduce to the same expression.
-/
private theorem rt_pre : Function.LeftInverse rt (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) := by
  rintro ⟨g, t⟩
  refine Prod.ext (Subtype.ext ?_) (det_el g t)
  change (((gl g * dM t) * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (gl g * dM t)))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = (g : Matrix (Fin 2) (Fin 2) (A ℚ))
  rw [det_el, mul_inv_cancel_right]
  rfl

/- English proof (translation)
Establish `hi : (t⁻¹ : (A ℚ)ˣ) ∈ UU` using `US.inv_mem (show t ∈ US from ht)`. Use `RationalIdeles.mem_positiveSubgroup.2 ⟨(IdeleGroup.mem_standardOpenSubgroup ℚ).2 fun v => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (ht.2 v).le`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hi.2 v).le`. Rewrite using `[RationalIdeles.coe_realPart, ht.1, map_one]`.

Conclude with `one_pos`.
-/
private theorem pos_of_UU {t : (A ℚ)ˣ} (ht : t ∈ UU) : t ∈ RationalIdeles.positiveSubgroup := by
  have hi : (t⁻¹ : (A ℚ)ˣ) ∈ UU := US.inv_mem (show t ∈ US from ht)
  refine RationalIdeles.mem_positiveSubgroup.2 ⟨(IdeleGroup.mem_standardOpenSubgroup ℚ).2 fun v => ⟨?_, ?_⟩, ?_⟩
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (ht.2 v).le
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hi.2 v).le
  · rw [RationalIdeles.coe_realPart, ht.1, map_one]
    exact one_pos

/- English proof (translation)
Establish `hr : (RationalIdeles.realPart t : ℝ) = 1`. Rewrite using `[← GroundTheory.Automorphic.GL2Classical.ideleModule_eq_realPart_of_mem hp, hm]`. Take `⟨hs, -⟩` from `RationalIdeles.mem_positiveSubgroup.1 hp`. Use `⟨RationalIdeles.realEquiv.injective ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, ← RationalIdeles.coe_realPart, hr]`.

Take `⟨ha, hb⟩` from `(IdeleGroup.mem_standardOpenSubgroup ℚ).1 hs v`. Establish `ha' : Valued.v (H.cp v (t : A ℚ)) ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha`. Establish `hb' : Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb`. Establish `hm1 : Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (t : A ℚ)) = 1`. Rewrite using `[← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]`.

Use `le_antisymm ha' ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem UU_of_pos {t : (A ℚ)ˣ} (hp : t ∈ RationalIdeles.positiveSubgroup)
    (hm : ((IdeleGroup.ideleModule ℚ t : {r : ℝ // 0 < r}) : ℝ) = 1) : t ∈ UU := by
  have hr : (RationalIdeles.realPart t : ℝ) = 1 := by
    rw [← GroundTheory.Automorphic.GL2Classical.ideleModule_eq_realPart_of_mem hp, hm]
  obtain ⟨hs, -⟩ := RationalIdeles.mem_positiveSubgroup.1 hp
  refine ⟨RationalIdeles.realEquiv.injective ?_, fun v => ?_⟩
  · rw [map_one, ← RationalIdeles.coe_realPart, hr]
  · obtain ⟨ha, hb⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 hs v
    have ha' : Valued.v (H.cp v (t : A ℚ)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha
    have hb' : Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb
    have hm1 : Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (t : A ℚ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    refine le_antisymm ha' ?_
    calc (1 : _) = Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (t : A ℚ)) := hm1.symm
      _ ≤ Valued.v (H.cp v (t : A ℚ)) := mul_le_of_le_one_left' hb'

/- English proof (translation)
Establish `hf : Topology.IsEmbedding (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2)` using `Function.LeftInverse.isEmbedding rt_pre continuous_rt ((continuous_gl'.comp continuous_fst).mul (continuous_dM'.comp continuous_snd))`. Establish `hu : Topology.IsEmbedding (Prod.map id Subtype.val : G1 ℚ × US → G1 ℚ × (A ℚ)ˣ)` using `Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal`. Establish `he : (Subtype.val ∘ pm : G1 ℚ × US → GL (Fin 2) (A ℚ)) = (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) ∘ (Prod.map id Subtype.val : G1 ℚ × US → G1 ℚ × (A ℚ)ˣ)`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression.

Establish `hc : Topology.IsEmbedding (Subtype.val ∘ pm : G1 ℚ × US → GL (Fin 2) (A ℚ))`. Rewrite using `[he]`. Conclude with `hf.comp hu`. Establish `hp : Continuous pm` using `Continuous.subtype_mk hc.continuous _`. Use `⟨Topology.IsEmbedding.of_comp hp continuous_subtype_val hc, ?_⟩` and prove the remaining obligations.

Establish `hs : Set.range pm = (fun x : GG => GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ))) ⁻¹' (RationalIdeles.positiveSubgroup : Set (IdeleGroup ℚ))`. Rewrite using `[range_pm]`. Use extensionality with `x`. Use `⟨fun h => pos_of_UU h, fun h => UU_of_pos h ?_⟩` and prove the remaining obligations. Conclude with `GroundTheory.Automorphic.Reduction.mem_normOneGL.1 x.2`.

Rewrite using `[hs]`. Conclude with `RationalIdeles.isOpen_positiveSubgroup.preimage ((GroundTheory.Automorphic.AdelicGLn.continuous_det ℚ 2).comp continuous_subtype_val)`.
-/
theorem UpperTheory.isOpenEmbedding_projection :
    IsOpenEmbedding pm := by
  have hf : Topology.IsEmbedding (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) :=
    Function.LeftInverse.isEmbedding rt_pre continuous_rt
      ((continuous_gl'.comp continuous_fst).mul (continuous_dM'.comp continuous_snd))
  have hu : Topology.IsEmbedding (Prod.map id Subtype.val : G1 ℚ × US → G1 ℚ × (A ℚ)ˣ) :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  have he : (Subtype.val ∘ pm : G1 ℚ × US → GL (Fin 2) (A ℚ)) =
      (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) ∘ (Prod.map id Subtype.val : G1 ℚ × US → G1 ℚ × (A ℚ)ˣ) := by
    funext p
    rfl
  have hc : Topology.IsEmbedding (Subtype.val ∘ pm : G1 ℚ × US → GL (Fin 2) (A ℚ)) := by
    rw [he]
    exact hf.comp hu
  have hp : Continuous pm := Continuous.subtype_mk hc.continuous _
  refine ⟨Topology.IsEmbedding.of_comp hp continuous_subtype_val hc, ?_⟩
  have hs : Set.range pm = (fun x : GG => GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ))) ⁻¹'
      (RationalIdeles.positiveSubgroup : Set (IdeleGroup ℚ)) := by
    rw [range_pm]
    ext x
    refine ⟨fun h => pos_of_UU h, fun h => UU_of_pos h ?_⟩
    exact GroundTheory.Automorphic.Reduction.mem_normOneGL.1 x.2
  rw [hs]
  exact RationalIdeles.isOpen_positiveSubgroup.preimage
    ((GroundTheory.Automorphic.AdelicGLn.continuous_det ℚ 2).comp continuous_subtype_val)
