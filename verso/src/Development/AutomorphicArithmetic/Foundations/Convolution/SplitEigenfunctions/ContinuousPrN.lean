import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.AutomorphicForms.Reduction

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical Pointwise ENNReal

noncomputable section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private abbrev dt (g : GL (Fin 2) (A E)) : (A E)ˣ := GroundTheory.Automorphic.AdelicGLn.det E 2 g

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use `show (dM t).val.det = (t : A E)`. Simplify using `[dM, Matrix.det_fin_two]`.
-/
private theorem dt_dM (t : (A E)ˣ) : dt (dM t) = t := by
  refine Units.ext ?_
  show (dM t).val.det = (t : A E)
  simp [dM, Matrix.det_fin_two]

/- English proof (translation)
The claim follows from `Units.ext h.det_coe`.
-/
private theorem dt_gl (h : G1 E) : dt (gl h) = 1 :=
  Units.ext h.det_coe

/- English proof (translation)
The claim follows from `GroundTheory.Automorphic.AdelicGLn.continuous_det E 2`.
-/
private theorem continuous_dt : Continuous (dt : GL (Fin 2) (A E) → (A E)ˣ) :=
  GroundTheory.Automorphic.AdelicGLn.continuous_det E 2

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j <;> simp [dM] <;> first | exact continuous_const | exact Units.continuous_val`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Establish `e : ∀ t : (A E)ˣ, (((dM t)⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) = !![1, 0; 0, ((t⁻¹ : (A E)ˣ) : A E)]` using `fun t => rfl`. Simplify using `only [e]`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact Units.continuous_coe_inv`.
-/
private theorem continuous_dM' : Continuous (dM : (A E)ˣ → GL (Fin 2) (A E)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [dM] <;> first | exact continuous_const | exact Units.continuous_val
  · refine continuous_matrix fun i j => ?_
    have e : ∀ t : (A E)ˣ, (((dM t)⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) = !![1, 0; 0, ((t⁻¹ : (A E)ˣ) : A E)] := fun t => rfl
    simp only [e]
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact Units.continuous_coe_inv

private def pr (g : GL (Fin 2) (A E)) : G1 E :=
  ⟨(g * (dM (dt g))⁻¹).val, by
    have h : dt (g * (dM (dt g))⁻¹) = 1 := by
      rw [dt, map_mul, map_inv]
      show dt g * (dt (dM (dt g)))⁻¹ = 1
      rw [dt_dM, mul_inv_cancel]
    exact congrArg Units.val h⟩

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
private theorem gl_pr (g : GL (Fin 2) (A E)) : gl (pr g) = g * (dM (dt g))⁻¹ := Units.ext rfl

/- English proof (translation)
The claim follows from `map_mul _ x y`.
-/
private theorem dt_mul (x y : GL (Fin 2) (A E)) : dt (x * y) = dt x * dt y := map_mul _ x y

/- English proof (translation)
Apply `M.gl_inj` to reduce the goal to its premises. Establish `hm : gl (h * pr g) = gl h * gl (pr g)` using `map_mul _ h (pr g)`. Rewrite using `[hm, gl_pr, gl_pr, dt_mul, dt_gl, one_mul, mul_assoc]`.
-/
private theorem pr_gl_mul (h : G1 E) (g : GL (Fin 2) (A E)) : pr (gl h * g) = h * pr g := by
  apply M.gl_inj
  have hm : gl (h * pr g) = gl h * gl (pr g) := map_mul _ h (pr g)
  rw [hm, gl_pr, gl_pr, dt_mul, dt_gl, one_mul, mul_assoc]

/- English proof (translation)
Apply `M.gl_inj` to reduce the goal to its premises. Rewrite using `[gl_pr, dt_gl]`. Establish `: dM (1 : (A E)ˣ) = 1` using `M.dM_one`. Rewrite using `[this, inv_one, mul_one]`.
-/
private theorem pr_gl (h : G1 E) : pr (gl h) = h := by
  apply M.gl_inj
  rw [gl_pr, dt_gl]
  have : dM (1 : (A E)ˣ) = 1 := M.dM_one
  rw [this, inv_one, mul_one]

/- English proof (translation)
Rewrite using `[gl_pr, inv_mul_cancel_right]`.
-/
private theorem gl_pr_mul (g : GL (Fin 2) (A E)) : gl (pr g) * dM (dt g) = g := by
  rw [gl_pr, inv_mul_cancel_right]

/- English proof (translation)
Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `Units.continuous_val.comp (continuous_id.mul (continuous_dM'.comp continuous_dt).inv)`.
-/
private theorem continuous_pr : Continuous (pr : GL (Fin 2) (A E) → G1 E) := by
  refine Continuous.subtype_mk ?_ _
  exact Units.continuous_val.comp (continuous_id.mul (continuous_dM'.comp continuous_dt).inv)

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]`. Conclude with `(RingHom.map_det (algebraMap E (A E)) (γ : Matrix (Fin 2) (Fin 2) E)).symm`.
-/
private theorem dt_diag (γ : GL (Fin 2) E) :
    dt (GroundTheory.Automorphic.AdelicGLn.diagonal E 2 γ) = IdeleGroup.diagonal E (Matrix.GeneralLinearGroup.det γ) := by
  refine Units.ext ?_
  rw [GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
  exact (RingHom.map_det (algebraMap E (A E)) (γ : Matrix (Fin 2) (Fin 2) E)).symm

/- English proof (translation)
Apply the tactic sequence `refine ⟨⟨!![1, 0; 0, (e : E)], !![1, 0; 0, ((e⁻¹ : Eˣ) : E)], by ext i j; fin_cases i <;> fin_cases j <;> simp, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩, ?_⟩`. Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[show ∀ g : GL (Fin 2) E, ((GroundTheory.Automorphic.AdelicGLn.diagonal E 2 g : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) i j = algebraMap E (A E) (g i j) from fun g => rfl]`. Apply the tactic sequence `fin_cases i <;> fin_cases j`.

Simplify using `[dM]`. Simplify using `[dM]`. Simplify using `[dM]`. Simplify using `[dM, IdeleGroup.coe_diagonal]`.
-/
private theorem dM_diag (e : Eˣ) : dM (IdeleGroup.diagonal E e) ∈ GroundTheory.Automorphic.AdelicGLn.rationalGL E 2 := by
  refine ⟨⟨!![1, 0; 0, (e : E)], !![1, 0; 0, ((e⁻¹ : Eˣ) : E)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩, ?_⟩
  refine Units.ext ?_
  ext i j
  rw [show ∀ g : GL (Fin 2) E, ((GroundTheory.Automorphic.AdelicGLn.diagonal E 2 g : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) i j = algebraMap E (A E) (g i j) from fun g => rfl]
  fin_cases i <;> fin_cases j
  · simp [dM]
  · simp [dM]
  · simp [dM]
  · simp [dM, IdeleGroup.coe_diagonal]

/- English proof (translation)
Use `haveI := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E 2`. Take `⟨V, hV, hVe⟩` from `isOpen_induced_iff.1 (isOpen_discrete ({1} : Set (GroundTheory.Automorphic.AdelicGLn.rationalGL E 2)))`. Use `⟨V, hV, ?_, fun e he => ?_⟩` and prove the remaining obligations. Establish `: (1 : GroundTheory.Automorphic.AdelicGLn.rationalGL E 2) ∈ Subtype.val ⁻¹' V` using `by rw [hVe]; rfl`. Conclude with `this`.

Establish `hin : (⟨_, dM_diag e⟩ : GroundTheory.Automorphic.AdelicGLn.rationalGL E 2) ∈ Subtype.val ⁻¹' V` using `he`. Rewrite `hin` using `[hVe]`. Conclude with `congrArg Subtype.val (Set.mem_singleton_iff.1 hin)`.
-/
private theorem exists_V : ∃ V : Set (GL (Fin 2) (A E)), IsOpen V ∧ (1 : GL (Fin 2) (A E)) ∈ V ∧
    ∀ e : Eˣ, dM (IdeleGroup.diagonal E e) ∈ V → dM (IdeleGroup.diagonal E e) = 1 := by
  haveI := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E 2
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.1
    (isOpen_discrete ({1} : Set (GroundTheory.Automorphic.AdelicGLn.rationalGL E 2)))
  refine ⟨V, hV, ?_, fun e he => ?_⟩
  · have : (1 : GroundTheory.Automorphic.AdelicGLn.rationalGL E 2) ∈ Subtype.val ⁻¹' V := by rw [hVe]; rfl
    exact this
  · have hin : (⟨_, dM_diag e⟩ : GroundTheory.Automorphic.AdelicGLn.rationalGL E 2) ∈ Subtype.val ⁻¹' V := he
    rw [hVe] at hin
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 hin)

/- English proof (translation)
Establish `hf : Continuous fun p : (A E)ˣ × (A E)ˣ => p.1 * p.2⁻¹` using `continuous_fst.mul continuous_snd.inv`. Establish `hf1 : (fun p : (A E)ˣ × (A E)ˣ => p.1 * p.2⁻¹) ⁻¹' U ∈ 𝓝 ((1 : (A E)ˣ), (1 : (A E)ˣ))` using `hf.continuousAt.preimage_mem_nhds (by simpa using hU)`. Take `⟨U₁, hU₁, U₂, hU₂, hUU⟩` from `mem_nhds_prod_iff.1 hf1`. Take `⟨K₀, hK₀, hK₀n⟩` from `exists_compact_mem_nhds (1 : (A E)ˣ)`. Use `⟨interior (K₀ ∩ (U₁ ∩ U₂)), K₀, isOpen_interior, mem_interior_iff_mem_nhds.2 (inter_mem hK₀n (inter_mem hU₁ hU₂)), hK₀, interior_subset.trans Set.inter_subset_left, ?_⟩` and prove the remaining obligations.

Introduce `x hx y hy`. Conclude with `hUU (Set.mk_mem_prod (interior_subset hx).2.1 (interior_subset hy).2.2)`.
-/
private theorem exists_U {U : Set (A E)ˣ} (hU : U ∈ 𝓝 (1 : (A E)ˣ)) :
    ∃ W K₀ : Set (A E)ˣ, IsOpen W ∧ (1 : (A E)ˣ) ∈ W ∧ IsCompact K₀ ∧ W ⊆ K₀ ∧ ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ U := by
  have hf : Continuous fun p : (A E)ˣ × (A E)ˣ => p.1 * p.2⁻¹ := continuous_fst.mul continuous_snd.inv
  have hf1 : (fun p : (A E)ˣ × (A E)ˣ => p.1 * p.2⁻¹) ⁻¹' U ∈ 𝓝 ((1 : (A E)ˣ), (1 : (A E)ˣ)) :=
    hf.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨U₁, hU₁, U₂, hU₂, hUU⟩ := mem_nhds_prod_iff.1 hf1
  obtain ⟨K₀, hK₀, hK₀n⟩ := exists_compact_mem_nhds (1 : (A E)ˣ)
  refine ⟨interior (K₀ ∩ (U₁ ∩ U₂)), K₀, isOpen_interior,
    mem_interior_iff_mem_nhds.2 (inter_mem hK₀n (inter_mem hU₁ hU₂)), hK₀,
    interior_subset.trans Set.inter_subset_left, ?_⟩
  intro x hx y hy
  exact hUU (Set.mk_mem_prod (interior_subset hx).2.1 (interior_subset hy).2.2)

/- English proof (translation)
Take `⟨V, hV, h1, hs⟩` from `exists_V (E := E)`. Establish `hU : dM ⁻¹' V ∈ 𝓝 (1 : (A E)ˣ)` using `(hV.preimage continuous_dM').mem_nhds (by show dM 1 ∈ V; rw [M.dM_one]; exact h1)`. Take `⟨W, K₀, hW, h1W, hK, hWK, hWW⟩` from `exists_U hU`. Use `⟨W, K₀, hW, h1W, hK, hWK, fun x hx y hy e he => ?_⟩` and prove the remaining obligations. Establish `hm : dM (IdeleGroup.diagonal E e) ∈ V` using `by rw [he]; exact hWW x hx y hy`.

Establish `h2` using `hs e hm`. Establish `h3 : IdeleGroup.diagonal E e = 1`. Rewrite using `[← dt_dM (IdeleGroup.diagonal E e), h2]`. Conclude with `map_one (GroundTheory.Automorphic.AdelicGLn.det E 2)`. Establish `h4` using `congrArg (Units.val) h3`.

Rewrite `h4` using `[IdeleGroup.coe_diagonal]`. Use `Units.ext (AdeleRing.algebraMap_injective (𝓞 E) E ?_)` and prove the remaining obligations. Simplify using `using h4`.
-/
private theorem exists_sep : ∃ W K₀ : Set (A E)ˣ, IsOpen W ∧ (1 : (A E)ˣ) ∈ W ∧ IsCompact K₀ ∧ W ⊆ K₀ ∧
    ∀ x ∈ W, ∀ y ∈ W, ∀ e : Eˣ, IdeleGroup.diagonal E e = x * y⁻¹ → e = 1 := by
  obtain ⟨V, hV, h1, hs⟩ := exists_V (E := E)
  have hU : dM ⁻¹' V ∈ 𝓝 (1 : (A E)ˣ) :=
    (hV.preimage continuous_dM').mem_nhds (by show dM 1 ∈ V; rw [M.dM_one]; exact h1)
  obtain ⟨W, K₀, hW, h1W, hK, hWK, hWW⟩ := exists_U hU
  refine ⟨W, K₀, hW, h1W, hK, hWK, fun x hx y hy e he => ?_⟩
  have hm : dM (IdeleGroup.diagonal E e) ∈ V := by rw [he]; exact hWW x hx y hy
  have h2 := hs e hm
  have h3 : IdeleGroup.diagonal E e = 1 := by
    rw [← dt_dM (IdeleGroup.diagonal E e), h2]
    exact map_one (GroundTheory.Automorphic.AdelicGLn.det E 2)
  have h4 := congrArg (Units.val) h3
  rw [IdeleGroup.coe_diagonal] at h4
  refine Units.ext (AdeleRing.algebraMap_injective (𝓞 E) E ?_)
  simpa using h4

private abbrev NG (E : Type) [Field E] [NumberField E] : Type := GroundTheory.Automorphic.Reduction.normOneGL E 2

/- English proof (translation)
Rewrite using `[GroundTheory.Automorphic.Reduction.mem_normOneGL]`. Use `show ((IdeleGroup.ideleModule E (dt (gl h)) : {r : ℝ // 0 < r}) : ℝ) = 1`. Rewrite using `[dt_gl, map_one]`. Both sides reduce to the same expression.
-/
private theorem gl_mem (h : G1 E) : gl h ∈ GroundTheory.Automorphic.Reduction.normOneGL E 2 := by
  rw [GroundTheory.Automorphic.Reduction.mem_normOneGL]
  show ((IdeleGroup.ideleModule E (dt (gl h)) : {r : ℝ // 0 < r}) : ℝ) = 1
  rw [dt_gl, map_one]
  rfl

private def glN (h : G1 E) : NG E := ⟨gl h, gl_mem h⟩

private def prN (g : NG E) : G1 E := pr g.1

private def dN (g : NG E) : (A E)ˣ := dt g.1

/- English proof (translation)
The claim follows from `continuous_pr.comp continuous_subtype_val`.
-/
private theorem continuous_prN : Continuous (prN : NG E → G1 E) := continuous_pr.comp continuous_subtype_val
/- English proof (translation)
The claim follows from `continuous_dt.comp continuous_subtype_val`.
-/
private theorem continuous_dN : Continuous (dN : NG E → (A E)ˣ) := continuous_dt.comp continuous_subtype_val

/- English proof (translation)
The claim follows from `pr_gl_mul h g.1`.
-/
private theorem prN_glN_mul (h : G1 E) (g : NG E) : prN (glN h * g) = h * prN g := pr_gl_mul h g.1
/- English proof (translation)
Use `show dt (gl h * g.1) = dt g.1`. Rewrite using `[dt_mul, dt_gl, one_mul]`.
-/
private theorem dN_glN_mul (h : G1 E) (g : NG E) : dN (glN h * g) = dN g := by
  show dt (gl h * g.1) = dt g.1
  rw [dt_mul, dt_gl, one_mul]

private def pm (W : Set (A E)ˣ) : Measure (G1 E) :=
  ((Measure.haar : Measure (NG E)).restrict (dN ⁻¹' W)).map prN

/- English proof (translation)
Rewrite using `[pm, Measure.map_apply continuous_prN.measurable hB]`. Conclude with `Measure.restrict_apply (continuous_prN.measurable hB)`.
-/
private theorem pm_apply {W : Set (A E)ˣ} {B : Set (G1 E)} (hB : MeasurableSet B) :
    pm W B = (Measure.haar : Measure (NG E)) (prN ⁻¹' B ∩ dN ⁻¹' W) := by
  rw [pm, Measure.map_apply continuous_prN.measurable hB]
  exact Measure.restrict_apply (continuous_prN.measurable hB)

/- English proof (translation)
Use `⟨fun h => Measure.ext fun B hB => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply (measurable_const_mul h) hB, pm_apply hB, pm_apply (measurable_const_mul h hB)]`. Establish `e : (glN h * ·) ⁻¹' (prN ⁻¹' B ∩ dN ⁻¹' W) = prN ⁻¹' ((h * ·) ⁻¹' B) ∩ dN ⁻¹' W`. Use extensionality with `g`. Simplify using `only [Set.mem_preimage, Set.mem_inter_iff, prN_glN_mul, dN_glN_mul]`.

Rewrite using `[← e]`. Conclude with `measure_preimage_mul (Measure.haar : Measure (NG E)) (glN h) _`.
-/
private theorem pm_left {W : Set (A E)ˣ} (hW : IsOpen W) : (pm W).IsMulLeftInvariant := by
  refine ⟨fun h => Measure.ext fun B hB => ?_⟩
  rw [Measure.map_apply (measurable_const_mul h) hB, pm_apply hB, pm_apply (measurable_const_mul h hB)]
  have e : (glN h * ·) ⁻¹' (prN ⁻¹' B ∩ dN ⁻¹' W) = prN ⁻¹' ((h * ·) ⁻¹' B) ∩ dN ⁻¹' W := by
    ext g
    simp only [Set.mem_preimage, Set.mem_inter_iff, prN_glN_mul, dN_glN_mul]
  rw [← e]
  exact measure_preimage_mul (Measure.haar : Measure (NG E)) (glN h) _

/- English proof (translation)
Use `⟨fun K hKc => ?_⟩` and prove the remaining obligations. Rewrite using `[pm_apply hKc.measurableSet]`. Establish `hQ : IsCompact ((gl '' K) * (dM '' K₀) : Set (GL (Fin 2) (A E)))` using `(hKc.image M.continuous_gl).mul (hK.image continuous_dM')`. Establish `hC : IsCompact (Subtype.val ⁻¹' ((gl '' K) * (dM '' K₀)) : Set (NG E))` using `GroundTheory.Automorphic.Reduction.isClosed_normOneGL.isClosedEmbedding_subtypeVal.isCompact_preimage hQ`. Use `(measure_mono ?_).trans_lt hC.measure_lt_top` and prove the remaining obligations.

Introduce and unpack `g ⟨hg1, hg2⟩`. Conclude with `⟨_, ⟨_, hg1, rfl⟩, _, ⟨_, hWK hg2, rfl⟩, gl_pr_mul g.1⟩`.
-/
private theorem pm_fin {W K₀ : Set (A E)ˣ} (hK : IsCompact K₀) (hWK : W ⊆ K₀) :
    IsFiniteMeasureOnCompacts (pm W) := by
  refine ⟨fun K hKc => ?_⟩
  rw [pm_apply hKc.measurableSet]
  have hQ : IsCompact ((gl '' K) * (dM '' K₀) : Set (GL (Fin 2) (A E))) :=
    (hKc.image M.continuous_gl).mul (hK.image continuous_dM')
  have hC : IsCompact (Subtype.val ⁻¹' ((gl '' K) * (dM '' K₀)) : Set (NG E)) :=
    GroundTheory.Automorphic.Reduction.isClosed_normOneGL.isClosedEmbedding_subtypeVal.isCompact_preimage hQ
  refine (measure_mono ?_).trans_lt hC.measure_lt_top
  rintro g ⟨hg1, hg2⟩
  exact ⟨_, ⟨_, hg1, rfl⟩, _, ⟨_, hWK hg2, rfl⟩, gl_pr_mul g.1⟩

/- English proof (translation)
Introduce `h0`. Establish `e` using `pm_apply (W := W) (B := Set.univ) MeasurableSet.univ`. Rewrite `e` using `[h0, Set.preimage_univ, Set.univ_inter]`. Establish `hpos` using `(hW.preimage continuous_dN).measure_pos (Measure.haar : Measure (NG E)) ⟨1, by show dt (1 : GL (Fin 2) (A E)) ∈ W; rw [show dt (1 : GL (Fin 2) (A E)) = 1 from map_one (GroundTheory.Automorphic.AdelicGLn.det E 2)]; exact h1⟩`. Rewrite `hpos` using `[← e]`.

Simplify using `at hpos`.
-/
private theorem pm_ne {W : Set (A E)ˣ} (hW : IsOpen W) (h1 : (1 : (A E)ˣ) ∈ W) : pm W ≠ 0 := by
  intro h0
  have e := pm_apply (W := W) (B := Set.univ) MeasurableSet.univ
  rw [h0, Set.preimage_univ, Set.univ_inter] at e
  have hpos := (hW.preimage continuous_dN).measure_pos (Measure.haar : Measure (NG E))
    ⟨1, by show dt (1 : GL (Fin 2) (A E)) ∈ W; rw [show dt (1 : GL (Fin 2) (A E)) = 1 from map_one (GroundTheory.Automorphic.AdelicGLn.det E 2)]; exact h1⟩
  rw [← e] at hpos
  simp at hpos

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use `show (s₀.1).map (algebraMap E (A E)) = (algebraMap E (A E)).mapMatrix γ₀.val`. Rewrite using `[hs]`. Both sides reduce to the same expression.
-/
private theorem glN_ratS (s₀ : Matrix.SpecialLinearGroup (Fin 2) E) (γ₀ : GL (Fin 2) E) (hs : s₀.1 = γ₀.val) :
    gl (ratS E s₀) = GroundTheory.Automorphic.AdelicGLn.diagonal E 2 γ₀ := by
  refine Units.ext ?_
  show (s₀.1).map (algebraMap E (A E)) = (algebraMap E (A E)).mapMatrix γ₀.val
  rw [hs]
  rfl

/- English proof (translation)
Take `⟨γ₀, hγ₀⟩` from `η.2`. Establish `hηv : ((η : NG E) : GL (Fin 2) (A E)) = GroundTheory.Automorphic.AdelicGLn.diagonal E 2 γ₀` using `hγ₀.symm`. Distinguish the cases in `he : Matrix.GeneralLinearGroup.det γ₀ = 1`. Establish `hd : γ₀.val.det = 1` using `congrArg Units.val he`. Set `s₀ : Matrix.SpecialLinearGroup (Fin 2) E` to `⟨γ₀.val, hd⟩`.

Establish `hgl : gl (ratS E s₀) = GroundTheory.Automorphic.AdelicGLn.diagonal E 2 γ₀` using `glN_ratS s₀ γ₀ rfl`. Set `sG : Gam E` to `⟨ratS E s₀, s₀, rfl⟩`. Establish `hsN : glN (sG : G1 E) = (η : NG E)` using `Subtype.ext (hgl.trans hηv.symm)`. Establish `hs1 : sG ≠ 1`. Introduce `h`.

Apply `hη` to reduce the goal to its premises. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[← hsN, h]`. Conclude with `Subtype.ext (map_one (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := A E)))`. Establish `hz : N.μ ((sG • N.D) ∩ (1 : Gam E) • N.D) = 0` using `N.fund.aedisjoint hs1`.

Rewrite `hz` using `[one_smul]`. Establish `hB : MeasurableSet ((sG • N.D) ∩ N.D)` using `(N.meas.const_smul sG).inter N.meas`. Establish `hp : pm W ((sG • N.D) ∩ N.D) = 0`. Rewrite using `[hc]`. Simplify using `[hz]`.

Rewrite `hp` using `[pm_apply hB]`. Use `measure_mono_null ?_ hp` and prove the remaining obligations. Introduce and unpack `x ⟨⟨a, ⟨ha1, -⟩, rfl⟩, hx1, hx2⟩`. Use `⟨⟨?_, hx1⟩, hx2⟩` and prove the remaining obligations. Use `⟨prN a, ha1, ?_⟩` and prove the remaining obligations.

Use `show (sG : G1 E) * prN a = prN ((η : NG E) * a)`. Rewrite using `[← hsN, prN_glN_mul]`. Establish `: η • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ (prN ⁻¹' N.D ∩ dN ⁻¹' W) = ∅`. Use `Set.eq_empty_of_forall_notMem ?_` and prove the remaining obligations. Introduce and unpack `x ⟨⟨a, ⟨-, ha2⟩, rfl⟩, -, hx2⟩`.

Apply `he` to reduce the goal to its premises. Use `hsep _ hx2 _ ha2 _ ?_` and prove the remaining obligations. Use `show IdeleGroup.diagonal E _ = dt (((η : NG E) * a).1) * (dt a.1)⁻¹`. Establish `: dt (((η : NG E) * a).1) = dt (η : NG E).1 * dt a.1` using `dt_mul _ _`. Rewrite using `[this, mul_inv_cancel_right, hηv, dt_diag]`.

Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
private theorem null_of_disj {W : Set (A E)ˣ} (N : MeasE E) (c : NNReal) (hc : pm W = c • N.μ)
    (η : GroundTheory.Automorphic.Reduction.rationalGLOne E 2) (hη : η ≠ 1)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, ∀ e : Eˣ, IdeleGroup.diagonal E e = x * y⁻¹ → e = 1) :
    (Measure.haar : Measure (NG E)) (η • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ (prN ⁻¹' N.D ∩ dN ⁻¹' W)) = 0 := by
  obtain ⟨γ₀, hγ₀⟩ := η.2
  have hηv : ((η : NG E) : GL (Fin 2) (A E)) = GroundTheory.Automorphic.AdelicGLn.diagonal E 2 γ₀ := hγ₀.symm
  by_cases he : Matrix.GeneralLinearGroup.det γ₀ = 1
  · have hd : γ₀.val.det = 1 := congrArg Units.val he
    let s₀ : Matrix.SpecialLinearGroup (Fin 2) E := ⟨γ₀.val, hd⟩
    have hgl : gl (ratS E s₀) = GroundTheory.Automorphic.AdelicGLn.diagonal E 2 γ₀ := glN_ratS s₀ γ₀ rfl
    let sG : Gam E := ⟨ratS E s₀, s₀, rfl⟩
    have hsN : glN (sG : G1 E) = (η : NG E) := Subtype.ext (hgl.trans hηv.symm)
    have hs1 : sG ≠ 1 := by
      intro h
      apply hη
      refine Subtype.ext ?_
      rw [← hsN, h]
      exact Subtype.ext (map_one (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := A E)))
    have hz : N.μ ((sG • N.D) ∩ (1 : Gam E) • N.D) = 0 := N.fund.aedisjoint hs1
    rw [one_smul] at hz
    have hB : MeasurableSet ((sG • N.D) ∩ N.D) := (N.meas.const_smul sG).inter N.meas
    have hp : pm W ((sG • N.D) ∩ N.D) = 0 := by
      rw [hc]
      simp [hz]
    rw [pm_apply hB] at hp
    refine measure_mono_null ?_ hp
    rintro x ⟨⟨a, ⟨ha1, -⟩, rfl⟩, hx1, hx2⟩
    refine ⟨⟨?_, hx1⟩, hx2⟩
    refine ⟨prN a, ha1, ?_⟩
    show (sG : G1 E) * prN a = prN ((η : NG E) * a)
    rw [← hsN, prN_glN_mul]
  · have : η • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ (prN ⁻¹' N.D ∩ dN ⁻¹' W) = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro x ⟨⟨a, ⟨-, ha2⟩, rfl⟩, -, hx2⟩
      apply he
      refine hsep _ hx2 _ ha2 _ ?_
      show IdeleGroup.diagonal E _ = dt (((η : NG E) * a).1) * (dt a.1)⁻¹
      have : dt (((η : NG E) * a).1) = dt (η : NG E).1 * dt a.1 := dt_mul _ _
      rw [this, mul_inv_cancel_right, hηv, dt_diag]
    rw [this]
    simp

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ N`. Take `⟨W, K₀, hW, h1, hK, hWK, hsep⟩` from `exists_sep (E := E)`. Use `haveI := N.haar`. Use `haveI := pm_left hW`. Use `haveI := pm_fin hK hWK`.

Take `⟨c, hc⟩ : ∃ c : NNReal, pm W = c • N.μ` from `⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩`. Establish `hc0 : c ≠ 0`. Introduce `h`. Apply `pm_ne hW h1` to reduce the goal to its premises. Rewrite using `[hc, h, zero_smul]`.

Use `set μG : Measure (NG E) := Measure.haar with hμG`. Establish `hF` using `GroundTheory.Automorphic.RightCosetSpace.isFundamentalDomain_fundamentalDomain (GroundTheory.Automorphic.Reduction.rationalGLOne E 2) μG`. Establish `hFin : μG (GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (GroundTheory.Automorphic.Reduction.rationalGLOne E 2)) < ⊤` using `by haveI := GroundTheory.Automorphic.Reduction.isFiniteMeasure_quotientMeasure μG`. Rewrite using `[← GroundTheory.Automorphic.RightCosetSpace.quotientMeasure_univ μG hF]`. Conclude with `measure_lt_top _ _`.

Establish `hSm : MeasurableSet (prN ⁻¹' N.D ∩ dN ⁻¹' W)` using `(continuous_prN.measurable N.meas).inter (hW.preimage continuous_dN).measurableSet`. Establish `hS : μG (prN ⁻¹' N.D ∩ dN ⁻¹' W) = c * N.μ N.D`. Rewrite using `[← pm_apply N.meas, hc]`. Both sides reduce to the same expression. Use `haveI h₀ : SMulInvariantMeasure (NG E) (NG E) μG := ⟨fun a s _ => measure_preimage_mul μG a s⟩`.

Use `haveI h₁ : SMulInvariantMeasure (GroundTheory.Automorphic.Reduction.rationalGLOne E 2) (NG E) μG := Subgroup.smulInvariantMeasure _`. Establish `hpair : Pairwise (Function.onFun (AEDisjoint μG) fun g : GroundTheory.Automorphic.Reduction.rationalGLOne E 2 => g • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (GroundTheory.Automorphic.Reduction.rationalGLOne E 2))`. Introduce `γ γ' hne`. Use `AEDisjoint.mono ?_ Set.inter_subset_left Set.inter_subset_left` and prove the remaining obligations. Use `show μG (γ • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ γ' • (prN ⁻¹' N.D ∩ dN ⁻¹' W)) = 0`.

Establish `e : γ • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ γ' • (prN ⁻¹' N.D ∩ dN ⁻¹' W) = γ' • ((γ'⁻¹ * γ) • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ (prN ⁻¹' N.D ∩ dN ⁻¹' W))` using `by conv_rhs => rw [Set.smul_set_inter, smul_smul, mul_inv_cancel_left]`. Rewrite using `[e, measure_smul]`. Conclude with `null_of_disj N c hc _ (fun h => hne (by rw [inv_mul_eq_one] at h; exact h.symm)) hsep`. Establish `hle` using `hF.measure_le_of_pairwise_disjoint hSm.nullMeasurableSet hpair`. Establish `hlt : (c : ENNReal) * N.μ N.D < ⊤` using `hS ▸ hle.trans_lt hFin`.

Assume the negation of the conclusion as `htop`. Rewrite `htop` using `[not_lt, top_le_iff]`. Rewrite `hlt` using `[htop, ENNReal.mul_top (by exact_mod_cast hc0)]`. Conclude with `lt_irrefl _ hlt`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.volE :
    VolE := by
  intro E _ _ N
  obtain ⟨W, K₀, hW, h1, hK, hWK, hsep⟩ := exists_sep (E := E)
  haveI := N.haar
  haveI := pm_left hW
  haveI := pm_fin hK hWK
  obtain ⟨c, hc⟩ : ∃ c : NNReal, pm W = c • N.μ := ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hc0 : c ≠ 0 := by
    intro h
    apply pm_ne hW h1
    rw [hc, h, zero_smul]
  set μG : Measure (NG E) := Measure.haar with hμG
  have hF := GroundTheory.Automorphic.RightCosetSpace.isFundamentalDomain_fundamentalDomain
    (GroundTheory.Automorphic.Reduction.rationalGLOne E 2) μG
  have hFin : μG (GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (GroundTheory.Automorphic.Reduction.rationalGLOne E 2)) < ⊤ := by
    haveI := GroundTheory.Automorphic.Reduction.isFiniteMeasure_quotientMeasure μG
    rw [← GroundTheory.Automorphic.RightCosetSpace.quotientMeasure_univ μG hF]
    exact measure_lt_top _ _
  have hSm : MeasurableSet (prN ⁻¹' N.D ∩ dN ⁻¹' W) :=
    (continuous_prN.measurable N.meas).inter (hW.preimage continuous_dN).measurableSet
  have hS : μG (prN ⁻¹' N.D ∩ dN ⁻¹' W) = c * N.μ N.D := by
    rw [← pm_apply N.meas, hc]
    rfl
  haveI h₀ : SMulInvariantMeasure (NG E) (NG E) μG := ⟨fun a s _ => measure_preimage_mul μG a s⟩
  haveI h₁ : SMulInvariantMeasure (GroundTheory.Automorphic.Reduction.rationalGLOne E 2) (NG E) μG :=
    Subgroup.smulInvariantMeasure _
  have hpair : Pairwise (Function.onFun (AEDisjoint μG) fun g : GroundTheory.Automorphic.Reduction.rationalGLOne E 2 =>
      g • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (GroundTheory.Automorphic.Reduction.rationalGLOne E 2)) := by
    intro γ γ' hne
    refine AEDisjoint.mono ?_ Set.inter_subset_left Set.inter_subset_left
    show μG (γ • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ γ' • (prN ⁻¹' N.D ∩ dN ⁻¹' W)) = 0
    have e : γ • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ γ' • (prN ⁻¹' N.D ∩ dN ⁻¹' W) =
        γ' • ((γ'⁻¹ * γ) • (prN ⁻¹' N.D ∩ dN ⁻¹' W) ∩ (prN ⁻¹' N.D ∩ dN ⁻¹' W)) := by
      conv_rhs => rw [Set.smul_set_inter, smul_smul, mul_inv_cancel_left]
    rw [e, measure_smul]
    exact null_of_disj N c hc _ (fun h => hne (by rw [inv_mul_eq_one] at h; exact h.symm)) hsep
  have hle := hF.measure_le_of_pairwise_disjoint hSm.nullMeasurableSet hpair
  have hlt : (c : ENNReal) * N.μ N.D < ⊤ := hS ▸ hle.trans_lt hFin
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop, ENNReal.mul_top (by exact_mod_cast hc0)] at hlt
  exact lt_irrefl _ hlt
