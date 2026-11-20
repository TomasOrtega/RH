import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspCentral
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Establish `h` using `infEmb_infPart_mul_finEmb_finPart (g : AdelicGLn.AdelicGL K n)`. Rewrite `h` using `[hg, map_one, mul_one]`. Rewrite using `[← retract_infEmb, h]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_retractOne, mem_normOneGL_iff_detModule.1 g.2, map_one, inv_one, mul_one]`.
-/
private theorem archP_inf {K : Type} [Field K] [NumberField K] {n : ℕ} (g : normOneGL K n)
    (hg : CuspidalSpectrum.finPart K n (g : AdelicGLn.AdelicGL K n) = 1) :
    archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) = g := by
  have h := infEmb_infPart_mul_finEmb_finPart (g : AdelicGLn.AdelicGL K n)
  rw [hg, map_one, mul_one] at h
  rw [← retract_infEmb, h]
  apply Subtype.ext
  rw [coe_retractOne, mem_normOneGL_iff_detModule.1 g.2, map_one, inv_one, mul_one]

/- English proof (translation)
Establish `hz : ∀ s : ℝ, ((zt K s : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = Matrix.diagonal fun _ => (posIdele (K` using `K) (Real.exp (s * UnitaryAdmissible.centralExp K 2)) (Real.exp_pos _) : AdeleRing (𝓞 K) K) := by`. Introduce `s`. Rewrite using `[zt, centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits, posIdeleHom_apply]`. Use `congr 1`. Use function extensionality and compare the values at `_`.

Use `congr 2`. Conclude with `(Real.exp_mul _ _).symm`. Rewrite using `[blkLaws.1]`. Simplify using `only [OneMemClass.coe_one, one_mul]`. Express the relevant statement in the definitionally equal form `Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (zt K t).val 0 0 (zt K (-t)).val) = _`.

Rewrite using `[hz, hz, Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply]`. Break down `finSumFinEquiv.symm i with j | j` into its components or cases.

Both sides reduce to the same expression. Simplify using `only [Sum.elim_inr, neg_mul, mul_neg]`.
-/
private theorem lv_diag {K : Type} [Field K] [NumberField K] (t : ℝ) :
    (((lv (1 : G1 K 2) 1 t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) (AdeleRing (𝓞 K) K)) =
      Matrix.diagonal fun i => (posIdele (K := K) (Real.exp (t * (Sum.elim (fun _ => UnitaryAdmissible.centralExp K 2)
        (fun _ => -UnitaryAdmissible.centralExp K 2) (finSumFinEquiv.symm i)))) (Real.exp_pos _) : AdeleRing (𝓞 K) K) := by
  have hz : ∀ s : ℝ, ((zt K s : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.diagonal fun _ => (posIdele (K := K) (Real.exp (s * UnitaryAdmissible.centralExp K 2)) (Real.exp_pos _) :
        AdeleRing (𝓞 K) K) := by
    intro s
    rw [zt, centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits, posIdeleHom_apply]
    congr 1
    funext _
    congr 2
    exact (Real.exp_mul _ _).symm
  rw [blkLaws.1]
  simp only [OneMemClass.coe_one, one_mul]
  change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (zt K t).val 0 0 (zt K (-t)).val) = _
  rw [hz, hz, Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rcases finSumFinEquiv.symm i with j | j
  · rfl
  · simp only [Sum.elim_inr, neg_mul, mul_neg]

/- English proof (translation)
Use `set e : Fin (2 + 2) → ℝ := fun i => Sum.elim (fun _ => UnitaryAdmissible.centralExp K 2) (fun _ => -UnitaryAdmissible.centralExp K 2) (finSumFinEquiv.symm i) with he`. Use `⟨⟨(Matrix.diagonal fun i => algebraMap ℝ (mixedEmbedding.mixedSpace K) (e i) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) (mixedEmbedding.mixedSpace K)), Submodule.mem_top⟩, fun t => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((((lv (1 : G1 K 2) 1 t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) (AdeleRing (𝓞 K) K)) i j).2 = _`.

Rewrite using `[lv_diag, Units.val_one]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Matrix.one_apply_eq]`. Use extensionality with `v`.

Conclude with `congrArg _ (posIdele_finite _ _ v)`. Rewrite using `[Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]`. Both sides reduce to the same expression. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[IsExpLieAlgebra.coe_expG]`. Express the relevant statement in the definitionally equal form `archMat K (2 + 2) (((lv (1 : G1 K 2) 1 t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) (AdeleRing (𝓞 K) K)) = NormedSpace.exp (t • (Matrix.diagonal fun i => algebraMap ℝ (mixedEmbedding.mixedSpace K) (e i) : Matrix (Fin (2 + 2)) (Fin (2 + 2) …`. Rewrite using `[lv_diag, ← Matrix.diagonal_smul, Matrix.exp_diagonal]`. Use `(archMat_diagonal _).trans ?_` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[UnitaryAdmissible.ringEquiv_posIdele, Pi.coe_exp, Pi.smul_apply, Algebra.smul_def, ← map_mul, ← NormedSpace.algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ]`.
-/
private theorem lv_exp {K : Type} [Field K] [NumberField K] : ∃ Y : archLie K (2 + 2), ∀ t : ℝ,
    CuspidalSpectrum.finPart K (2 + 2) (lv (1 : G1 K 2) 1 t : G1 K (2 + 2)) = 1 ∧
    infPart K (2 + 2) (lv (1 : G1 K 2) 1 t : G1 K (2 + 2)) = (isExpLieAlgebra K (2 + 2)).expG (t • Y) := by
  classical
  set e : Fin (2 + 2) → ℝ := fun i => Sum.elim (fun _ => UnitaryAdmissible.centralExp K 2)
        (fun _ => -UnitaryAdmissible.centralExp K 2) (finSumFinEquiv.symm i) with he
  refine ⟨⟨(Matrix.diagonal fun i => algebraMap ℝ (mixedEmbedding.mixedSpace K) (e i) :
    Matrix (Fin (2 + 2)) (Fin (2 + 2)) (mixedEmbedding.mixedSpace K)), Submodule.mem_top⟩, fun t => ⟨?_, ?_⟩⟩
  · apply Units.ext
    refine Matrix.ext fun i j => ?_
    change ((((lv (1 : G1 K 2) 1 t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) :
      Matrix (Fin (2 + 2)) (Fin (2 + 2)) (AdeleRing (𝓞 K) K)) i j).2 = _
    rw [lv_diag, Units.val_one]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      ext v
      exact congrArg _ (posIdele_finite _ _ v)
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rfl
  · apply Subtype.ext
    apply Units.ext
    rw [IsExpLieAlgebra.coe_expG]
    change archMat K (2 + 2) (((lv (1 : G1 K 2) 1 t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) :
      Matrix (Fin (2 + 2)) (Fin (2 + 2)) (AdeleRing (𝓞 K) K)) =
      NormedSpace.exp (t • (Matrix.diagonal fun i => algebraMap ℝ (mixedEmbedding.mixedSpace K) (e i) :
        Matrix (Fin (2 + 2)) (Fin (2 + 2)) (mixedEmbedding.mixedSpace K)))
    rw [lv_diag, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
    refine (archMat_diagonal _).trans ?_
    congr 1
    funext i
    rw [UnitaryAdmissible.ringEquiv_posIdele, Pi.coe_exp, Pi.smul_apply, Algebra.smul_def, ← map_mul,
      ← NormedSpace.algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ]

/- English proof (translation)
Take `⟨Y, hY⟩` from `lv_exp (K := K)`. Use `⟨(isExpLieAlgebra K (2 + 2)).Ad (infPart K (2 + 2) x)⁻¹ Y, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← archP_inf (x⁻¹ * lv (1 : G1 K 2) 1 t * x), ← map_smul, IsExpLieAlgebra.expG_Ad, ← (hY t).2]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, inv_inv]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, (hY t).1, mul_one, inv_mul_cancel]`.
-/
private theorem conj_exp {K : Type} [Field K] [NumberField K] (x : G1 K (2 + 2)) : ∃ Y : archLie K (2 + 2), ∀ t : ℝ,
    x⁻¹ * lv (1 : G1 K 2) 1 t * x = archP K (2 + 2) ((isExpLieAlgebra K (2 + 2)).expG (t • Y)) := by
  obtain ⟨Y, hY⟩ := lv_exp (K := K)
  refine ⟨(isExpLieAlgebra K (2 + 2)).Ad (infPart K (2 + 2) x)⁻¹ Y, fun t => ?_⟩
  rw [← archP_inf (x⁻¹ * lv (1 : G1 K 2) 1 t * x), ← map_smul, IsExpLieAlgebra.expG_Ad, ← (hY t).2]
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, inv_inv]
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, (hY t).1, mul_one, inv_mul_cancel]

/- English proof (translation)
Use `set h := isExpLieAlgebra K n`. Establish `hi : h.IsSmoothFun fun B => f B⁻¹`. Use `letI := h.chartedSpace`. Use `haveI := h.lieGroup ((⊤ : ℕ∞) : WithTop ℕ∞)`. Conclude with `ContMDiff.comp (I' := modelWithCornersSelf ℝ (archLie K n)) hf (contMDiff_inv _ _)`.

Establish `hc : Continuous (h.rightDeriv (-Y) fun B => f B⁻¹)`. Use `letI := h.chartedSpace`. Conclude with `ContMDiff.continuous (h.isSmoothFun_rightDeriv hi (-Y))`. Use `⟨fun A => h.rightDeriv (-Y) (fun B => f B⁻¹) A⁻¹, hc.comp continuous_inv, fun A => ?_⟩` and prove the remaining obligations. Establish `h1` using `h.hasDerivAt_rightDeriv hi (-Y) A⁻¹`.

Simplify `h1` using `only [smul_neg, IsExpLieAlgebra.expG_neg, mul_inv_rev, inv_inv]`.
-/
private theorem left_deriv {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) (Y : archLie K n) :
    ∃ E : archGroup K n → ℂ, Continuous E ∧
      ∀ A, HasDerivAt (fun t : ℝ => f ((isExpLieAlgebra K n).expG (t • Y) * A)) (E A) 0 := by
  set h := isExpLieAlgebra K n
  have hi : h.IsSmoothFun fun B => f B⁻¹ := by
    letI := h.chartedSpace
    haveI := h.lieGroup ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact ContMDiff.comp (I' := modelWithCornersSelf ℝ (archLie K n)) hf (contMDiff_inv _ _)
  have hc : Continuous (h.rightDeriv (-Y) fun B => f B⁻¹) := by
    letI := h.chartedSpace
    exact ContMDiff.continuous (h.isSmoothFun_rightDeriv hi (-Y))
  refine ⟨fun A => h.rightDeriv (-Y) (fun B => f B⁻¹) A⁻¹, hc.comp continuous_inv, fun A => ?_⟩
  have h1 := h.hasDerivAt_rightDeriv hi (-Y) A⁻¹
  simpa only [smul_neg, IsExpLieAlgebra.expG_neg, mul_inv_rev, inv_inv] using h1

/- English proof (translation)
Take `⟨hs, U, hU, hinv⟩` from `ha`. Use `set c : ℝ → G1 K n := fun t => archP K n ((isExpLieAlgebra K n).expG (t • Y)) with hc`. Establish `c0 : c 0 = 1` using `by simp only [hc, zero_smul, IsExpLieAlgebra.expG_zero, map_one]`. Establish `cadd : ∀ s t, c (s + t) = c s * c t` using `fun s t => by`. Simplify using `only [hc]`.

Rewrite using `[← map_mul]`. Use `congr 1`. Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Simplify using `only [Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG, add_smul, Submodule.coe_add]`. Conclude with `exp_add_of_commute' ℝ (((Commute.refl (Y : ArchMatrix K n)).smul_left s).smul_right t)`.

Establish `ccont : Continuous c` using `continuous_archP.comp ((isExpLieAlgebra K n).continuous_expG.comp (continuous_id.smul continuous_const))`. Establish `key : ∀ x₀ : G1 K n, ∃ E : archGroup K n → ℂ, Continuous E ∧ ∀ A, HasDerivAt (fun t : ℝ => a (c t * (archP K n A * x₀))) (E A) 0` using `fun x₀ => by`. Take `⟨E, hE, hd⟩` from `left_deriv (hs x₀) Y`. Use `⟨E, hE, fun A => ?_⟩` and prove the remaining obligations. Simplify `hd A` using `only [map_mul, mul_assoc]`.

Use `set D : G1 K n → ℂ := fun g => deriv (fun t : ℝ => a (c t * g)) 0 with hD`. Establish `hder : ∀ g, HasDerivAt (fun t : ℝ => a (c t * g)) (D g) 0` using `fun g => by`. Take `⟨E, -, hd⟩` from `key g`. Establish `h1` using `hd 1`. Simplify using `only [map_one, one_mul] at h1`.

Conclude with `h1.differentiableAt.hasDerivAt`. Establish `Dcont : Continuous D`. Use `continuous_iff_continuousAt.2 fun x₀ => ?_` and prove the remaining obligations. Take `⟨E, hE, hd⟩` from `key x₀`. Establish `hq : Continuous fun g : G1 K n => ((g * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n)` using `continuous_subtype_val.comp (continuous_id.mul continuous_const)`.

Establish `hev : ∀ᶠ g in 𝓝 x₀, CuspidalSpectrum.finPart K n ((g * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) ∈ finOpenSubgroup U hU`. Use `(CuspidalSpectrum.continuous_finPart.comp hq).continuousAt.eventually_mem ((finOpenSubgroup U hU).isOpen.mem_nhds ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, mul_inv_cancel, OneMemClass.coe_one, map_one, SetLike.mem_coe]`. Conclude with `one_mem _`. Use `(hE.comp (continuous_infPart.comp hq)).continuousAt.congr (hev.mono fun g hg => ?_)` and prove the remaining obligations.

Take `⟨u, hu, hue⟩` from `Subgroup.mem_map.1 hg`. Use `set A := infPart K n ((g * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) with hA`. Establish `e1 : g * x₀⁻¹ = archP K n A * finOne K n u`. Rewrite using `[← retract_infEmb, ← retractOne_mul_finEmb _ u.2]`. Establish `e2 : infEmb K n A * finEmb K n u = ((g * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n)`.

Rewrite using `[← infEmb_infPart_mul_finEmb_finPart ((g * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n), ← hue]`. Both sides reduce to the same expression. Rewrite using `[e2]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_retractOne, mem_normOneGL_iff_detModule.1 (g * x₀⁻¹).2, map_one, inv_one, mul_one]`.

Establish `e3 : (fun t : ℝ => a (c t * g)) = fun t : ℝ => a (c t * (archP K n A * x₀))`. Use function extensionality and compare the values at `t`. Establish `e4 : c t * g = finOne K n u * (c t * (archP K n A * x₀))`. Establish `e5 : c t * finOne K n u = finOne K n u * c t` using `archimedeanProjection_mul_finiteEmbedding_comm _ u`. Rewrite using `[← mul_assoc, ← e5, mul_assoc, ← mul_assoc (finOne K n u), ← archimedeanProjection_mul_finiteEmbedding_comm, ← e1, inv_mul_cancel_right]`.

Rewrite using `[e4]`. Conclude with `hinv u hu _`. Express the relevant statement in the definitionally equal form `E A = deriv _ 0`. Rewrite using `[e3, (hd A).deriv]`. Establish `Dsupp : HasCompactSupport D`.

Use `HasCompactSupport.intro' (K := tsupport a) a.hasCompactSupport' (isClosed_tsupport _) fun g hg => ?_` and prove the remaining obligations. Establish `hev : ∀ᶠ t in 𝓝 (0 : ℝ), c t * g ∈ (tsupport a)ᶜ` using `(ccont.mul continuous_const).continuousAt.eventually_mem ((isClosed_tsupport _).isOpen_compl.mem_nhds (by simpa only [Pi.mul_apply, c0, one_mul, Set.mem_compl_iff] using hg))`. Establish `: (fun t : ℝ => a (c t * g)) =ᶠ[𝓝 0] fun _ => 0` using `hev.mono fun t ht => image_eq_zero_of_notMem_tsupport ht`. Express the relevant statement in the definitionally equal form `deriv _ 0 = 0`. Rewrite using `[this.deriv_eq, deriv_const]`.

Take `⟨L, hL⟩` from `Dcont.bounded_above_of_compact_support Dsupp`. Use `⟨L, fun t g => ?_⟩` and prove the remaining obligations. Establish `hall : ∀ s, HasDerivAt (fun t : ℝ => a (c t * g)) (D (c s * g)) s` using `fun s => by`. Establish `h1` using `hder (c s * g)`. Rewrite `h1` using `[← sub_self s]`.

Use `(h1.comp_sub_const s s).congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)` and prove the remaining obligations. Simplify using `only [← mul_assoc, ← cadd, sub_add_cancel]`. Establish `h2` using `Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := fun t : ℝ => a (c t * g)) (s := Set.univ) (C := L) (x := 0) (y := t) (fun s _ => (hall s).differentiableAt) (fun s _ => by rw [(hall s).deriv]; exact hL _) convex_univ trivial trivial`. Simplify `h2` using `only [c0, one_mul, sub_zero, Real.norm_eq_abs]`.
-/
private theorem lip {K : Type} [Field K] [NumberField K] {n : ℕ} (a : CC K n) (ha : IsLeftSmooth a) (Y : archLie K n) :
    ∃ L : ℝ, ∀ (t : ℝ) (g : G1 K n), ‖a (archP K n ((isExpLieAlgebra K n).expG (t • Y)) * g) - a g‖ ≤ L * |t| := by
  obtain ⟨hs, U, hU, hinv⟩ := ha
  set c : ℝ → G1 K n := fun t => archP K n ((isExpLieAlgebra K n).expG (t • Y)) with hc
  have c0 : c 0 = 1 := by simp only [hc, zero_smul, IsExpLieAlgebra.expG_zero, map_one]
  have cadd : ∀ s t, c (s + t) = c s * c t := fun s t => by
    simp only [hc]
    rw [← map_mul]
    congr 1
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG, add_smul, Submodule.coe_add]
    exact exp_add_of_commute' ℝ (((Commute.refl (Y : ArchMatrix K n)).smul_left s).smul_right t)
  have ccont : Continuous c :=
    continuous_archP.comp ((isExpLieAlgebra K n).continuous_expG.comp (continuous_id.smul continuous_const))
  have key : ∀ x₀ : G1 K n, ∃ E : archGroup K n → ℂ, Continuous E ∧
      ∀ A, HasDerivAt (fun t : ℝ => a (c t * (archP K n A * x₀))) (E A) 0 := fun x₀ => by
    obtain ⟨E, hE, hd⟩ := left_deriv (hs x₀) Y
    refine ⟨E, hE, fun A => ?_⟩
    simpa only [map_mul, mul_assoc] using hd A
  set D : G1 K n → ℂ := fun g => deriv (fun t : ℝ => a (c t * g)) 0 with hD
  have hder : ∀ g, HasDerivAt (fun t : ℝ => a (c t * g)) (D g) 0 := fun g => by
    obtain ⟨E, -, hd⟩ := key g
    have h1 := hd 1
    simp only [map_one, one_mul] at h1
    exact h1.differentiableAt.hasDerivAt
  have Dcont : Continuous D := by
    refine continuous_iff_continuousAt.2 fun x₀ => ?_
    obtain ⟨E, hE, hd⟩ := key x₀
    have hq : Continuous fun g : G1 K n => ((g * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) :=
      continuous_subtype_val.comp (continuous_id.mul continuous_const)
    have hev : ∀ᶠ g in 𝓝 x₀, CuspidalSpectrum.finPart K n ((g * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) ∈
        finOpenSubgroup U hU := by
      refine (CuspidalSpectrum.continuous_finPart.comp hq).continuousAt.eventually_mem
        ((finOpenSubgroup U hU).isOpen.mem_nhds ?_)
      simp only [Function.comp_apply, mul_inv_cancel, OneMemClass.coe_one, map_one, SetLike.mem_coe]
      exact one_mem _
    refine (hE.comp (continuous_infPart.comp hq)).continuousAt.congr (hev.mono fun g hg => ?_)
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hg
    set A := infPart K n ((g * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) with hA
    have e1 : g * x₀⁻¹ = archP K n A * finOne K n u := by
      rw [← retract_infEmb, ← retractOne_mul_finEmb _ u.2]
      have e2 : infEmb K n A * finEmb K n u = ((g * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) := by
        rw [← infEmb_infPart_mul_finEmb_finPart ((g * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n), ← hue]
        rfl
      rw [e2]
      apply Subtype.ext
      rw [coe_retractOne, mem_normOneGL_iff_detModule.1 (g * x₀⁻¹).2, map_one, inv_one, mul_one]
    have e3 : (fun t : ℝ => a (c t * g)) = fun t : ℝ => a (c t * (archP K n A * x₀)) := by
      funext t
      have e4 : c t * g = finOne K n u * (c t * (archP K n A * x₀)) := by
        have e5 : c t * finOne K n u = finOne K n u * c t := archimedeanProjection_mul_finiteEmbedding_comm _ u
        rw [← mul_assoc, ← e5, mul_assoc, ← mul_assoc (finOne K n u), ← archimedeanProjection_mul_finiteEmbedding_comm, ← e1,
          inv_mul_cancel_right]
      rw [e4]
      exact hinv u hu _
    change E A = deriv _ 0
    rw [e3, (hd A).deriv]
  have Dsupp : HasCompactSupport D := by
    refine HasCompactSupport.intro' (K := tsupport a) a.hasCompactSupport' (isClosed_tsupport _) fun g hg => ?_
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), c t * g ∈ (tsupport a)ᶜ :=
      (ccont.mul continuous_const).continuousAt.eventually_mem
        ((isClosed_tsupport _).isOpen_compl.mem_nhds (by simpa only [Pi.mul_apply, c0, one_mul, Set.mem_compl_iff] using hg))
    have : (fun t : ℝ => a (c t * g)) =ᶠ[𝓝 0] fun _ => 0 := hev.mono fun t ht => image_eq_zero_of_notMem_tsupport ht
    change deriv _ 0 = 0
    rw [this.deriv_eq, deriv_const]
  obtain ⟨L, hL⟩ := Dcont.bounded_above_of_compact_support Dsupp
  refine ⟨L, fun t g => ?_⟩
  have hall : ∀ s, HasDerivAt (fun t : ℝ => a (c t * g)) (D (c s * g)) s := fun s => by
    have h1 := hder (c s * g)
    rw [← sub_self s] at h1
    refine (h1.comp_sub_const s s).congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    simp only [← mul_assoc, ← cadd, sub_add_cancel]
  have h2 := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := fun t : ℝ => a (c t * g)) (s := Set.univ) (C := L)
    (x := 0) (y := t) (fun s _ => (hall s).differentiableAt) (fun s _ => by rw [(hall s).deriv]; exact hL _)
    convex_univ trivial trivial
  simpa only [c0, one_mul, sub_zero, Real.norm_eq_abs] using h2

/- English proof (translation)
Use `set S : Set G := (fun p : ℝ × G => (c p.1)⁻¹ * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a) with hS`. Establish `hSc : IsCompact S` using `(isCompact_Icc.prod has).image (((hc.comp continuous_fst).inv).mul continuous_snd)`. Establish `hout : ∀ t : ℝ, |t| ≤ 1 → ∀ g ∉ S, a (c t * g) = 0` using `fun t ht g hg => image_eq_zero_of_notMem_tsupport fun h => hg ⟨(t, c t * g), ⟨abs_le.1 ht, h⟩, inv_mul_cancel_left _ _⟩`. Establish `hout0 : ∀ g ∉ S, a g = 0` using `fun g hg => by simpa only [c0, one_mul] using hout 0 (by simp) g hg`. Take `⟨B, hB⟩` from `hb S hSc`.

Take `⟨A, hA⟩` from `hac.bounded_above_of_compact_support has`. Establish `hint : ∀ (f : G → ℂ) (M : ℝ) (z : ℂ), |z.re| ≤ 1 → (∀ g ∉ S, f g = 0) → (∀ g, ‖f g‖ ≤ M) → ‖∫ g, f g * Φ z g ∂μ‖ ≤ M * B * μ.real S` using `fun f M z hz h0 hM => by`. Rewrite using `[← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) fun g hg => by rw [h0 g hg, zero_mul]]`. Use `norm_setIntegral_le_of_norm_le_const hSc.measure_lt_top fun g hg => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul (hM g) (hB z hz g hg) (norm_nonneg _) ((norm_nonneg _).trans (hM g))`. Use `⟨max ((1 + Real.pi) * (A * B * μ.real S)) (2 * (L * Real.pi * B * μ.real S)), fun z hz => ?_⟩` and prove the remaining obligations. Use `set I := ∫ g, a g * Φ z g ∂μ with hI`. Distinguish the cases in `him : |z.im| ≤ Real.pi`. Use `le_trans ?_ (le_max_left _ _)` and prove the remaining obligations.

Conclude with `mul_le_mul (by linarith) (hint a A z hz hout0 hA) (norm_nonneg _) (by positivity)`. Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Establish `him' : Real.pi < |z.im|` using `not_le.1 him`. Establish `hpos : 0 < |z.im|` using `Real.pi_pos.trans him'`. Establish `hne : z.im ≠ 0` using `abs_pos.1 hpos`.

Use `set t : ℝ := Real.pi / z.im with ht`. Establish `habs : |t| = Real.pi / |z.im|` using `by rw [ht, abs_div, abs_of_pos Real.pi_pos]`. Establish `ht1 : |t| ≤ 1` using `by rw [habs]; exact (div_le_one hpos).2 him'.le`. Use `set r : ℝ := Real.exp ((z.re + 2) * t) with hr`. Establish `hr0 : 0 < r` using `Real.exp_pos _`.

Establish `he : Complex.exp ((z + 2) * t) = -(r : ℂ)`. Establish `: (z + 2) * t = (((z.re + 2) * t : ℝ) : ℂ) + Real.pi * Complex.I`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `[ht]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, mul_neg, mul_one]`. Use `set J := ∫ g, a (c t * g) * Φ z g ∂μ with hJ`. Establish `h1 : I = -(r : ℂ) * J`. Rewrite using `[hI, ← integral_mul_left_eq_self (fun g => a g * Φ z g) (c t), hJ, ← integral_const_mul]`.

Use `integral_congr_ae (Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [hcov, he]`. Expand and normalize the polynomial expressions, which then agree. Establish `i1 : Integrable (fun g => a g * Φ z g) μ` using `(hac.mul (hΦ z)).integrable_of_hasCompactSupport has.mul_right`. Establish `i2 : Integrable (fun g => a (c t * g) * Φ z g) μ` using `((hac.comp (continuous_const.mul continuous_id)).mul (hΦ z)).integrable_of_hasCompactSupport (HasCompactSupport.mul_right (HasCompactSupport.intro hSc (hout t ht1)))`.

Establish `h2 : ‖J - I‖ ≤ L * |t| * B * μ.real S`. Rewrite using `[hI, hJ, ← integral_sub i2 i1]`. Simplify `hint (fun g => a (c t * g) - a g) _ z hz (fun g hg => by rw [hout t ht1 g hg, hout0 g hg, sub_zero]) (hL t)` using `only [sub_mul]`. Establish `h3 : ‖I‖ ≤ ‖J - I‖`. Establish `e : J - I = ((1 + r : ℝ) : ℂ) * J` using `by rw [h1]; push_cast; ring`.

Rewrite using `[e, h1, norm_mul, norm_mul, norm_neg, Complex.norm_of_nonneg hr0.le, Complex.norm_of_nonneg (by positivity)]`. Conclude with `mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)`. Establish `h4 : |z.im| * ‖I‖ ≤ L * Real.pi * B * μ.real S`. Use `(mul_le_mul_of_nonneg_left (h3.trans h2) hpos.le).trans_eq ?_` and prove the remaining obligations. Rewrite using `[habs]`.

Clear the denominators using the available nonvanishing facts. Establish `h5 : (1 + |z.im|) * ‖I‖ ≤ 2 * |z.im| * ‖I‖` using `mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (norm_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem osc {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (a : G → ℂ) (hac : Continuous a) (has : HasCompactSupport a)
    (c : ℝ → G) (hc : Continuous c) (c0 : c 0 = 1) (L : ℝ) (hL : ∀ t g, ‖a (c t * g) - a g‖ ≤ L * |t|)
    (Φ : ℂ → G → ℂ) (hΦ : ∀ z, Continuous (Φ z)) (hcov : ∀ z (t : ℝ) g, Φ z (c t * g) = Complex.exp ((z + 2) * t) * Φ z g)
    (hb : ∀ S : Set G, IsCompact S → ∃ B : ℝ, ∀ z : ℂ, |z.re| ≤ 1 → ∀ g ∈ S, ‖Φ z g‖ ≤ B) :
    ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ 1 → (1 + |z.im|) * ‖∫ g, a g * Φ z g ∂μ‖ ≤ C := by
  set S : Set G := (fun p : ℝ × G => (c p.1)⁻¹ * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a) with hS
  have hSc : IsCompact S := (isCompact_Icc.prod has).image (((hc.comp continuous_fst).inv).mul continuous_snd)
  have hout : ∀ t : ℝ, |t| ≤ 1 → ∀ g ∉ S, a (c t * g) = 0 := fun t ht g hg =>
    image_eq_zero_of_notMem_tsupport fun h => hg ⟨(t, c t * g), ⟨abs_le.1 ht, h⟩, inv_mul_cancel_left _ _⟩
  have hout0 : ∀ g ∉ S, a g = 0 := fun g hg => by simpa only [c0, one_mul] using hout 0 (by simp) g hg
  obtain ⟨B, hB⟩ := hb S hSc
  obtain ⟨A, hA⟩ := hac.bounded_above_of_compact_support has
  have hint : ∀ (f : G → ℂ) (M : ℝ) (z : ℂ), |z.re| ≤ 1 → (∀ g ∉ S, f g = 0) → (∀ g, ‖f g‖ ≤ M) →
      ‖∫ g, f g * Φ z g ∂μ‖ ≤ M * B * μ.real S := fun f M z hz h0 hM => by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) fun g hg => by rw [h0 g hg, zero_mul]]
    refine norm_setIntegral_le_of_norm_le_const hSc.measure_lt_top fun g hg => ?_
    rw [norm_mul]
    exact mul_le_mul (hM g) (hB z hz g hg) (norm_nonneg _) ((norm_nonneg _).trans (hM g))
  refine ⟨max ((1 + Real.pi) * (A * B * μ.real S)) (2 * (L * Real.pi * B * μ.real S)), fun z hz => ?_⟩
  set I := ∫ g, a g * Φ z g ∂μ with hI
  by_cases him : |z.im| ≤ Real.pi
  · refine le_trans ?_ (le_max_left _ _)
    exact mul_le_mul (by linarith) (hint a A z hz hout0 hA) (norm_nonneg _) (by positivity)
  · refine le_trans ?_ (le_max_right _ _)
    have him' : Real.pi < |z.im| := not_le.1 him
    have hpos : 0 < |z.im| := Real.pi_pos.trans him'
    have hne : z.im ≠ 0 := abs_pos.1 hpos
    set t : ℝ := Real.pi / z.im with ht
    have habs : |t| = Real.pi / |z.im| := by rw [ht, abs_div, abs_of_pos Real.pi_pos]
    have ht1 : |t| ≤ 1 := by rw [habs]; exact (div_le_one hpos).2 him'.le
    set r : ℝ := Real.exp ((z.re + 2) * t) with hr
    have hr0 : 0 < r := Real.exp_pos _
    have he : Complex.exp ((z + 2) * t) = -(r : ℂ) := by
      have : (z + 2) * t = (((z.re + 2) * t : ℝ) : ℂ) + Real.pi * Complex.I := by
        apply Complex.ext
        · simp
        · simp [ht]
          field_simp
      rw [this, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, mul_neg, mul_one]
    set J := ∫ g, a (c t * g) * Φ z g ∂μ with hJ
    have h1 : I = -(r : ℂ) * J := by
      rw [hI, ← integral_mul_left_eq_self (fun g => a g * Φ z g) (c t), hJ, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only [hcov, he]
      ring
    have i1 : Integrable (fun g => a g * Φ z g) μ :=
      (hac.mul (hΦ z)).integrable_of_hasCompactSupport has.mul_right
    have i2 : Integrable (fun g => a (c t * g) * Φ z g) μ :=
      ((hac.comp (continuous_const.mul continuous_id)).mul (hΦ z)).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_right (HasCompactSupport.intro hSc (hout t ht1)))
    have h2 : ‖J - I‖ ≤ L * |t| * B * μ.real S := by
      rw [hI, hJ, ← integral_sub i2 i1]
      simpa only [sub_mul] using hint (fun g => a (c t * g) - a g) _ z hz
        (fun g hg => by rw [hout t ht1 g hg, hout0 g hg, sub_zero]) (hL t)
    have h3 : ‖I‖ ≤ ‖J - I‖ := by
      have e : J - I = ((1 + r : ℝ) : ℂ) * J := by rw [h1]; push_cast; ring
      rw [e, h1, norm_mul, norm_mul, norm_neg, Complex.norm_of_nonneg hr0.le, Complex.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have h4 : |z.im| * ‖I‖ ≤ L * Real.pi * B * μ.real S := by
      refine (mul_le_mul_of_nonneg_left (h3.trans h2) hpos.le).trans_eq ?_
      rw [habs]
      field_simp
    have h5 : (1 + |z.im|) * ‖I‖ ≤ 2 * |z.im| * ‖I‖ :=
      mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (norm_nonneg _)
    linarith

/- English proof (translation)
Introduce `K _ _ _ μ _ μ₂ _ τ₁ τ₂ _ D d d' A _ a β ha hβ`. Take `⟨hH, -, -, Hc, -⟩` from `hpSpec (K := K)`. Establish `hH' : ∀ (t : ℝ) (g : G1 K (2 + 2)), HP 2 2 (lv 1 1 t * g) = t + HP 2 2 g` using `fun t g => by`. Establish `h` using `hH 0 1 1 t g`. Establish `e : (nn 0 : G1 K (2 + 2)) = 1` using `Subtype.ext unipGL_zero`.

Rewrite `h` using `[e, one_mul]`. Then use the resulting hypothesis. Establish `pt : ∀ (v : Eu d) (x : G1 K (2 + 2)), ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ 1 → (1 + |z.im|) * ‖A.sec (symb β z v) x‖ ≤ C` using `fun v x => by`. Establish `hs : IsSec τ₁ τ₂ (A.sec v)` using `((A.onto _).1 ⟨v, rfl⟩).1`. Take `⟨M, hM⟩` from `hs.bdd`. Establish `hray : ∀ (t : ℝ) (g : G1 K (2 + 2)), A.sec v (lv 1 1 t * g) = A.sec v g` using `fun t g => by`.

Use `hs.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, blkLaws.1]`. Simplify using `only [OneMemClass.coe_one, one_mul, zt]`. Use `congr 3`. Conclude with `Subtype.ext (Real.exp_neg t)`.

Take `⟨Y, hY⟩` from `conj_exp x`. Take `⟨L, hL⟩` from `lip a ha Y`. Establish `hcc : Continuous fun t : ℝ => x⁻¹ * lv (1 : G1 K 2) 1 t * x` using `(continuous_const.mul ((blkLaws (K := K)).2.2.2.1.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))).mul continuous_const`. Establish `hHx : Continuous fun g : G1 K (2 + 2) => HP 2 2 (x * g)` using `Hc.comp (continuous_const.mul continuous_id)`. Establish `hre : ∀ (z : ℂ) (h : ℝ), ((z + 2) * (h : ℂ)).re = (z.re + 2) * h` using `fun z h => by simp`.

Take `⟨C, hC⟩` from `osc μ a a.continuous a.hasCompactSupport' (fun t => x⁻¹ * lv (1 : G1 K 2) 1 t * x) hcc (by rw [(blkLaws (K := K)).2.2.1, mul_one, inv_mul_cancel]) L (fun t g => by rw [hY]; exact hL t g) (fun z g => flat z (A.sec v) (x * g)) (fun z => (Complex.continuous_exp.comp (continuous_cons …`. Establish `e : x * (x⁻¹ * lv (1 : G1 K 2) 1 t * x * g) = lv 1 1 t * (x * g)` using `by group`. Simplify using `only [flat]`. Rewrite using `[e, hH', hray, Complex.ofReal_add, mul_add, Complex.exp_add, mul_assoc])`. Use the proof step `(fun S hS => by`.

Take `⟨R, hR⟩` from `hS.exists_bound_of_continuousOn hHx.continuousOn`. Use `⟨Real.exp (3 * R) * M, fun z hz g hg => ?_⟩` and prove the remaining obligations. Simplify using `only [flat]`. Rewrite using `[norm_mul, Complex.norm_exp, hre]`. Use `mul_le_mul (Real.exp_le_exp.2 ((le_abs_self _).trans ?_)) (hM _) (norm_nonneg _) (Real.exp_pos _).le` and prove the remaining obligations.

Rewrite using `[abs_mul]`. Conclude with `mul_le_mul (abs_le.2 ⟨by linarith [abs_le.1 hz], by linarith [abs_le.1 hz]⟩) (hR g hg) (abs_nonneg _) (by norm_num))`. Use `⟨Real.exp (3 * |HP 2 2 x|) * C, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `hC z hz`. Rewrite `h1` using `[hβ.2.2 z v x, flat, norm_mul, Complex.norm_exp, hre]`.

Establish `h2 : 1 ≤ Real.exp (3 * |HP 2 2 x|) * Real.exp ((z.re + 2) * HP 2 2 x)`. Rewrite using `[← Real.exp_add]`. Use `Real.one_le_exp ?_` and prove the remaining obligations. Establish `h3 : |(z.re + 2) * HP 2 2 x| ≤ 3 * |HP 2 2 x|`. Rewrite using `[abs_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (abs_le.2 ⟨by linarith [abs_le.1 hz], by linarith [abs_le.1 hz]⟩) (abs_nonneg _)`. Combine the linear relations using `[neg_abs_le ((z.re + 2) * HP 2 2 x)]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le`.

Take `⟨S, hS⟩` from `exists_finset_eval_eq_zero (LinearMap.range A.sec)`. Set `T : Eu d →ₗ[ℂ] (S → ℂ)` to `LinearMap.pi fun x => (LinearMap.proj (x : G1 K (2 + 2))).comp A.sec`. Establish `hT : LinearMap.ker T = ⊥`. Use `LinearMap.ker_eq_bot'.2 fun w hw => A.inj ?_` and prove the remaining obligations. Rewrite using `[map_zero]`.

Conclude with `hS _ ⟨w, rfl⟩ fun x hx => congrFun hw ⟨x, hx⟩`. Take `⟨k, -, hk⟩` from `T.exists_antilipschitzWith hT`. Take `⟨C, hC⟩` from `banach_steinhaus (g := fun z : {z : ℂ // |z.re| ≤ 1} => ((1 + |z.1.im| : ℝ) : ℂ) • symb β z.1) fun v => by choose C hC using pt v`. Use `⟨k * ∑ x ∈ S, |C x|, fun z => ?_⟩` and prove the remaining obligations. Use `(hk.le_mul_norm (map_zero T) _).trans (mul_le_mul_of_nonneg_left ?_ k.2)` and prove the remaining obligations.

Use `(pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun x => ?_` and prove the remaining obligations. Establish `e : T ((((1 + |z.1.im| : ℝ) : ℂ) • symb β z.1) v) x = ((1 + |z.1.im| : ℝ) : ℂ) * A.sec (symb β z.1 v) x`. Rewrite using `[ContinuousLinearMap.smul_apply, map_smul]`. Both sides reduce to the same expression. Rewrite using `[e, norm_mul, Complex.norm_of_nonneg (by positivity)]`.

Conclude with `((hC x z.1 z.2).trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) x.2)`. Use `⟨C, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h` using `hC ⟨z, hz⟩`. Rewrite `h` using `[norm_smul, Complex.norm_of_nonneg (by positivity)]`. Rewrite using `[le_div_iff₀ (by positivity), mul_comm]`.

Conclude with `h`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.decayA :
    ForAllC fun K _ _ μ _ _ _ _ _ D d _ A _ => ∀ (a : CC K (2 + 2)) (β : ℝ → Eu d →L[ℂ] Eu d), IsLeftSmooth a → ActsBy μ A a β →
      ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ 1 → ‖symb β z‖ ≤ C / (1 + |z.im|) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ _ D d d' A _ a β ha hβ
  obtain ⟨hH, -, -, Hc, -⟩ := hpSpec (K := K)
  have hH' : ∀ (t : ℝ) (g : G1 K (2 + 2)), HP 2 2 (lv 1 1 t * g) = t + HP 2 2 g := fun t g => by
    have h := hH 0 1 1 t g
    have e : (nn 0 : G1 K (2 + 2)) = 1 := Subtype.ext unipGL_zero
    rwa [e, one_mul] at h
  have pt : ∀ (v : Eu d) (x : G1 K (2 + 2)), ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ 1 →
      (1 + |z.im|) * ‖A.sec (symb β z v) x‖ ≤ C := fun v x => by
    have hs : IsSec τ₁ τ₂ (A.sec v) := ((A.onto _).1 ⟨v, rfl⟩).1
    obtain ⟨M, hM⟩ := hs.bdd
    have hray : ∀ (t : ℝ) (g : G1 K (2 + 2)), A.sec v (lv 1 1 t * g) = A.sec v g := fun t g => by
      refine hs.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_
      rw [Subgroup.coe_mul, blkLaws.1]
      simp only [OneMemClass.coe_one, one_mul, zt]
      congr 3
      exact Subtype.ext (Real.exp_neg t)
    obtain ⟨Y, hY⟩ := conj_exp x
    obtain ⟨L, hL⟩ := lip a ha Y
    have hcc : Continuous fun t : ℝ => x⁻¹ * lv (1 : G1 K 2) 1 t * x :=
      (continuous_const.mul ((blkLaws (K := K)).2.2.2.1.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)))).mul continuous_const
    have hHx : Continuous fun g : G1 K (2 + 2) => HP 2 2 (x * g) := Hc.comp (continuous_const.mul continuous_id)
    have hre : ∀ (z : ℂ) (h : ℝ), ((z + 2) * (h : ℂ)).re = (z.re + 2) * h := fun z h => by simp
    obtain ⟨C, hC⟩ := osc μ a a.continuous a.hasCompactSupport' (fun t => x⁻¹ * lv (1 : G1 K 2) 1 t * x) hcc
      (by rw [(blkLaws (K := K)).2.2.1, mul_one, inv_mul_cancel]) L (fun t g => by rw [hY]; exact hL t g)
      (fun z g => flat z (A.sec v) (x * g))
      (fun z => (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hHx))).mul
        (hs.cont.comp (continuous_const.mul continuous_id)))
      (fun z t g => by
        have e : x * (x⁻¹ * lv (1 : G1 K 2) 1 t * x * g) = lv 1 1 t * (x * g) := by group
        simp only [flat]
        rw [e, hH', hray, Complex.ofReal_add, mul_add, Complex.exp_add, mul_assoc])
      (fun S hS => by
        obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn hHx.continuousOn
        refine ⟨Real.exp (3 * R) * M, fun z hz g hg => ?_⟩
        simp only [flat]
        rw [norm_mul, Complex.norm_exp, hre]
        refine mul_le_mul (Real.exp_le_exp.2 ((le_abs_self _).trans ?_)) (hM _) (norm_nonneg _) (Real.exp_pos _).le
        rw [abs_mul]
        exact mul_le_mul (abs_le.2 ⟨by linarith [abs_le.1 hz], by linarith [abs_le.1 hz]⟩) (hR g hg) (abs_nonneg _)
          (by norm_num))
    refine ⟨Real.exp (3 * |HP 2 2 x|) * C, fun z hz => ?_⟩
    have h1 := hC z hz
    rw [hβ.2.2 z v x, flat, norm_mul, Complex.norm_exp, hre] at h1
    have h2 : 1 ≤ Real.exp (3 * |HP 2 2 x|) * Real.exp ((z.re + 2) * HP 2 2 x) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have h3 : |(z.re + 2) * HP 2 2 x| ≤ 3 * |HP 2 2 x| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_le.2 ⟨by linarith [abs_le.1 hz], by linarith [abs_le.1 hz]⟩) (abs_nonneg _)
      linarith [neg_abs_le ((z.re + 2) * HP 2 2 x)]
    calc (1 + |z.im|) * ‖A.sec (symb β z v) x‖
        ≤ (Real.exp (3 * |HP 2 2 x|) * Real.exp ((z.re + 2) * HP 2 2 x)) * ((1 + |z.im|) * ‖A.sec (symb β z v) x‖) :=
          le_mul_of_one_le_left (by positivity) h2
      _ = Real.exp (3 * |HP 2 2 x|) * ((1 + |z.im|) * (Real.exp ((z.re + 2) * HP 2 2 x) * ‖A.sec (symb β z v) x‖)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  obtain ⟨S, hS⟩ := exists_finset_eval_eq_zero (LinearMap.range A.sec)
  let T : Eu d →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun x => (LinearMap.proj (x : G1 K (2 + 2))).comp A.sec
  have hT : LinearMap.ker T = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun w hw => A.inj ?_
    rw [map_zero]
    exact hS _ ⟨w, rfl⟩ fun x hx => congrFun hw ⟨x, hx⟩
  obtain ⟨k, -, hk⟩ := T.exists_antilipschitzWith hT
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun z : {z : ℂ // |z.re| ≤ 1} => ((1 + |z.1.im| : ℝ) : ℂ) • symb β z.1) fun v => by
      choose C hC using pt v
      refine ⟨k * ∑ x ∈ S, |C x|, fun z => ?_⟩
      refine (hk.le_mul_norm (map_zero T) _).trans (mul_le_mul_of_nonneg_left ?_ k.2)
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun x => ?_
      have e : T ((((1 + |z.1.im| : ℝ) : ℂ) • symb β z.1) v) x = ((1 + |z.1.im| : ℝ) : ℂ) * A.sec (symb β z.1 v) x := by
        rw [ContinuousLinearMap.smul_apply, map_smul]
        rfl
      rw [e, norm_mul, Complex.norm_of_nonneg (by positivity)]
      exact ((hC x z.1 z.2).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) x.2)
  refine ⟨C, fun z hz => ?_⟩
  have h := hC ⟨z, hz⟩
  rw [norm_smul, Complex.norm_of_nonneg (by positivity)] at h
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact h
