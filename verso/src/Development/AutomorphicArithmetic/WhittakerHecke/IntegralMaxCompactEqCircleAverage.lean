import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private noncomputable def Mr (t : ℝ) : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ) :=
  !![fun _ => Real.cos t, fun _ => -Real.sin t; fun _ => Real.sin t, fun _ => Real.cos t]

/- English proof (translation)
Unfold `UpperTheory.ConvolutionTheory.RankTwoDescent.rot`. Conclude with `congrArg (fun g : GL (Fin 2) (TR.Rinf ℚ) => g.val i j) (TR.pInf_infGL _)`.
-/
private theorem rot_inf (t : ℝ) (i j : Fin 2) :
    TR.pInf ℚ ((UpperTheory.ConvolutionTheory.RankTwoDescent.rot t).val i j) = Mr t i j := by
  unfold UpperTheory.ConvolutionTheory.RankTwoDescent.rot
  exact congrArg (fun g : GL (Fin 2) (TR.Rinf ℚ) => g.val i j) (TR.pInf_infGL _)

/- English proof (translation)
Unfold `UpperTheory.ConvolutionTheory.RankTwoDescent.rot`. Conclude with `congrArg (fun g : GL (Fin 2) (Af ℚ) => g.val i j) (TR.pFin_infGL _)`.
-/
private theorem rot_fin (t : ℝ) (i j : Fin 2) :
    pFin ℚ ((UpperTheory.ConvolutionTheory.RankTwoDescent.rot t).val i j) = ((1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j) := by
  unfold UpperTheory.ConvolutionTheory.RankTwoDescent.rot
  exact congrArg (fun g : GL (Fin 2) (Af ℚ) => g.val i j) (TR.pFin_infGL _)

/- English proof (translation)
Establish `h : Continuous (TR.infEq ℚ).symm` using `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)`. Conclude with `(continuous_apply _).comp (h.comp continuous_fst)`.
-/
private theorem cont_re : Continuous UpperTheory.ConvolutionTheory.RankTwoDescent.re := by
  have h : Continuous (TR.infEq ℚ).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
        (continuous_apply w)
  exact (continuous_apply _).comp (h.comp continuous_fst)

private noncomputable def reH : A ℚ →+* ℝ :=
  (Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) Rat.infinitePlace).comp (TR.pInf ℚ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem re_eq (x : A ℚ) : UpperTheory.ConvolutionTheory.RankTwoDescent.re x = reH x := rfl

/- English proof (translation)
The claim follows from `Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous.matrix_elem i j`.
-/
private theorem cont_entry (i j : Fin 2) : Continuous fun k : G1 ℚ => k i j :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous.matrix_elem i j

private noncomputable def Rr (t : ℝ) : G1 ℚ := ⟨(UpperTheory.ConvolutionTheory.RankTwoDescent.rot t).val, by
  rw [Matrix.det_fin_two]
  apply TR.ad_ext
  · simp only [map_sub, map_mul, map_one, rot_inf]
    funext w
    simp [Mr]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · simp only [map_sub, map_mul, map_one, rot_fin]
    simp⟩

/- English proof (translation)
The claim follows from `rot_inf t i j`.
-/
private theorem Rr_inf (t : ℝ) (i j : Fin 2) : TR.pInf ℚ ((Rr t) i j) = Mr t i j := rot_inf t i j
/- English proof (translation)
The claim follows from `rot_fin t i j`.
-/
private theorem Rr_fin (t : ℝ) (i j : Fin 2) :
    pFin ℚ ((Rr t) i j) = ((1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j) := rot_fin t i j

/- English proof (translation)
The claim follows from `(TR.infEq ℚ).symm.injective h`.
-/
private theorem inf_ext {x y : A ℚ} (h : TR.pInf ℚ x = TR.pInf ℚ y) : x.1 = y.1 :=
  (TR.infEq ℚ).symm.injective h

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Apply `inf_ext` to reduce the goal to its premises. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add, map_mul, Rr_inf]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> funext w <;> simp [Mr] <;> nlinarith [Real.sin_sq_add_cos_sq t]`.

Introduce `v i j`. Establish `h : ((Rr t) i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j)` using `Rr_fin t i j`. Rewrite using `[h, Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`.
-/
private theorem Rr_mem (t : ℝ) : Rr t ∈ KK ℚ := by
  refine ⟨?_, ?_⟩
  · intro i j
    apply inf_ext
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add, map_mul, Rr_inf]
    fin_cases i <;> fin_cases j <;> funext w <;> simp [Mr] <;> nlinarith [Real.sin_sq_add_cos_sq t]
  · intro v i j
    have h : ((Rr t) i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j) := Rr_fin t i j
    rw [h, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

/- English proof (translation)
Use `congrFun (Rr_inf t 1 0) Rat.infinitePlace` as an intermediate fact. Express the relevant statement in the definitionally equal form `TR.pInf ℚ _ _ = _`. Simplify `this` using `[Mr]`.
-/
private theorem rotation_entry_sin (t : ℝ) : UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr t) 1 0) = Real.sin t := by
  have := congrFun (Rr_inf t 1 0) Rat.infinitePlace
  change TR.pInf ℚ _ _ = _
  simpa [Mr] using this
/- English proof (translation)
Use `congrFun (Rr_inf t 1 1) Rat.infinitePlace` as an intermediate fact. Express the relevant statement in the definitionally equal form `TR.pInf ℚ _ _ = _`. Simplify `this` using `[Mr]`.
-/
private theorem rotation_entry_cos (t : ℝ) : UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr t) 1 1) = Real.cos t := by
  have := congrFun (Rr_inf t 1 1) Rat.infinitePlace
  change TR.pInf ℚ _ _ = _
  simpa [Mr] using this

/- English proof (translation)
Express the relevant statement in the definitionally equal form `pLoc ℚ v (pFin ℚ ((Rr t) i j)) = _`. Rewrite using `[Rr_fin, Matrix.one_apply, Matrix.one_apply]`. Use `split_ifs`. Conclude with `map_one _`. Conclude with `map_zero _`.
-/
private theorem Rr_cp (t : ℝ) (v : H.P ℚ) (i j : Fin 2) :
    H.cp v ((Rr t) i j) = ((1 : Matrix (Fin 2) (Fin 2) (H.Kv v)) i j) := by
  change pLoc ℚ v (pFin ℚ ((Rr t) i j)) = _
  rw [Rr_fin, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

/- English proof (translation)
Establish `h : ∀ v, H.cp v ((Rr u * k) 1 0) = H.cp v (k 1 0)`. Introduce `v`. Simplify using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, Rr_cp]`. Simplify using `only [SS, Dv, Set.mem_setOf_eq, h]`.
-/
private theorem mul_mem_SS (N : ℕ) (u : ℝ) (k : G1 ℚ) : Rr u * k ∈ SS N ↔ k ∈ SS N := by
  have h : ∀ v, H.cp v ((Rr u * k) 1 0) = H.cp v (k 1 0) := by
    intro v
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, Rr_cp]
  simp only [SS, Dv, Set.mem_setOf_eq, h]

/- English proof (translation)
Introduce `v`. Simplify using `[Dv, Rr_cp]`.
-/
private theorem Rr_SS (N : ℕ) (t : ℝ) : Rr t ∈ SS N := by
  intro v
  simp [Dv, Rr_cp]

/- English proof (translation)
Establish `: SS N = ⋂ v, {k : G1 ℚ | Dv N v (k 1 0)}`. Use extensionality with `k`. Simplify using `[SS]`. Rewrite using `[this]`. Use `isClosed_iInter fun v => ?_` and prove the remaining obligations.

Establish `hc : ((N : H.Kv v)) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hcp : Continuous (H.cp v)`. Establish `h1 : Continuous (pLoc ℚ v)` using `RestrictedProduct.continuous_eval (R := fun v : H.P ℚ => v.adicCompletion ℚ) v`. Conclude with `h1.comp continuous_snd`. Establish `hset : {k : G1 ℚ | Dv N v (k 1 0)} = (fun k : G1 ℚ => H.cp v (k 1 0) * (N : H.Kv v)⁻¹) ⁻¹' (Valued.integer (H.Kv v) : Set (H.Kv v))`.

Use extensionality with `k`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Dv]`. Express the relevant statement in the definitionally equal form `_ ↔ Valued.v (H.cp v (k 1 0) * (N : H.Kv v)⁻¹) ≤ 1`. Rewrite using `[map_mul, map_inv₀, ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc))]`. Rewrite using `[hset]`.

Apply the tactic sequence `exact (Valued.isClosed_integer (H.Kv v)).preimage ((hcp.comp (cont_entry 1 0)).mul continuous_const)`.
-/
private theorem SS_closed (N : ℕ) (hN : 0 < N) : IsClosed (SS N) := by
  have : SS N = ⋂ v, {k : G1 ℚ | Dv N v (k 1 0)} := by
    ext k; simp [SS]
  rw [this]
  refine isClosed_iInter fun v => ?_
  have hc : ((N : H.Kv v)) ≠ 0 := by exact_mod_cast hN.ne'
  have hcp : Continuous (H.cp v) := by
    have h1 : Continuous (pLoc ℚ v) := RestrictedProduct.continuous_eval (R := fun v : H.P ℚ => v.adicCompletion ℚ) v
    exact h1.comp continuous_snd
  have hset : {k : G1 ℚ | Dv N v (k 1 0)} =
      (fun k : G1 ℚ => H.cp v (k 1 0) * (N : H.Kv v)⁻¹) ⁻¹' (Valued.integer (H.Kv v) : Set (H.Kv v)) := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Dv]
    change _ ↔ Valued.v (H.cp v (k 1 0) * (N : H.Kv v)⁻¹) ≤ 1
    rw [map_mul, map_inv₀, ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc))]
  rw [hset]
  exact (Valued.isClosed_integer (H.Kv v)).preimage ((hcp.comp (cont_entry 1 0)).mul continuous_const)

/- English proof (translation)
Establish `key : ∀ i j, reH ((k.1 * k.1ᵀ) i j) = reH ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)`. Introduce `i j`. Express the relevant statement in the definitionally equal form `(TR.infEq ℚ).symm ((k.1 * k.1ᵀ) i j).1 _ = (TR.infEq ℚ).symm ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1 _`. Rewrite using `[hk.1 i j]`. Establish `h00` using `key 0 0`.

Establish `h01` using `key 0 1`. Establish `h11` using `key 1 1`. Establish `hd : reH (k.1 0 0 * k.1 1 1 - k.1 0 1 * k.1 1 0) = 1`. Rewrite using `[← Matrix.det_fin_two, k.det_coe, map_one]`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add, map_mul, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), map_one, map_zero] at h00 h01 h11`.

Simplify using `only [map_sub, map_mul] at hd`. Simplify using `only [re_eq]`. Generalize the expression as in `reH (k.1 0 0) = a at *`. Generalize the expression as in `reH (k.1 0 1) = b at *`. Generalize the expression as in `reH (k.1 1 0) = c at *`.

Generalize the expression as in `reH (k.1 1 1) = d at *`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take the linear combination `(-a) * h11 + c * h01 + d * hd`. Take the linear combination `(-b) * h11 + d * h01 - c * hd`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem kk_rel {k : G1 ℚ} (hk : k ∈ KK ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 0 0) = UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1) ∧ UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 0 1) = - UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0) ∧
      UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0) ^ 2 + UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1) ^ 2 = 1 := by
  have key : ∀ i j, reH ((k.1 * k.1ᵀ) i j) = reH ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
    intro i j
    change (TR.infEq ℚ).symm ((k.1 * k.1ᵀ) i j).1 _ = (TR.infEq ℚ).symm ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1 _
    rw [hk.1 i j]
  have h00 := key 0 0
  have h01 := key 0 1
  have h11 := key 1 1
  have hd : reH (k.1 0 0 * k.1 1 1 - k.1 0 1 * k.1 1 0) = 1 := by
    rw [← Matrix.det_fin_two, k.det_coe, map_one]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add, map_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), map_one, map_zero] at h00 h01 h11
  simp only [map_sub, map_mul] at hd
  simp only [re_eq]
  generalize reH (k.1 0 0) = a at *
  generalize reH (k.1 0 1) = b at *
  generalize reH (k.1 1 0) = c at *
  generalize reH (k.1 1 1) = d at *
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-a) * h11 + c * h01 + d * hd
  · linear_combination (-b) * h11 + d * h01 - c * hd
  · nlinarith

private noncomputable def th (k : G1 ℚ) : ℝ :=
  Complex.arg ⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩

/- English proof (translation)
Establish `h : Continuous fun k : G1 ℚ => (⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩ : ℂ)`. Apply the tactic sequence `have h1 := cont_re.comp (cont_entry 1 1)`. Apply the tactic sequence `have h0 := cont_re.comp (cont_entry 1 0)`. Establish `: (fun k : G1 ℚ => (⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩ : ℂ)) = fun k => Complex.equivRealProdCLM.symm (UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDes …`. Apply the tactic sequence `funext k; apply Complex.ext <;> simp`.

Rewrite using `[this]`. Conclude with `Complex.equivRealProdCLM.symm.continuous.comp (h1.prodMk h0)`. Conclude with `Complex.measurable_arg.comp h.measurable`.
-/
private theorem th_meas : Measurable th := by
  have h : Continuous fun k : G1 ℚ => (⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩ : ℂ) := by
    have h1 := cont_re.comp (cont_entry 1 1)
    have h0 := cont_re.comp (cont_entry 1 0)
    have : (fun k : G1 ℚ => (⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩ : ℂ)) =
        fun k => Complex.equivRealProdCLM.symm (UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)) := by
      funext k; apply Complex.ext <;> simp
    rw [this]
    exact Complex.equivRealProdCLM.symm.continuous.comp (h1.prodMk h0)
  exact Complex.measurable_arg.comp h.measurable

/- English proof (translation)
Take `⟨-, -, h⟩` from `kk_rel hk`. Use `set z : ℂ := ⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩ with hz`. Establish `hn : ‖z‖ = 1`. Rewrite using `[Complex.norm_def, Complex.normSq_apply, Real.sqrt_eq_one]`. Simplify using `only [hz]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hz0 : z ≠ 0`. Introduce `h0`. Rewrite `hn` using `[h0]`. Simplify using `at hn`.

Prove the components needed by the constructor for the conclusion. Use `Complex.sin_arg z` as an intermediate fact. Rewrite `this` using `[hn, div_one]`. Conclude with `this.symm`. Use `Complex.cos_arg hz0` as an intermediate fact.

Rewrite `this` using `[hn, div_one]`. Conclude with `this.symm`.
-/
private theorem th_sin_cos {k : G1 ℚ} (hk : k ∈ KK ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0) = Real.sin (th k) ∧ UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1) = Real.cos (th k) := by
  obtain ⟨-, -, h⟩ := kk_rel hk
  set z : ℂ := ⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩ with hz
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_eq_one]
    simp only [hz]
    nlinarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hn
    simp at hn
  constructor
  · have := Complex.sin_arg z
    rw [hn, div_one] at this
    exact this.symm
  · have := Complex.cos_arg hz0
    rw [hn, div_one] at this
    exact this.symm

/- English proof (translation)
Take `⟨h0, h1, -⟩` from `kk_rel hk`. Take `⟨hs, hc⟩` from `th_sin_cos hk`. Establish `e0 : UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u * k) 1 0) = UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 0) * UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 0 0) + UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 1) * UpperTheory.ConvolutionT …`. Simplify using `only [re_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]`. Establish `e1 : UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u * k) 1 1) = UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 0) * UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 0 1) + UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 1) * UpperTheory.ConvolutionT …`.

Simplify using `only [re_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]`. Rewrite using `[e0, e1, rotation_entry_sin, rotation_entry_cos, h0, h1, hs, hc, Real.sin_add, Real.cos_add]`. Apply the tactic sequence `constructor <;> ring`.
-/
private theorem mul_re {u : ℝ} {k : G1 ℚ} (hk : k ∈ KK ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u * k) 1 0) = Real.sin (th k + u) ∧
      UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u * k) 1 1) = Real.cos (th k + u) := by
  obtain ⟨h0, h1, -⟩ := kk_rel hk
  obtain ⟨hs, hc⟩ := th_sin_cos hk
  have e0 : UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u * k) 1 0) = UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 0) * UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 0 0) +
      UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 1) * UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0) := by
    simp only [re_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
  have e1 : UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u * k) 1 1) = UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 0) * UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 0 1) +
      UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 1) * UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1) := by
    simp only [re_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
  rw [e0, e1, rotation_entry_sin, rotation_entry_cos, h0, h1, hs, hc, Real.sin_add, Real.cos_add]
  constructor <;> ring

/- English proof (translation)
Set `Fu : ℝ → X → ℂ` to `fun u => S.indicator fun k => H' (θ k + u)`. Establish `hFm : Measurable (Function.uncurry Fu)`. Establish `h2 : Measurable fun p : ℝ × X => H' (θ p.2 + p.1)` using `hH.comp ((hθ.comp measurable_snd).add measurable_fst)`. Establish `h3 : Function.uncurry Fu = (Set.univ ×ˢ S).indicator fun p : ℝ × X => H' (θ p.2 + p.1)`. Use function extensionality and compare the values at `p`.

Apply the tactic sequence `by_cases hp : p.2 ∈ S <;> simp [Fu, Function.uncurry, Set.indicator, hp]`. Rewrite using `[h3]`. Conclude with `h2.indicator (MeasurableSet.univ.prod hS)`. Use `set J : ℂ := ∫ t in (0 : ℝ)..2 * Real.pi, H' t with hJ`. Establish `hbound : ∀ p : ℝ × X, ‖Function.uncurry Fu p‖ ≤ C`.

Introduce `p`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 0)`. Distinguish the cases in `hp : p.2 ∈ S`. Simplify `hC _` using `[Fu, Function.uncurry, hp]`. Simplify `hC0` using `[Fu, Function.uncurry, hp]`.

Establish `hint : Integrable (Function.uncurry Fu) ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod κ)` using `Integrable.of_bound hFm.aestronglyMeasurable C (Eventually.of_forall hbound)`. Establish `hpi : (0 : ℝ) ≤ 2 * Real.pi` using `by positivity`. Establish `hinner : ∀ k, ∫ u in Set.Ioc 0 (2 * Real.pi), Fu u k = S.indicator (fun _ => J) k`. Introduce `k`. Distinguish the cases in `hs : k ∈ S`.

Simplify using `only [Fu, Set.indicator_of_mem hs]`. Rewrite using `[← intervalIntegral.integral_of_le hpi, intervalIntegral.integral_comp_add_left (fun t => H' t) (θ k)]`. Use `hper.intervalIntegral_add_eq (θ k) 0` as an intermediate fact. Rewrite `this` using `[zero_add]`. Rewrite using `[add_zero]`.

Conclude with `this`. Simplify using `[Fu, hs]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[hpi]`. Use `_ = ∫ u in Set.Ioc 0 (2 * Real.pi), ∫ k, Fu u k ∂κ := by`.

Use `integral_congr_ae (Eventually.of_forall fun u => hinv u)` and prove the remaining obligations. Use `_ = ∫ k, ∫ u in Set.Ioc 0 (2 * Real.pi), Fu u k ∂volume ∂κ := integral_integral_swap hint`. Use `_ = ∫ k, S.indicator (fun _ => J) k ∂κ := by simp_rw [hinner]`. Use `_ = κ.real S • J := integral_indicator_const _ hS`.
-/
private theorem avg {X : Type} [MeasurableSpace X] (κ : Measure X) [IsProbabilityMeasure κ] (S : Set X)
    (hS : MeasurableSet S) (θ : X → ℝ) (hθ : Measurable θ) (H' : ℝ → ℂ) (hH : Measurable H') (C : ℝ)
    (hC : ∀ t, ‖H' t‖ ≤ C) (hper : Function.Periodic H' (2 * Real.pi)) (I : ℂ)
    (hinv : ∀ u : ℝ, I = ∫ k, S.indicator (fun k => H' (θ k + u)) k ∂κ) :
    (2 * Real.pi : ℝ) • I = κ.real S • ∫ t in (0 : ℝ)..2 * Real.pi, H' t := by
  let Fu : ℝ → X → ℂ := fun u => S.indicator fun k => H' (θ k + u)
  have hFm : Measurable (Function.uncurry Fu) := by
    have h2 : Measurable fun p : ℝ × X => H' (θ p.2 + p.1) :=
      hH.comp ((hθ.comp measurable_snd).add measurable_fst)
    have h3 : Function.uncurry Fu = (Set.univ ×ˢ S).indicator fun p : ℝ × X => H' (θ p.2 + p.1) := by
      funext p
      by_cases hp : p.2 ∈ S <;> simp [Fu, Function.uncurry, Set.indicator, hp]
    rw [h3]
    exact h2.indicator (MeasurableSet.univ.prod hS)
  set J : ℂ := ∫ t in (0 : ℝ)..2 * Real.pi, H' t with hJ
  have hbound : ∀ p : ℝ × X, ‖Function.uncurry Fu p‖ ≤ C := by
    intro p
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    by_cases hp : p.2 ∈ S
    · simpa [Fu, Function.uncurry, hp] using hC _
    · simpa [Fu, Function.uncurry, hp] using hC0
  have hint : Integrable (Function.uncurry Fu) ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod κ) :=
    Integrable.of_bound hFm.aestronglyMeasurable C (Eventually.of_forall hbound)
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hinner : ∀ k, ∫ u in Set.Ioc 0 (2 * Real.pi), Fu u k = S.indicator (fun _ => J) k := by
    intro k
    by_cases hs : k ∈ S
    · simp only [Fu, Set.indicator_of_mem hs]
      rw [← intervalIntegral.integral_of_le hpi, intervalIntegral.integral_comp_add_left (fun t => H' t) (θ k)]
      have := hper.intervalIntegral_add_eq (θ k) 0
      rw [zero_add] at this
      rw [add_zero]
      exact this
    · simp [Fu, hs]
  calc (2 * Real.pi : ℝ) • I
      = ∫ _u in Set.Ioc 0 (2 * Real.pi), I := by
        simp [hpi]
    _ = ∫ u in Set.Ioc 0 (2 * Real.pi), ∫ k, Fu u k ∂κ := by
        refine integral_congr_ae (Eventually.of_forall fun u => hinv u)
    _ = ∫ k, ∫ u in Set.Ioc 0 (2 * Real.pi), Fu u k ∂volume ∂κ := integral_integral_swap hint
    _ = ∫ k, S.indicator (fun _ => J) k ∂κ := by simp_rw [hinner]
    _ = κ.real S • J := integral_indicator_const _ hS

/- English proof (translation)
Introduce `M N hN A' H' hH ⟨C, hC⟩ h0 h1`. Use `haveI := M.prob`. Establish `hS : MeasurableSet (SS N)` using `(SS_closed N hN).measurableSet`. Establish `hper : Function.Periodic H' (2 * Real.pi)` using `fun t => by`. Establish `e1` using `h1 (Rr t) (Rr_mem t) (Rr_SS N t) t (rotation_entry_sin t) (rotation_entry_cos t)`.

Establish `e2` using `h1 (Rr t) (Rr_mem t) (Rr_SS N t) (t + 2 * Real.pi) (by rw [rotation_entry_sin, Real.sin_add_two_pi]) (by rw [rotation_entry_cos, Real.cos_add_two_pi])`. Conclude with `e2.symm.trans e1`. Establish `hKK : ∀ᵐ k ∂M.κ, k ∈ KK ℚ`. Rewrite using `[ae_iff]`. Conclude with `M.supp`.

Establish `hFm : ∀ u : ℝ, Measurable ((SS N).indicator fun k => H' (th k + u))` using `fun u => (hH.comp (th_meas.add_const u)).indicator hS`. Establish `key : ∀ u : ℝ, ∀ k ∈ KK ℚ, A' (Rr u * k) = (SS N).indicator (fun k => H' (th k + u)) k`. Introduce `u k hk`. Establish `hk' : Rr u * k ∈ KK ℚ`. Take `⟨hKs, -⟩` from `UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ`.

Establish `a1` using `Rr_mem u`. Rewrite `a1`, `hk`, the goal using `[hKs]`. Conclude with `(UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).mul_mem a1 hk`. Distinguish the cases in `hs : k ∈ SS N`. Rewrite using `[h1 _ hk' ((mul_mem_SS N u k).2 hs) (th k + u) (mul_re hk).1 (mul_re hk).2, Set.indicator_of_mem hs]`.

Rewrite using `[h0 _ hk' (fun h => hs ((mul_mem_SS N u k).1 h)), Set.indicator_of_notMem hs]`. Establish `hA0 : A' =ᵐ[M.κ] (SS N).indicator fun k => H' (th k + 0)`. Use `hKK.mono fun k hk => ?_` and prove the remaining obligations. Distinguish the cases in `hs : k ∈ SS N`. Rewrite using `[h1 k hk hs (th k) (th_sin_cos hk).1 (th_sin_cos hk).2, Set.indicator_of_mem hs, add_zero]`.

Rewrite using `[h0 k hk hs, Set.indicator_of_notMem hs]`. Establish `hAs : AEStronglyMeasurable A' M.κ` using `(hFm 0).aestronglyMeasurable.congr hA0.symm`. Establish `hinv : ∀ u : ℝ, ∫ k, A' k ∂M.κ = ∫ k, (SS N).indicator (fun k => H' (th k + u)) k ∂M.κ`. Introduce `u`. Establish `hm : Measurable (fun x : G1 ℚ => Rr u * x)` using `(continuous_const.mul continuous_id).measurable`.

Combine the equalities or inequalities in the displayed calculation. Establish `hmain` using `avg M.κ (SS N) hS th th_meas H' hH C hC hper _ hinv`. Establish `hc : M.κ.real (SS N) = cK M N`. Simplify using `only [cK, Measure.real]`. Rewrite using `[measure_inter_conull M.supp]`.

Rewrite `hmain` using `[hc]`. Establish `hpi0 : (2 * Real.pi : ℝ) ≠ 0` using `by positivity`. Establish `hpc : ((2 * Real.pi : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hpi0`. Simplify using `only [Complex.real_smul] at hmain`. Rewrite using `[Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hpc, mul_comm]`.

Conclude with `hmain`.
-/
theorem UpperTheory.integral_maxCompact_eq_circle_average :
    ∀ (M : Meas ℚ) (N : ℕ), 0 < N → ∀ (A' : G1 ℚ → ℂ) (H' : ℝ → ℂ), Measurable H' → (∃ C : ℝ, ∀ t, ‖H' t‖ ≤ C) →
        (∀ k ∈ KK ℚ, k ∉ SS N → A' k = 0) →
        (∀ k ∈ KK ℚ, k ∈ SS N → ∀ t : ℝ, re (k 1 0) = Real.sin t → re (k 1 1) = Real.cos t → A' k = H' t) →
        ∫ k, A' k ∂M.κ = ((cK M N / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (0 : ℝ)..2 * Real.pi, H' t := by
  intro M N hN A' H' hH ⟨C, hC⟩ h0 h1
  haveI := M.prob
  have hS : MeasurableSet (SS N) := (SS_closed N hN).measurableSet
  have hper : Function.Periodic H' (2 * Real.pi) := fun t => by
    have e1 := h1 (Rr t) (Rr_mem t) (Rr_SS N t) t (rotation_entry_sin t) (rotation_entry_cos t)
    have e2 := h1 (Rr t) (Rr_mem t) (Rr_SS N t) (t + 2 * Real.pi)
      (by rw [rotation_entry_sin, Real.sin_add_two_pi]) (by rw [rotation_entry_cos, Real.cos_add_two_pi])
    exact e2.symm.trans e1
  have hKK : ∀ᵐ k ∂M.κ, k ∈ KK ℚ := by
    rw [ae_iff]
    exact M.supp
  have hFm : ∀ u : ℝ, Measurable ((SS N).indicator fun k => H' (th k + u)) := fun u =>
    (hH.comp (th_meas.add_const u)).indicator hS
  have key : ∀ u : ℝ, ∀ k ∈ KK ℚ, A' (Rr u * k) = (SS N).indicator (fun k => H' (th k + u)) k := by
    intro u k hk
    have hk' : Rr u * k ∈ KK ℚ := by
      obtain ⟨hKs, -⟩ := UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ
      have a1 := Rr_mem u
      rw [hKs] at a1 hk ⊢
      exact (UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).mul_mem a1 hk
    by_cases hs : k ∈ SS N
    · rw [h1 _ hk' ((mul_mem_SS N u k).2 hs) (th k + u) (mul_re hk).1 (mul_re hk).2, Set.indicator_of_mem hs]
    · rw [h0 _ hk' (fun h => hs ((mul_mem_SS N u k).1 h)), Set.indicator_of_notMem hs]
  have hA0 : A' =ᵐ[M.κ] (SS N).indicator fun k => H' (th k + 0) := by
    refine hKK.mono fun k hk => ?_
    by_cases hs : k ∈ SS N
    · rw [h1 k hk hs (th k) (th_sin_cos hk).1 (th_sin_cos hk).2, Set.indicator_of_mem hs, add_zero]
    · rw [h0 k hk hs, Set.indicator_of_notMem hs]
  have hAs : AEStronglyMeasurable A' M.κ := (hFm 0).aestronglyMeasurable.congr hA0.symm
  have hinv : ∀ u : ℝ, ∫ k, A' k ∂M.κ = ∫ k, (SS N).indicator (fun k => H' (th k + u)) k ∂M.κ := by
    intro u
    have hm : Measurable (fun x : G1 ℚ => Rr u * x) := (continuous_const.mul continuous_id).measurable
    calc ∫ k, A' k ∂M.κ = ∫ k, A' k ∂(M.κ.map (Rr u * ·)) := by rw [M.κ_left _ (Rr_mem u)]
      _ = ∫ k, A' (Rr u * k) ∂M.κ :=
        integral_map hm.aemeasurable (by rw [M.κ_left _ (Rr_mem u)]; exact hAs)
      _ = _ := integral_congr_ae (hKK.mono fun k hk => key u k hk)
  have hmain := avg M.κ (SS N) hS th th_meas H' hH C hC hper _ hinv
  have hc : M.κ.real (SS N) = cK M N := by
    simp only [cK, Measure.real]
    rw [measure_inter_conull M.supp]
  rw [hc] at hmain
  have hpi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpc : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi0
  simp only [Complex.real_smul] at hmain
  rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hpc, mul_comm]
  exact hmain
