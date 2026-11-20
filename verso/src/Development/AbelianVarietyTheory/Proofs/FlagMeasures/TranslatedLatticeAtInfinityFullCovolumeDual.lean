import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase Module

noncomputable section

namespace GlobalTheory.LatFacts

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

abbrev Idx : Type := Σ _ : InfinitePlace E, Σ _ : Fin j, Fin 2

def stdB : Basis (Idx E j) ℝ (VecInf E j) :=
  Pi.basis fun _ => Pi.basis fun _ => Complex.basisOneI

def cube : Set (VecInf E j) :=
  {y | ∀ w a, (y w a).re ∈ Set.Ico (0 : ℝ) 1 ∧ (y w a).im ∈ Set.Ico (0 : ℝ) 1}

/- English proof (translation)
Use extensionality with `z`. Simplify using `[ZSpan.fundamentalDomain, stdB, cube, Pi.basis_repr, Sigma.forall, Fin.forall_fin_two]`.
-/
theorem fd_stdB : ZSpan.fundamentalDomain (stdB E j) = cube E j := by
  ext z
  simp [ZSpan.fundamentalDomain, stdB, cube, Pi.basis_repr, Sigma.forall, Fin.forall_fin_two]

/- English proof (translation)
Establish `h : cube E j = Set.pi Set.univ fun _ : InfinitePlace E => Set.pi Set.univ fun _ : Fin j => Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1)`. Use extensionality with `z`. Simplify using `[cube]`. Rewrite using `[h, volume_pi_pi]`. Use `Finset.prod_eq_one fun _ _ => ?_` and prove the remaining obligations.

Rewrite using `[volume_pi_pi]`. Use `Finset.prod_eq_one fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.volume_preserving_equiv_real_prod.measure_preimage (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]`. Simplify using `[Measure.volume_eq_prod]`.
-/
theorem volume_cube : volume (cube E j) = 1 := by
  have h : cube E j = Set.pi Set.univ fun _ : InfinitePlace E => Set.pi Set.univ fun _ : Fin j =>
        Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp [cube]
  rw [h, volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]

instance : (volume : Measure (VecInf E j)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

/- English proof (translation)
The claim follows from `ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain b volume)`.
-/
theorem covAt_span {ι : Type} [Fintype ι] (b : Basis ι ℝ (VecInf E j)) :
    covAt E j (Submodule.span ℤ (Set.range b)) = volume.real (ZSpan.fundamentalDomain b) :=
  ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain b volume)

open Classical in
/- English proof (translation)
Rewrite using `[covAt_span, ZSpan.measureReal_fundamentalDomain b volume (stdB E j), fd_stdB, Measure.real, volume_cube]`. Simplify using the standard rewrite rules.
-/
theorem covAt_span_std (b : Basis (Idx E j) ℝ (VecInf E j)) :
    covAt E j (Submodule.span ℤ (Set.range b)) = |(stdB E j).det b| := by
  rw [covAt_span, ZSpan.measureReal_fundamentalDomain b volume (stdB E j), fd_stdB, Measure.real, volume_cube]
  simp

def form : LinearMap.BilinForm ℝ (VecInf E j) :=
  LinearMap.mk₂ ℝ (fun x y => ∑ w, (x w ⬝ᵥ y w).re)
    (fun x x' y => by simp [add_dotProduct, Finset.sum_add_distrib])
    (fun c x y => by simp [smul_dotProduct, Finset.mul_sum])
    (fun x y y' => by simp [dotProduct_add, Finset.sum_add_distrib])
    (fun c x y => by simp [dotProduct_smul, Finset.mul_sum])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem form_apply (x y : VecInf E j) : form E j x y = ∑ w, (x w ⬝ᵥ y w).re := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x y => by simp [form_apply, dotProduct_comm]⟩`.
-/
theorem form_symm : (form E j).IsSymm := ⟨fun x y => by simp [form_apply, dotProduct_comm]⟩

open Classical in
/- English proof (translation)
Use extensionality with `⟨w, a, s⟩ ⟨w', a', s'⟩`. Rewrite using `[LinearMap.BilinForm.toMatrix_apply, form_apply, Matrix.diagonal_apply]`. Simplify using `only [stdB, Pi.basis_apply]`. Rewrite using `[Finset.sum_eq_single w]`. Distinguish the cases in `hw : w = w'`.

Substitute `hw` using the available equality. Simplify using `only [Pi.single_eq_same, single_dotProduct]`. Distinguish the cases in `ha : a = a'`. Apply the tactic sequence `subst ha fin_cases s <;> fin_cases s' <;> simp`. Simplify using `[ha, Pi.single_eq_of_ne ha]`.

Simplify using `[hw, Pi.single_eq_of_ne hw]`. Introduce `w'' _ h`. Simplify using `[Pi.single_eq_of_ne h]`. Simplify using the standard rewrite rules.
-/
theorem toMatrix_form : LinearMap.BilinForm.toMatrix (stdB E j) (form E j) =
    Matrix.diagonal fun i : Idx E j => if i.2.2 = 0 then (1 : ℝ) else -1 := by
  ext ⟨w, a, s⟩ ⟨w', a', s'⟩
  rw [LinearMap.BilinForm.toMatrix_apply, form_apply, Matrix.diagonal_apply]
  simp only [stdB, Pi.basis_apply]
  rw [Finset.sum_eq_single w]
  · by_cases hw : w = w'
    · subst hw
      simp only [Pi.single_eq_same, single_dotProduct]
      by_cases ha : a = a'
      · subst ha
        fin_cases s <;> fin_cases s' <;> simp
      · simp [ha, Pi.single_eq_of_ne ha]
    · simp [hw, Pi.single_eq_of_ne hw]
  · intro w'' _ h
    simp [Pi.single_eq_of_ne h]
  · simp

open Classical in
/- English proof (translation)
Rewrite using `[toMatrix_form, Matrix.det_diagonal, Finset.abs_prod]`. Apply the tactic sequence `exact Finset.prod_eq_one fun i _ => by split_ifs <;> simp`.
-/
theorem abs_det_form : |(LinearMap.BilinForm.toMatrix (stdB E j) (form E j)).det| = 1 := by
  rw [toMatrix_form, Matrix.det_diagonal, Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => by split_ifs <;> simp

/- English proof (translation)
Rewrite using `[LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (stdB E j)]`. Introduce `h`. Use `abs_det_form E j` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.
-/
theorem form_nondeg : (form E j).Nondegenerate := by
  classical
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (stdB E j)]
  intro h
  have := abs_det_form E j
  rw [h] at this
  simp at this

/- English proof (translation)
Rewrite using `[dualAt, ← Submodule.span_eq ((form E j).dualSubmodule L)]`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one, form_apply, eq_intCast]`. Use `forall₂_congr fun x _ => exists_congr fun z => ?_` and prove the remaining obligations.

Simplify using `only [dotProduct_comm (y _)]`. Conclude with `eq_comm`.
-/
theorem dualAt_eq (L : Submodule ℤ (VecInf E j)) : dualAt E j L = (form E j).dualSubmodule L := by
  rw [dualAt, ← Submodule.span_eq ((form E j).dualSubmodule L)]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one,
    form_apply, eq_intCast]
  refine forall₂_congr fun x _ => exists_congr fun z => ?_
  simp only [dotProduct_comm (y _)]
  exact eq_comm

/- English proof (translation)
Rewrite using `[dualAt_eq, dualAt_eq]`. Conclude with `LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ (form_nondeg E j) (form_symm E j) b`.
-/
theorem dual_dual {ι : Type} [Fintype ι] (b : Basis ι ℝ (VecInf E j)) :
    dualAt E j (dualAt E j (Submodule.span ℤ (Set.range b))) = Submodule.span ℤ (Set.range b) := by
  rw [dualAt_eq, dualAt_eq]
  exact LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ (form_nondeg E j) (form_symm E j) b

/- English proof (translation)
Rewrite using `[dualAt_eq, LinearMap.BilinForm.dualSubmodule_span_of_basis _ (form_nondeg E j) b, covAt_span_std, covAt_span_std]`. Use `set d := (form E j).dualBasis (form_nondeg E j) b with hd`. Establish `h : ((stdB E j).toMatrix d)ᵀ * LinearMap.BilinForm.toMatrix (stdB E j) (form E j) * (stdB E j).toMatrix b = 1`. Use extensionality with `i k`. Establish `h1 : form E j (d i) (b k) = if k = i then 1 else 0` using `LinearMap.BilinForm.apply_dualBasis_left (form_nondeg E j) b i k`.

Establish `h3 : (1 : Matrix (Idx E j) (Idx E j) ℝ) i k = form E j (d i) (b k)`. Rewrite using `[h1, Matrix.one_apply]`. Conclude with `if_congr eq_comm rfl rfl`. Rewrite using `[h3]`. Use `conv_rhs => rw [← (stdB E j).sum_repr (d i), ← (stdB E j).sum_repr (b k)]`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Basis.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Use `first`. Consider the case `exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Consider the case `(rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)`. Establish `h2` using `congrArg (fun M => |Matrix.det M|) h`.

Simplify using `only [Matrix.det_mul, Matrix.det_transpose, abs_mul, abs_det_form, Matrix.det_one, abs_one, mul_one] at h2`. Rewrite using `[Basis.det_apply, Basis.det_apply]`. Conclude with `eq_inv_of_mul_eq_one_left h2`.
-/
theorem covAt_dual (b : Basis (Idx E j) ℝ (VecInf E j)) :
    covAt E j (dualAt E j (Submodule.span ℤ (Set.range b))) = (covAt E j (Submodule.span ℤ (Set.range b)))⁻¹ := by
  classical
  rw [dualAt_eq, LinearMap.BilinForm.dualSubmodule_span_of_basis _ (form_nondeg E j) b, covAt_span_std,
    covAt_span_std]
  set d := (form E j).dualBasis (form_nondeg E j) b with hd
  have h : ((stdB E j).toMatrix d)ᵀ * LinearMap.BilinForm.toMatrix (stdB E j) (form E j) *
      (stdB E j).toMatrix b = 1 := by
    ext i k
    have h1 : form E j (d i) (b k) = if k = i then 1 else 0 :=
      LinearMap.BilinForm.apply_dualBasis_left (form_nondeg E j) b i k
    have h3 : (1 : Matrix (Idx E j) (Idx E j) ℝ) i k = form E j (d i) (b k) := by
      rw [h1, Matrix.one_apply]
      exact if_congr eq_comm rfl rfl
    rw [h3]
    conv_rhs => rw [← (stdB E j).sum_repr (d i), ← (stdB E j).sum_repr (b k)]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Basis.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply,
      map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    first
      | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  have h2 := congrArg (fun M => |Matrix.det M|) h
  simp only [Matrix.det_mul, Matrix.det_transpose, abs_mul, abs_det_form, Matrix.det_one, abs_one, mul_one] at h2
  rw [Basis.det_apply, Basis.det_apply]
  exact eq_inv_of_mul_eq_one_left h2

def act (M : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) : VecInf E j →ₗ[ℝ] VecInf E j :=
  LinearMap.pi fun w => ((Matrix.toLin' (M w)).restrictScalars ℝ).comp (LinearMap.proj w)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem act_apply (M : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) (x : VecInf E j) (w : InfinitePlace E) :
    act E j M x w = M w *ᵥ x w := rfl

/- English proof (translation)
Rewrite using `[act, LinearMap.det_pi]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]`.
-/
theorem det_act (M : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (act E j M) = ∏ w, ‖(M w).det‖ ^ 2 := by
  rw [act, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Rewrite using `[det_act, detNorm, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, inv_pow]`.
-/
theorem det_act_inv (g : MatInf E j) :
    LinearMap.det (act E j fun w => (Matrix.of (g w))⁻¹) = (detNorm E j g)⁻¹ := by
  rw [det_act, detNorm, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, inv_pow]

def emb : (Fin j → E) →+ VecInf E j where
  toFun y w a := w.embedding (y a)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def mix [IsTotallyComplex E] : (Fin j → mixedEmbedding.mixedSpace E) ≃ₗ[ℝ] VecInf E j where
  toFun x w a := (x a).2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun y a := (fun _ => 0, fun w => y w.1 a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext a
    refine Prod.ext ?_ rfl
    funext w
    exact absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1))
  right_inv _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mix_apply [IsTotallyComplex E] (x : Fin j → mixedEmbedding.mixedSpace E) (w : InfinitePlace E) (a : Fin j) :
    mix E j x w a = (x a).2 ⟨w, IsTotallyComplex.isComplex w⟩ := rfl

def ratB : Basis (Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ (Fin j → E) :=
  Pi.basis fun _ => integralBasis E

def intB [IsTotallyComplex E] : Basis (Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (VecInf E j) :=
  (Pi.basis fun _ => mixedEmbedding.latticeBasis E).map (mix E j)

/- English proof (translation)
Take `⟨a, i⟩` from `i`. Use function extensionality and compare the values at `w c`. Simplify using `only [intB, ratB, Basis.map_apply, Pi.basis_apply, mix_apply, emb, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Distinguish the cases in `h : c = a`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.
-/
theorem intB_apply [IsTotallyComplex E] (i) : intB E j i = emb E j (ratB E j i) := by
  obtain ⟨a, i⟩ := i
  funext w c
  simp only [intB, ratB, Basis.map_apply, Pi.basis_apply, mix_apply, emb, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  by_cases h : c = a
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

instance : MeasurableAdd (mixedEmbedding.mixedSpace E) := MeasurableAdd₂.toMeasurableAdd

open Classical in
/- English proof (translation)
Use `haveI : (volume : Measure (Fin j → mixedEmbedding.mixedSpace E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI : @BorelSpace (Fin j → mixedEmbedding.mixedSpace E) _ MeasureSpace.toMeasurableSpace := Pi.borelSpace`. Establish `hpi : ∀ {κ : Type} [Fintype κ] (c : Basis κ ℝ (mixedEmbedding.mixedSpace E)), volume.real (ZSpan.fundamentalDomain (Pi.basis fun _ : Fin j => c)) = volume.real (ZSpan.fundamentalDomain c) ^ j`. Introduce `κ _ c`. Establish `: ZSpan.fundamentalDomain (Pi.basis fun _ : Fin j => c) = Set.pi Set.univ fun _ => ZSpan.fundamentalDomain c`.

Use extensionality with `y`. Simplify using `only [ZSpan.mem_fundamentalDomain, Pi.basis_repr, Sigma.forall, Set.mem_pi, Set.mem_univ, true_implies]`. Rewrite using `[this, measureReal_def, volume_pi_pi, ENNReal.toReal_prod, measureReal_def]`. Simplify using the standard rewrite rules. Set `s` to `(mixedEmbedding.stdBasis E).reindex ((mixedEmbedding.stdBasis E).indexEquiv b)`.

Establish `hs : ZSpan.fundamentalDomain s = ZSpan.fundamentalDomain (mixedEmbedding.stdBasis E)` using `ZSpan.fundamentalDomain_reindex _ _`. Establish `hs1 : volume.real (ZSpan.fundamentalDomain s) = 1`. Rewrite using `[hs, Measure.real, mixedEmbedding.volume_fundamentalDomain_stdBasis]`. Simplify using the standard rewrite rules. Establish `hc : ZSpan.fundamentalDomain ((Pi.basis fun _ : Fin j => s).map (mix E j)) = cube E j`.

Use extensionality with `y`. Simplify using `only [ZSpan.mem_fundamentalDomain, Basis.map_repr, LinearEquiv.trans_apply, Pi.basis_repr, Sigma.forall]`. Establish `: ∀ a, (∀ i, s.repr ((mix E j).symm y a) i ∈ Set.Ico (0 : ℝ) 1) ↔ ∀ w, (y w a).re ∈ Set.Ico (0 : ℝ) 1 ∧ (y w a).im ∈ Set.Ico (0 : ℝ) 1`. Introduce `a`. Rewrite using `[← ZSpan.mem_fundamentalDomain, hs, ZSpan.mem_fundamentalDomain]`.

Simplify using `only [Sum.forall, Prod.forall, Fin.forall_fin_two, mixedEmbedding.stdBasis_apply_isReal, mixedEmbedding.stdBasis_apply_isComplex_fst, mixedEmbedding.stdBasis_apply_isComplex_snd]`. Prove the components needed by the constructor for the conclusion. Introduce `h w`. Conclude with `h.2 ⟨w, IsTotallyComplex.isComplex w⟩`. Introduce `h`.

Conclude with `⟨fun w => absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1)), fun w => h w.1⟩`. Simplify using `only [this, cube, Set.mem_setOf_eq]`. Conclude with `forall_swap`. Rewrite using `[ZSpan.measureReal_fundamentalDomain _ volume ((Pi.basis fun _ : Fin j => s).map (mix E j)), hc, ← hpi b, ZSpan.measureReal_fundamentalDomain _ volume (Pi.basis fun _ : Fin j => s), hpi s, hs1, Measure.real, volume_cube, Basis.det_map]`. Establish `: (mix E j).symm ∘ ((Pi.basis fun _ : Fin j => b).map (mix E j)) = Pi.basis fun _ : Fin j => b`.

Use function extensionality and compare the values at `fun i => by rw [Function.comp_apply, Basis.map_apply, LinearEquiv.symm_apply_apply]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem volume_fd_map [IsTotallyComplex E] {ι : Type} [Fintype ι] (b : Basis ι ℝ (mixedEmbedding.mixedSpace E)) :
    volume.real (ZSpan.fundamentalDomain ((Pi.basis fun _ : Fin j => b).map (mix E j))) =
      volume.real (ZSpan.fundamentalDomain b) ^ j := by
  haveI : (volume : Measure (Fin j → mixedEmbedding.mixedSpace E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : @BorelSpace (Fin j → mixedEmbedding.mixedSpace E) _ MeasureSpace.toMeasurableSpace := Pi.borelSpace
  have hpi : ∀ {κ : Type} [Fintype κ] (c : Basis κ ℝ (mixedEmbedding.mixedSpace E)),
      volume.real (ZSpan.fundamentalDomain (Pi.basis fun _ : Fin j => c)) =
        volume.real (ZSpan.fundamentalDomain c) ^ j := by
    intro κ _ c
    have : ZSpan.fundamentalDomain (Pi.basis fun _ : Fin j => c) =
        Set.pi Set.univ fun _ => ZSpan.fundamentalDomain c := by
      ext y
      simp only [ZSpan.mem_fundamentalDomain, Pi.basis_repr, Sigma.forall, Set.mem_pi, Set.mem_univ,
        true_implies]
    rw [this, measureReal_def, volume_pi_pi, ENNReal.toReal_prod, measureReal_def]
    simp
  let s := (mixedEmbedding.stdBasis E).reindex ((mixedEmbedding.stdBasis E).indexEquiv b)
  have hs : ZSpan.fundamentalDomain s = ZSpan.fundamentalDomain (mixedEmbedding.stdBasis E) :=
    ZSpan.fundamentalDomain_reindex _ _
  have hs1 : volume.real (ZSpan.fundamentalDomain s) = 1 := by
    rw [hs, Measure.real, mixedEmbedding.volume_fundamentalDomain_stdBasis]; simp
  have hc : ZSpan.fundamentalDomain ((Pi.basis fun _ : Fin j => s).map (mix E j)) = cube E j := by
    ext y
    simp only [ZSpan.mem_fundamentalDomain, Basis.map_repr, LinearEquiv.trans_apply, Pi.basis_repr, Sigma.forall]
    have : ∀ a, (∀ i, s.repr ((mix E j).symm y a) i ∈ Set.Ico (0 : ℝ) 1) ↔
        ∀ w, (y w a).re ∈ Set.Ico (0 : ℝ) 1 ∧ (y w a).im ∈ Set.Ico (0 : ℝ) 1 := by
      intro a
      rw [← ZSpan.mem_fundamentalDomain, hs, ZSpan.mem_fundamentalDomain]
      simp only [Sum.forall, Prod.forall, Fin.forall_fin_two, mixedEmbedding.stdBasis_apply_isReal,
        mixedEmbedding.stdBasis_apply_isComplex_fst, mixedEmbedding.stdBasis_apply_isComplex_snd]
      constructor
      · intro h w
        exact h.2 ⟨w, IsTotallyComplex.isComplex w⟩
      · intro h
        exact ⟨fun w => absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1)),
          fun w => h w.1⟩
    simp only [this, cube, Set.mem_setOf_eq]
    exact forall_swap
  rw [ZSpan.measureReal_fundamentalDomain _ volume ((Pi.basis fun _ : Fin j => s).map (mix E j)), hc,
    ← hpi b, ZSpan.measureReal_fundamentalDomain _ volume (Pi.basis fun _ : Fin j => s), hpi s, hs1,
    Measure.real, volume_cube, Basis.det_map]
  have : (mix E j).symm ∘ ((Pi.basis fun _ : Fin j => b).map (mix E j)) = Pi.basis fun _ : Fin j => b :=
    funext fun i => by rw [Function.comp_apply, Basis.map_apply, LinearEquiv.symm_apply_apply]
  rw [this]
  simp

/- English proof (translation)
Rewrite using `[intB, volume_fd_map, pow_mul]`. Use `congr 1`. Establish `hf : Formalism.HermitianLatticesTheory.fDeg E ≠ 0` using `Fintype.card_ne_zero`. Establish `hc : InfinitePlace.nrComplexPlaces E = Formalism.HermitianLatticesTheory.fDeg E`. Use `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E` as an intermediate fact.

Rewrite `this` using `[IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`. Conclude with `this.symm`. Rewrite using `[Measure.real, mixedEmbedding.volume_fundamentalDomain_latticeBasis, hc, Formalism.HermitianLatticesTheory.vInv, div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]`. Establish `: (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg E) * Formalism.HermitianLatticesTheory.fDeg E = 1 / 2`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this, ← Real.sqrt_eq_rpow]`. Simplify using `[div_eq_inv_mul, Int.norm_eq_abs]`.
-/
theorem volume_fd_intB [IsTotallyComplex E] :
    volume.real (ZSpan.fundamentalDomain (intB E j)) = Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j) := by
  classical
  rw [intB, volume_fd_map, pow_mul]
  congr 1
  have hf : Formalism.HermitianLatticesTheory.fDeg E ≠ 0 := Fintype.card_ne_zero
  have hc : InfinitePlace.nrComplexPlaces E = Formalism.HermitianLatticesTheory.fDeg E := by
    have := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] at this
    exact this.symm
  rw [Measure.real, mixedEmbedding.volume_fundamentalDomain_latticeBasis, hc, Formalism.HermitianLatticesTheory.vInv, div_pow,
    ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  have : (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg E) * Formalism.HermitianLatticesTheory.fDeg E = 1 / 2 := by
    field_simp
  rw [this, ← Real.sqrt_eq_rpow]
  simp [div_eq_inv_mul, Int.norm_eq_abs]

/- English proof (translation)
Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.2 h.fg`. Establish `: Module.Finite ℤ Λ` using `Module.Finite.trans (𝓞 E) Λ`. Conclude with `Module.Finite.iff_fg.1 (this : Module.Finite ℤ (Λ.restrictScalars ℤ))`. Use `span_eq_top := by`. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Establish `hy : y ∈ Submodule.span E (Λ : Set (Fin j → E))` using `by rw [h.span_eq_top]; trivial`. Take `⟨n, c, v, rfl⟩` from `Submodule.mem_span_set'.1 hy`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← (integralBasis E).sum_repr (c i), Finset.sum_smul]`.

Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Rewrite using `[integralBasis_apply, algebraMap_smul]`. Conclude with `Λ.smul_mem _ (v i).2`.
-/
theorem isLattice_int (Λ : Submodule (𝓞 E) (Fin j → E)) (h : Submodule.IsLattice E Λ) :
    Submodule.IsLattice ℚ (Λ.restrictScalars ℤ) where
  fg := by
    have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 h.fg
    have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
    exact Module.Finite.iff_fg.1 (this : Module.Finite ℤ (Λ.restrictScalars ℤ))
  span_eq_top := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Submodule.span E (Λ : Set (Fin j → E)) := by rw [h.span_eq_top]; trivial
    obtain ⟨n, c, v, rfl⟩ := Submodule.mem_span_set'.1 hy
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← (integralBasis E).sum_repr (c i), Finset.sum_smul]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [smul_assoc]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [integralBasis_apply, algebraMap_smul]
    exact Λ.smul_mem _ (v i).2

/- English proof (translation)
Use `haveI := isLattice_int E j Λ h`. Set `β₀` to `Module.Free.chooseBasis ℤ (Λ.restrictScalars ℤ)`. Set `β` to `β₀.reindex (((β₀.extendOfIsLattice ℚ).indexEquiv (ratB E j)).trans ((intB E j).indexEquiv (stdB E j)))`. Set `q` to `β.extendOfIsLattice ℚ`. Establish `hq : ∀ i, q i = (β i : Fin j → E)` using `fun i => Basis.extendOfIsLattice_apply ℚ β i`.

Establish `hall : ∀ y, emb E j y ∈ Submodule.span ℝ (Set.range fun i => emb E j (q i))`. Introduce `y`. Rewrite using `[← q.sum_repr y, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_rat_smul, ← Rat.cast_smul_eq_qsmul ℝ]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => emb E j (q i))`. Rewrite using `[← (intB E j).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[intB_apply]`.

Conclude with `hall _`. Use `⟨basisOfTopLeSpanOfCardEqFinrank _ htop (Module.finrank_eq_card_basis (stdB E j)).symm, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_basisOfTopLeSpanOfCardEqFinrank]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `congrArg Subtype.val (β.sum_repr ⟨y, hy⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul_of_tower] at this`. Rewrite using `[← this, map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← hq]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `⟨q i, by rw [hq]; exact (β i).2, rfl⟩`.
-/
theorem exists_basis [IsTotallyComplex E] (Λ : Submodule (𝓞 E) (Fin j → E)) (h : Submodule.IsLattice E Λ) :
    ∃ b : Basis (Idx E j) ℝ (VecInf E j),
      Submodule.span ℤ (emb E j '' (Λ : Set (Fin j → E))) = Submodule.span ℤ (Set.range b) := by
  classical
  haveI := isLattice_int E j Λ h
  let β₀ := Module.Free.chooseBasis ℤ (Λ.restrictScalars ℤ)
  let β := β₀.reindex (((β₀.extendOfIsLattice ℚ).indexEquiv (ratB E j)).trans ((intB E j).indexEquiv (stdB E j)))
  let q := β.extendOfIsLattice ℚ
  have hq : ∀ i, q i = (β i : Fin j → E) := fun i => Basis.extendOfIsLattice_apply ℚ β i
  have hall : ∀ y, emb E j y ∈ Submodule.span ℝ (Set.range fun i => emb E j (q i)) := by
    intro y
    rw [← q.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_rat_smul, ← Rat.cast_smul_eq_qsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => emb E j (q i)) := by
    rw [← (intB E j).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [intB_apply]
    exact hall _
  refine ⟨basisOfTopLeSpanOfCardEqFinrank _ htop (Module.finrank_eq_card_basis (stdB E j)).symm, ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    have := congrArg Subtype.val (β.sum_repr ⟨y, hy⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul_of_tower] at this
    rw [← this, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul, ← hq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨q i, by rw [hq]; exact (β i).2, rfl⟩

/- English proof (translation)
Use `Submodule.map_span ((act E j fun w => (Matrix.of (g w))⁻¹).restrictScalars ℤ) (emb E j '' (Λ : Set (Fin j → E)))` as an intermediate fact. Establish `h2` using `Submodule.span_eq ((Submodule.span ℤ (emb E j '' (Λ : Set (Fin j → E)))).map ((act E j fun w => (Matrix.of (g w))⁻¹).restrictScalars ℤ))`. Use `Eq.trans ?_ h2.symm` and prove the remaining obligations. Rewrite using `[this, Set.image_image]`. Both sides reduce to the same expression.
-/
theorem latAt_eq_map (Λ : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) :
    latAt E j Λ g = Submodule.span ℤ
      (act E j (fun w => (Matrix.of (g w))⁻¹) '' (Submodule.span ℤ (emb E j '' (Λ : Set (Fin j → E))))) := by
  have := Submodule.map_span ((act E j fun w => (Matrix.of (g w))⁻¹).restrictScalars ℤ)
    (emb E j '' (Λ : Set (Fin j → E)))
  have h2 := Submodule.span_eq ((Submodule.span ℤ (emb E j '' (Λ : Set (Fin j → E)))).map
    ((act E j fun w => (Matrix.of (g w))⁻¹).restrictScalars ℤ))
  refine Eq.trans ?_ h2.symm
  rw [this, Set.image_image]
  rfl

/- English proof (translation)
Establish `h1 : (Matrix.of fun a b : Fin j => if a = b then (1 : ℂ) else 0) = 1` using `rfl`. Establish `h2 : latAt E j (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a 1 : Fin j → E))) (fun _ a b => if a = b then 1 else 0) = Submodule.span ℤ (emb E j '' (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a 1 : Fin j → E)) : Set (Fin j → E)))`. Simplify using `only [latAt, h1, inv_one, Matrix.one_mulVec]`. Both sides reduce to the same expression. Establish `h3 : ∀ a i, ratB E j ⟨a, i⟩ = RingOfIntegers.basis E i • (Pi.single a 1 : Fin j → E)`.

Introduce `a i`. Rewrite using `[ratB, Pi.basis_apply, ← Pi.single_smul, integralBasis_apply, Algebra.smul_def, mul_one]`. Rewrite using `[h2]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hy`. Rewrite using `[map_sum]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← (RingOfIntegers.basis E).sum_repr (c a), Finset.sum_smul, map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc, map_zsmul, ← h3, ← intB_apply]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨a, i⟩, rfl⟩`.

Use `⟨ratB E j ⟨a, i⟩, ?_, (intB_apply E j _).symm⟩` and prove the remaining obligations. Rewrite using `[h3]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem span_std [IsTotallyComplex E] :
    latAt E j (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a 1 : Fin j → E)))
      (fun _ a b => if a = b then 1 else 0) = Submodule.span ℤ (Set.range (intB E j)) := by
  have h1 : (Matrix.of fun a b : Fin j => if a = b then (1 : ℂ) else 0) = 1 := rfl
  have h2 : latAt E j (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a 1 : Fin j → E)))
      (fun _ a b => if a = b then 1 else 0) = Submodule.span ℤ (emb E j ''
        (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a 1 : Fin j → E)) : Set (Fin j → E))) := by
    simp only [latAt, h1, inv_one, Matrix.one_mulVec]
    rfl
  have h3 : ∀ a i, ratB E j ⟨a, i⟩ = RingOfIntegers.basis E i • (Pi.single a 1 : Fin j → E) := by
    intro a i
    rw [ratB, Pi.basis_apply, ← Pi.single_smul, integralBasis_apply, Algebra.smul_def, mul_one]
  rw [h2]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hy
    rw [map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [← (RingOfIntegers.basis E).sum_repr (c a), Finset.sum_smul, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_assoc, map_zsmul, ← h3, ← intB_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · refine Submodule.span_mono ?_
    rintro _ ⟨⟨a, i⟩, rfl⟩
    refine ⟨ratB E j ⟨a, i⟩, ?_, (intB_apply E j _).symm⟩
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Introduce `E _ _ hE j`. Use `⟨fun Λ hΛ => ?_, by rw [span_std, covAt_span, volume_fd_intB]⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `exists_basis E j Λ hΛ`. Use `⟨|(stdB E j).det b|, abs_pos.2 ((stdB E j).isUnit_det b).ne_zero, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hdet : LinearMap.det (act E j fun w => (Matrix.of (g w))⁻¹) ≠ 0`.

Rewrite using `[det_act_inv]`. Conclude with `inv_ne_zero hg.ne'`. Set `T` to `LinearMap.equivOfDetNeZero _ hdet`. Establish `hL : latAt E j Λ g = Submodule.span ℤ (Set.range (b.map T))`. Rewrite using `[latAt_eq_map, hb]`.

Use `Submodule.map_span ((act E j fun w => (Matrix.of (g w))⁻¹).restrictScalars ℤ) (Set.range b)` as an intermediate fact. Establish `h2` using `Submodule.span_eq ((Submodule.span ℤ (Set.range b)).map ((act E j fun w => (Matrix.of (g w))⁻¹).restrictScalars ℤ))`. Use `Eq.trans h2 ?_` and prove the remaining obligations. Rewrite using `[this, ← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[hL]`. Use `⟨⟨inferInstance, inferInstance⟩, ?_, covAt_dual E j _, dual_dual E j _⟩` and prove the remaining obligations. Establish `h4 : ⇑(b.map T) = (act E j fun w => (Matrix.of (g w))⁻¹) ∘ b` using `rfl`. Rewrite using `[covAt_span_std, h4, Basis.det_comp, det_act_inv, abs_mul, abs_of_pos (inv_pos.2 hg), div_eq_inv_mul]`.
-/
theorem lattice_facts : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, (∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∃ κ : ℝ, 0 < κ ∧ ∀ g : MatInf E j, 0 < detNorm E j g → (∃ _ : DiscreteTopology (latAt E j Λ g), IsZLattice ℝ (latAt E j Λ g)) ∧ covAt E j (latAt E j Λ g) = κ / detNorm E j g ∧ covAt E j (dualAt E j (latAt E j Λ g)) = (covAt E j (latAt E j Λ g))⁻¹ ∧ dualAt E j (dualAt E j (latAt E j Λ g)) = latAt E j Λ g) ∧ covAt E j (latAt E j (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a 1 : Fin j → E))) fun _ a b => if a = b then 1 else 0) = Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j) := by
  intro E _ _ hE j
  refine ⟨fun Λ hΛ => ?_, by rw [span_std, covAt_span, volume_fd_intB]⟩
  classical
  obtain ⟨b, hb⟩ := exists_basis E j Λ hΛ
  refine ⟨|(stdB E j).det b|, abs_pos.2 ((stdB E j).isUnit_det b).ne_zero, fun g hg => ?_⟩
  have hdet : LinearMap.det (act E j fun w => (Matrix.of (g w))⁻¹) ≠ 0 := by
    rw [det_act_inv]; exact inv_ne_zero hg.ne'
  let T := LinearMap.equivOfDetNeZero _ hdet
  have hL : latAt E j Λ g = Submodule.span ℤ (Set.range (b.map T)) := by
    rw [latAt_eq_map, hb]
    have := Submodule.map_span ((act E j fun w => (Matrix.of (g w))⁻¹).restrictScalars ℤ) (Set.range b)
    have h2 := Submodule.span_eq ((Submodule.span ℤ (Set.range b)).map
      ((act E j fun w => (Matrix.of (g w))⁻¹).restrictScalars ℤ))
    refine Eq.trans h2 ?_
    rw [this, ← Set.range_comp]
    rfl
  rw [hL]
  refine ⟨⟨inferInstance, inferInstance⟩, ?_, covAt_dual E j _, dual_dual E j _⟩
  have h4 : ⇑(b.map T) = (act E j fun w => (Matrix.of (g w))⁻¹) ∘ b := rfl
  rw [covAt_span_std, h4, Basis.det_comp, det_act_inv, abs_mul, abs_of_pos (inv_pos.2 hg), div_eq_inv_mul]

end GlobalTheory.LatFacts
