import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NsmulApplyMemOfMemTensorLat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IntegrableOnFundamentalDomainOfContinuous

namespace GlobalTheory.TensorLat

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)

/- English proof (translation)
Establish `hM0 : (M : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Establish `h2' : ∀ x ∈ L, (M : ℝ) • x ∈ Submodule.span ℤ (Set.range b)`. Introduce `x hx`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `h2 x hx`.

Set `f : L → Submodule.span ℤ (Set.range b)` to `fun x => ⟨(M : ℝ) • (x : V), h2' x x.2⟩`. Establish `hfc : Continuous f` using `(continuous_const.smul continuous_subtype_val).subtype_mk _`. Establish `hfi : Function.Injective f`. Introduce `x y h`. Establish `h' : (M : ℝ) • (x : V) = (M : ℝ) • (y : V)` using `congrArg Subtype.val h`.

Conclude with `Subtype.ext (smul_right_injective V hM0 h')`. Establish `: DiscreteTopology L` using `DiscreteTopology.of_continuous_injective hfc hfi`. Establish `: IsZLattice ℝ L`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← b.span_eq, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hm : M • b i ∈ L` using `h1 (b i) (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hbi : b i = (M : ℝ)⁻¹ • (M • b i)`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hM0, one_smul]`. Rewrite using `[SetLike.mem_coe, hbi]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hm)`. Use `ZLattice.module_free ℝ L` as an intermediate fact. Use `ZLattice.module_finite ℝ L` as an intermediate fact. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Fintype.card κ`. Rewrite using `[← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, Module.finrank_eq_card_basis b]`.

Conclude with `⟨((Module.Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard)).ofZLatticeBasis ℝ L, Module.Basis.ofZLatticeBasis_span ℝ L _⟩`.
-/
theorem exists_basis_span_eq_of_commensurable {V κ : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Fintype κ] (b : Module.Basis κ ℝ V)
    (L : Submodule ℤ V) {M : ℕ} (hM : 1 ≤ M)
    (h1 : ∀ x ∈ Submodule.span ℤ (Set.range b), M • x ∈ L)
    (h2 : ∀ x ∈ L, M • x ∈ Submodule.span ℤ (Set.range b)) :
    ∃ b' : Module.Basis κ ℝ V, Submodule.span ℤ (Set.range b') = L := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2' : ∀ x ∈ L, (M : ℝ) • x ∈ Submodule.span ℤ (Set.range b) := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact h2 x hx
  let f : L → Submodule.span ℤ (Set.range b) := fun x => ⟨(M : ℝ) • (x : V), h2' x x.2⟩
  have hfc : Continuous f := (continuous_const.smul continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := by
    intro x y h
    have h' : (M : ℝ) • (x : V) = (M : ℝ) • (y : V) := congrArg Subtype.val h
    exact Subtype.ext (smul_right_injective V hM0 h')
  have : DiscreteTopology L := DiscreteTopology.of_continuous_injective hfc hfi
  have : IsZLattice ℝ L := by
    refine ⟨?_⟩
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hm : M • b i ∈ L := h1 (b i) (Submodule.subset_span ⟨i, rfl⟩)
    have hbi : b i = (M : ℝ)⁻¹ • (M • b i) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    rw [SetLike.mem_coe, hbi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
  have := ZLattice.module_free ℝ L
  have := ZLattice.module_finite ℝ L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Fintype.card κ := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L,
      Module.finrank_eq_card_basis b]
  exact ⟨((Module.Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard)).ofZLatticeBasis ℝ L,
    Module.Basis.ofZLatticeBasis_span ℝ L _⟩

/- English proof (translation)
Establish `hme : MeasurableEmbedding e` using `e.toHomeomorph.measurableEmbedding`. Establish `key : ∀ t : Set W, ⨍ v in e ⁻¹' t, f (e v) ∂μ = ⨍ w in t, f w ∂(μ.map e)`. Introduce `t`. Rewrite using `[average_eq, average_eq, hme.restrict_map μ t, hme.integral_map]`. Use `congr 2`.

Rewrite using `[measureReal_def, measureReal_def, Measure.map_apply hme.measurable MeasurableSet.univ, Set.preimage_univ]`. Rewrite using `[key s]`. Establish `hc` using `Measure.isAddLeftInvariant_eq_smul (μ.map e) ν`. Establish `hpos` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) ν`. Use `set c := Measure.addHaarScalarFactor (μ.map e) ν`.

Establish `hc0 : (c : ℝ) ≠ 0` using `by exact_mod_cast hpos.ne'`. Rewrite using `[hc, average_eq, average_eq, Measure.restrict_smul, integral_smul_nnreal_measure, measureReal_nnreal_smul_apply, NNReal.smul_def, smul_smul]`. Use `congr 1`. Rewrite using `[mul_inv, mul_comm (c : ℝ)⁻¹, mul_assoc, inv_mul_cancel₀ hc0, mul_one]`.
-/
theorem setAverage_comp_equiv {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
    [BorelSpace W] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure W) [ν.IsAddHaarMeasure]
    (e : V ≃L[ℝ] W) (s : Set W) (f : W → F) :
    ⨍ w in s, f w ∂ν = ⨍ v in e ⁻¹' s, f (e v) ∂μ := by
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have key : ∀ t : Set W, ⨍ v in e ⁻¹' t, f (e v) ∂μ = ⨍ w in t, f w ∂(μ.map e) := by
    intro t
    rw [average_eq, average_eq, hme.restrict_map μ t, hme.integral_map]
    congr 2
    rw [measureReal_def, measureReal_def, Measure.map_apply hme.measurable MeasurableSet.univ,
      Set.preimage_univ]
  rw [key s]
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map e) ν
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) ν
  set c := Measure.addHaarScalarFactor (μ.map e) ν
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [hc, average_eq, average_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply, NNReal.smul_def, smul_smul]
  congr 1
  rw [mul_inv, mul_comm (c : ℝ)⁻¹, mul_assoc, inv_mul_cancel₀ hc0, mul_one]

variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `v`. Establish `e1 : Hf v (flat a) = HC (flat.symm v) a`. Rewrite using `[← HC_flat_symm v (flat a), ContinuousLinearEquiv.symm_apply_apply]`. Simplify using `only [hU, Function.comp, PT.U, e1, Hf_flat, map_sub, ContinuousLinearEquiv.symm_apply_apply]`.
-/
theorem translate_comp_flat_symm (X : PT E)
    (U : ℕ → EuclideanSpace ℂ (Fin n × Idx X.dim) → (EuclideanSpace ℂ (Fin n × Idx X.dim) → ℂ) →
      EuclideanSpace ℂ (Fin n × Idx X.dim) → ℂ)
    (hU : ∀ (q : ℕ) a F v,
      U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (q : ℕ) (a : Fin n → Vsp X.dim) (F : (Fin n → Vsp X.dim) → ℂ) :
    U q (flat a) (F ∘ flat.symm) = X.U q a F ∘ flat.symm := by
  funext v
  have e1 : Hf v (flat a) = HC (flat.symm v) a := by
    rw [← HC_flat_symm v (flat a), ContinuousLinearEquiv.symm_apply_apply]
  simp only [hU, Function.comp, PT.U, e1, Hf_flat, map_sub, ContinuousLinearEquiv.symm_apply_apply]

open Classical in

/- English proof (translation)
Establish `hd : ∀ l : Letter n dim, (flat (n` using `n) (ι := Idx dim)).symm (EuclideanSpace.single l 1) = dir l := fun l => by`. Rewrite using `[← flat_dir, ContinuousLinearEquiv.symm_apply_apply]`. Establish `hit : ∀ (i : ℕ) (x : EuclideanSpace ℂ (Fin n × Idx dim)), iteratedFDeriv ℂ i (F ∘ (flat (n` using `n) (ι := Idx dim)).symm) x = (iteratedFDeriv ℂ i F ((flat (n := n) (ι := Idx dim)).symm x)).compContinuousLinearMap fun _ => ((flat (n := n) (ι := Idx dim)).symm : EuclideanSpace ℂ (Fin n × Idx dim) →L[ℂ] (Fin n → Vsp dim)) := by`. Introduce `i x`. Establish `h` using `(flat (n := n) (ι := Idx dim)).symm.iteratedFDerivWithin_comp_right F (uniqueDiffOn_univ (𝕜 := ℂ)) (x := x) (Set.mem_univ _) i`.

Simplify `h` using `only [Set.preimage_univ, iteratedFDerivWithin_univ]`. Unfold `polyDeriv`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[hit, ContinuousLinearEquiv.symm_apply_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]`.

Simplify using `only [ContinuousLinearEquiv.coe_coe, hd]`.
-/
theorem polyDeriv_comp_flat_symm (P : MvPolynomial (Letter n dim) ℂ)
    (F : (Fin n → Vsp dim) → ℂ) (v : Fin n → Vsp dim) :
    polyDeriv P (fun l => EuclideanSpace.single l 1) (F ∘ flat.symm) (flat v) =
      polyDeriv P dir F v := by
  have hd : ∀ l : Letter n dim,
      (flat (n := n) (ι := Idx dim)).symm (EuclideanSpace.single l 1) = dir l := fun l => by
    rw [← flat_dir, ContinuousLinearEquiv.symm_apply_apply]
  have hit : ∀ (i : ℕ) (x : EuclideanSpace ℂ (Fin n × Idx dim)),
      iteratedFDeriv ℂ i (F ∘ (flat (n := n) (ι := Idx dim)).symm) x =
        (iteratedFDeriv ℂ i F ((flat (n := n) (ι := Idx dim)).symm x)).compContinuousLinearMap
          fun _ => ((flat (n := n) (ι := Idx dim)).symm :
            EuclideanSpace ℂ (Fin n × Idx dim) →L[ℂ] (Fin n → Vsp dim)) := by
    intro i x
    have h := (flat (n := n) (ι := Idx dim)).symm.iteratedFDerivWithin_comp_right F
      (uniqueDiffOn_univ (𝕜 := ℂ)) (x := x) (Set.mem_univ _) i
    simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using h
  unfold polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [hit, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, hd]

/- English proof (translation)
Simplify using `only [GT.ptN2, PT.ptN2, Function.comp, ContinuousLinearEquiv.symm_apply_apply, HC_self_re]`.
-/
theorem pointwiseNorm_comp_flatten_symm_eq (X : PT E) (Y : GT (Fin n × Idx X.dim)) (q : ℕ)
    (F : (Fin n → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim) :
    Y.ptN2 q (F ∘ flat.symm) (flat v) = X.ptN2 q F v := by
  simp only [GT.ptN2, PT.ptN2, Function.comp, ContinuousLinearEquiv.symm_apply_apply, HC_self_re]

/- English proof (translation)
Establish `hper : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → ∀ v, X.ptN2 q F (v + γ) = X.ptN2 q F v`. Introduce `γ hγ v`. Establish `hFv` using `hF.2 γ hγ v`. Establish `heps : ‖(∏ k, (X.eps (γ k) : ℂ))‖ = 1`. Rewrite using `[norm_prod]`.

Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases X.eps_pm _ (hγ k) with h | h <;> simp [h]`. Establish `hre : (HC (v + γ) (v + γ)).re = (HC v v).re + 2 * (HC v γ).re + (HC γ γ).re`. Rewrite using `[HC_add_left, HC_add_right, HC_add_right, HC_conj v γ]`. Simplify using `only [Complex.add_re, Complex.conj_re]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsq : ∀ a b c : ℝ, (Real.exp a * c) ^ 2 * Real.exp b = c ^ 2 * Real.exp (2 * a + b)`. Introduce `a b c`. Rewrite using `[show 2 * a + b = a + a + b by ring, Real.exp_add, Real.exp_add]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `PT.ptN2`. Rewrite using `[hFv, norm_mul, norm_mul, norm_pow, heps, one_pow, one_mul, Complex.norm_exp, hsq, hre]`. Use `congr 2`. Simplify using `only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re, mul_zero, zero_mul, sub_zero, add_zero]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hlat : lat Y.b = lat (TiledBoundaries.bT X n)`. Use extensionality with `w`. Establish `h` using `hY (flat.symm w)`. Rewrite `h` using `[ContinuousLinearEquiv.apply_symm_apply]`. Rewrite using `[h, TiledBoundaries.mem_latT, ← flat_symm_eq_eT_symm]`.

Establish `hg : ∀ v, Y.ptN2 q (F ∘ flat.symm) (flat v) = X.ptN2 q F v` using `pointwiseNorm_comp_flatten_symm_eq X Y q F`. Establish `hgc : Continuous (Y.ptN2 q (F ∘ flat.symm))`. Establish `hFc : Continuous F` using `hF.1.continuous`. Unfold `GT.ptN2`. Conclude with `((hFc.comp flat.symm.continuous).norm.pow 2).mul (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))`.

Establish `hgper : ∀ γ ∈ lat Y.b, ∀ w, Y.ptN2 q (F ∘ flat.symm) (w + γ) = Y.ptN2 q (F ∘ flat.symm) w`. Introduce `γ hγ w`. Establish `hγ' : ∀ k, flat.symm γ k ∈ X.L`. Rewrite using `[← hY, ContinuousLinearEquiv.apply_symm_apply]`. Conclude with `hγ`.

Establish `h` using `hper (flat.symm γ) hγ' (flat.symm w)`. Rewrite `h` using `[← hg, ← hg, map_add, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]`. Conclude with `h`. Establish `h1 : Y.l2 q (F ∘ flat.symm) = ⨍ w in ZSpan.fundamentalDomain (TiledBoundaries.bT X n), Y.ptN2 q (F ∘ flat.symm) w`. Establish `h` using `average_fundamentalDomain_eq_real volume Y.b (TiledBoundaries.bT X n) (Y.ptN2 q (F ∘ flat.symm)) hgc hgper hlat.symm.le 0`.

Simplify using `only [add_zero] at h`. Rewrite using `[GT.l2]`. Conclude with `h.symm`. Set `e : (Fin n → Vsp X.dim) ≃L[ℝ] EuclideanSpace ℂ (Fin n × Idx X.dim)` to `{ toLinearEquiv := (flat (n := n) (ι := Idx X.dim)).toLinearEquiv.restrictScalars ℝ continuous_toFun := (flat (n := n) (ι := Idx X.dim)).continuous continuous_invFun := (flat (n := n) (ι := Idx X.dim)).symm.continuous }`. Establish `hpre : e ⁻¹' ZSpan.fundamentalDomain (TiledBoundaries.bT X n) = X.fd n`.

Rewrite using `[TiledBoundaries.fd_eq]`. Unfold `TiledBoundaries.bT`. Rewrite using `[ZSpan.fundamentalDomain_reindex, ← ZSpan.map_fundamentalDomain]`. Use extensionality with `v`. Rewrite using `[Set.mem_preimage, show e v = ((TiledBoundaries.eT X n).restrictScalars ℝ) v from flat_eq_eT X v]`.

Conclude with `(LinearEquiv.injective _).mem_set_image`. Rewrite using `[h1, setAverage_comp_equiv (volume : Measure (Fin n → Vsp X.dim)) volume e, hpre, PT.l2]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `hg v`.
-/
theorem l2_comp_flat_symm_eq_l2 (X : PT E) (Y : GT (Fin n × Idx X.dim))
    (hY : ∀ γ, flat γ ∈ lat Y.b ↔ ∀ k, γ k ∈ X.L) (q : ℕ) {F : (Fin n → Vsp X.dim) → ℂ}
    (hF : F ∈ X.Sec q n) : Y.l2 q (F ∘ flat.symm) = X.l2 q F := by
  have hper : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → ∀ v,
      X.ptN2 q F (v + γ) = X.ptN2 q F v := by
    intro γ hγ v
    have hFv := hF.2 γ hγ v
    have heps : ‖(∏ k, (X.eps (γ k) : ℂ))‖ = 1 := by
      rw [norm_prod]
      refine Finset.prod_eq_one fun k _ => ?_
      rcases X.eps_pm _ (hγ k) with h | h <;> simp [h]
    have hre : (HC (v + γ) (v + γ)).re = (HC v v).re + 2 * (HC v γ).re + (HC γ γ).re := by
      rw [HC_add_left, HC_add_right, HC_add_right, HC_conj v γ]
      simp only [Complex.add_re, Complex.conj_re]
      ring
    have hsq : ∀ a b c : ℝ, (Real.exp a * c) ^ 2 * Real.exp b = c ^ 2 * Real.exp (2 * a + b) := by
      intro a b c
      rw [show 2 * a + b = a + a + b by ring, Real.exp_add, Real.exp_add]
      ring
    unfold PT.ptN2
    rw [hFv, norm_mul, norm_mul, norm_pow, heps, one_pow, one_mul, Complex.norm_exp, hsq, hre]
    congr 2
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re, mul_zero,
      zero_mul, sub_zero, add_zero]
    ring
  have hlat : lat Y.b = lat (TiledBoundaries.bT X n) := by
    ext w
    have h := hY (flat.symm w)
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    rw [h, TiledBoundaries.mem_latT, ← flat_symm_eq_eT_symm]
  have hg : ∀ v, Y.ptN2 q (F ∘ flat.symm) (flat v) = X.ptN2 q F v :=
    pointwiseNorm_comp_flatten_symm_eq X Y q F
  have hgc : Continuous (Y.ptN2 q (F ∘ flat.symm)) := by
    have hFc : Continuous F := hF.1.continuous
    unfold GT.ptN2
    exact ((hFc.comp flat.symm.continuous).norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hgper : ∀ γ ∈ lat Y.b, ∀ w,
      Y.ptN2 q (F ∘ flat.symm) (w + γ) = Y.ptN2 q (F ∘ flat.symm) w := by
    intro γ hγ w
    have hγ' : ∀ k, flat.symm γ k ∈ X.L := by
      rw [← hY, ContinuousLinearEquiv.apply_symm_apply]
      exact hγ
    have h := hper (flat.symm γ) hγ' (flat.symm w)
    rw [← hg, ← hg, map_add, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply] at h
    exact h
  have h1 : Y.l2 q (F ∘ flat.symm) =
      ⨍ w in ZSpan.fundamentalDomain (TiledBoundaries.bT X n), Y.ptN2 q (F ∘ flat.symm) w := by
    have h := average_fundamentalDomain_eq_real volume Y.b (TiledBoundaries.bT X n)
      (Y.ptN2 q (F ∘ flat.symm)) hgc hgper hlat.symm.le 0
    simp only [add_zero] at h
    rw [GT.l2]
    exact h.symm
  let e : (Fin n → Vsp X.dim) ≃L[ℝ] EuclideanSpace ℂ (Fin n × Idx X.dim) :=
    { toLinearEquiv := (flat (n := n) (ι := Idx X.dim)).toLinearEquiv.restrictScalars ℝ
      continuous_toFun := (flat (n := n) (ι := Idx X.dim)).continuous
      continuous_invFun := (flat (n := n) (ι := Idx X.dim)).symm.continuous }
  have hpre : e ⁻¹' ZSpan.fundamentalDomain (TiledBoundaries.bT X n) = X.fd n := by
    rw [TiledBoundaries.fd_eq]
    unfold TiledBoundaries.bT
    rw [ZSpan.fundamentalDomain_reindex, ← ZSpan.map_fundamentalDomain]
    ext v
    rw [Set.mem_preimage, show e v = ((TiledBoundaries.eT X n).restrictScalars ℝ) v from flat_eq_eT X v]
    exact (LinearEquiv.injective _).mem_set_image
  rw [h1, setAverage_comp_equiv (volume : Measure (Fin n → Vsp X.dim)) volume e, hpre, PT.l2]
  congr 1
  funext v
  exact hg v

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hG`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hG.1.comp (flat (n := n) (ι := Idx X.dim)).differentiable`. Simplify `h` using `[Function.comp_def]`.

Introduce `γ hγ v`. Establish `h` using `hG.2 (flat γ) ((hY γ).2 hγ) (flat v)`. Simplify using `only [Function.comp, ← map_add, ContinuousLinearEquiv.symm_apply_apply, hka γ hγ, Hf_flat] at h`. Conclude with `h`. Introduce `hF`.

Use `⟨hF.1.comp (flat (n := n) (ι := Idx X.dim)).symm.differentiable, ?_⟩` and prove the remaining obligations. Introduce `γ' hγ' w`. Establish `hγ : ∀ k, flat.symm γ' k ∈ X.L`. Rewrite using `[← hY, ContinuousLinearEquiv.apply_symm_apply]`. Conclude with `hγ'`.

Establish `h` using `hF.2 _ hγ (flat.symm w)`. Establish `hk` using `hka _ hγ`. Rewrite `hk` using `[ContinuousLinearEquiv.apply_symm_apply]`. Simplify using `only [Function.comp, map_add, hk]`. Rewrite using `[h, HC_flat_symm, HC_flat_symm]`.
-/
theorem comp_flat_symm_mem_sec_iff (X : PT E) (Y : GT (Fin n × Idx X.dim))
    (hY : ∀ γ, flat γ ∈ lat Y.b ↔ ∀ k, γ k ∈ X.L) (q : ℕ)
    (hka : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) →
      Y.ka (flat γ) = (∏ k, (X.eps (γ k) : ℂ)) ^ q)
    (F : (Fin n → Vsp X.dim) → ℂ) : F ∘ flat.symm ∈ Y.Sec q ↔ F ∈ X.Sec q n := by
  constructor
  · intro hG
    refine ⟨?_, ?_⟩
    · have h := hG.1.comp (flat (n := n) (ι := Idx X.dim)).differentiable
      simpa [Function.comp_def] using h
    · intro γ hγ v
      have h := hG.2 (flat γ) ((hY γ).2 hγ) (flat v)
      simp only [Function.comp, ← map_add, ContinuousLinearEquiv.symm_apply_apply, hka γ hγ,
        Hf_flat] at h
      exact h
  · intro hF
    refine ⟨hF.1.comp (flat (n := n) (ι := Idx X.dim)).symm.differentiable, ?_⟩
    intro γ' hγ' w
    have hγ : ∀ k, flat.symm γ' k ∈ X.L := by
      rw [← hY, ContinuousLinearEquiv.apply_symm_apply]
      exact hγ'
    have h := hF.2 _ hγ (flat.symm w)
    have hk := hka _ hγ
    rw [ContinuousLinearEquiv.apply_symm_apply] at hk
    simp only [Function.comp, map_add, hk]
    rw [h, HC_flat_symm, HC_flat_symm]

variable [IsCMField E]

/- English proof (translation)
Establish `hact : ∀ v : Vsp dim, act w₀ v = actE (w₀ : E) v` using `fun v => (actE_coe w₀ v).symm`. Simplify using `only [hact]`. Establish `hsplit : (fun k => actE (w₀ : E) ((γ + δ) k)) = (fun k => actE (w₀ : E) (γ k)) + (fun k => actE (w₀ : E) (δ k))`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, actE_add_right]`.

Establish `h1 : HC δ (fun k => actE (w₀ : E) (γ k)) = starRingEnd ℂ (HC γ (fun k => actE (cc (w₀ : E)) (δ k)))`. Rewrite using `[HC_conj (fun k => actE (w₀ : E) (γ k)) δ, HC_actE]`. Establish `h3 : HC γ δ = HC γ (fun k => actE (cc (w₀ : E)) (δ k)) + HC γ (fun k => actE (w₀ : E) (δ k))`. Rewrite using `[← HC_add_right]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[Pi.add_apply, ← actE_add_left, show cc (w₀ : E) + w₀ = 1 by rw [add_comm]; exact hw, actE_one]`. Rewrite using `[hsplit, HC_add_left, HC_add_right, HC_add_right, h1]`. Establish `h3'` using `congrArg Complex.im h3`. Simplify using `only [Complex.add_im] at h3'`.

Simplify using `only [Complex.add_im, Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem im_HC_act_add (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1) (γ δ : Fin n → Vsp dim) :
    (HC (γ + δ) fun k => act w₀ ((γ + δ) k)).im =
      (HC γ fun k => act w₀ (γ k)).im + (HC δ fun k => act w₀ (δ k)).im +
        (2 * (HC γ fun k => act w₀ (δ k)).im - (HC γ δ).im) := by
  have hact : ∀ v : Vsp dim, act w₀ v = actE (w₀ : E) v := fun v => (actE_coe w₀ v).symm
  simp only [hact]
  have hsplit : (fun k => actE (w₀ : E) ((γ + δ) k)) =
      (fun k => actE (w₀ : E) (γ k)) + (fun k => actE (w₀ : E) (δ k)) := by
    funext k
    simp only [Pi.add_apply, actE_add_right]
  have h1 : HC δ (fun k => actE (w₀ : E) (γ k)) =
      starRingEnd ℂ (HC γ (fun k => actE (cc (w₀ : E)) (δ k))) := by
    rw [HC_conj (fun k => actE (w₀ : E) (γ k)) δ, HC_actE]
  have h3 : HC γ δ = HC γ (fun k => actE (cc (w₀ : E)) (δ k)) +
      HC γ (fun k => actE (w₀ : E) (δ k)) := by
    rw [← HC_add_right]
    congr 1
    funext k
    rw [Pi.add_apply, ← actE_add_left, show cc (w₀ : E) + w₀ = 1 by rw [add_comm]; exact hw,
      actE_one]
  rw [hsplit, HC_add_left, HC_add_right, HC_add_right, h1]
  have h3' := congrArg Complex.im h3
  simp only [Complex.add_im] at h3'
  simp only [Complex.add_im, Complex.conj_im]
  linarith

variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}

/- English proof (translation)
Take `⟨m, hm⟩` from `im_HC_int hfg hint hdual hγ (act_mem_tensorLat w₀ hγ)`. Rewrite using `[tensorEps_of_int w₀ γ m hm, ← zpow_natCast, ← zpow_mul]`. Conclude with `Even.neg_one_zpow ⟨m, by push_cast; ring⟩`.
-/
theorem tensorEps_sq_of_mem (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') (w₀ : 𝓞 E)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') : tensorEps w₀ γ ^ 2 = 1 := by
  obtain ⟨m, hm⟩ := im_HC_int hfg hint hdual hγ (act_mem_tensorLat w₀ hγ)
  rw [tensorEps_of_int w₀ γ m hm, ← zpow_natCast, ← zpow_mul]
  exact Even.neg_one_zpow ⟨m, by push_cast; ring⟩

/- English proof (translation)
Unfold `tensorEps`. Rewrite using `[im_HC_act_add w₀ hw γ δ]`. Take `⟨c, hc⟩` from `im_HC_int hfg hint hdual hγ (act_mem_tensorLat w₀ hδ)`. Take `⟨d, hd⟩` from `im_HC_int hfg hint hdual hγ hδ`. Rewrite using `[hc, hd, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]`.

Use `⟨c - d, ?_⟩` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tensorEps_add_of_mem (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') (w₀ : 𝓞 E)
    (hw : (w₀ : E) + cc (w₀ : E) = 1) {γ δ : Fin n → Vsp X.dim}
    (hγ : γ ∈ tensorLat X Λ') (hδ : δ ∈ tensorLat X Λ') :
    tensorEps w₀ (γ + δ) =
      tensorEps w₀ γ * tensorEps w₀ δ * cexp (Real.pi * I * (HC γ δ).im) := by
  unfold tensorEps
  rw [im_HC_act_add w₀ hw γ δ]
  obtain ⟨c, hc⟩ := im_HC_int hfg hint hdual hγ (act_mem_tensorLat w₀ hδ)
  obtain ⟨d, hd⟩ := im_HC_int hfg hint hdual hγ hδ
  rw [hc, hd, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨c - d, ?_⟩
  push_cast
  ring

/- English proof (translation)
Take `⟨M, hM, hM1, hM2⟩` from `exists_nsmul_commensurable (X := X) hfg hint hdual`. Set `L : Submodule ℤ (EuclideanSpace ℂ (Fin n × Idx X.dim))` to `(tensorLat X Λ').map (((flat (n := n) (ι := Idx X.dim)).toLinearEquiv.restrictScalars ℤ : _ ≃ₗ[ℤ] _) : (Fin n → Vsp X.dim) →ₗ[ℤ] EuclideanSpace ℂ (Fin n × Idx X.dim))`. Establish `hmemL : ∀ γ, flat γ ∈ L ↔ γ ∈ tensorLat X Λ'`. Introduce `γ`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨γ', hγ', h⟩`. Establish `hγγ : γ' = γ` using `flat.injective h`. Rewrite using `[← hγγ]`. Conclude with `hγ'`. Introduce `h`.

Conclude with `⟨γ, h, rfl⟩`. Establish `hlatT : ∀ w, w ∈ lat (TiledBoundaries.bT X n) ↔ ∀ k, flat.symm w k ∈ X.L`. Introduce `w`. Rewrite using `[TiledBoundaries.mem_latT, flat_symm_eq_eT_symm]`. Establish `h1 : ∀ x ∈ Submodule.span ℤ (Set.range (TiledBoundaries.bT X n)), M • x ∈ L`.

Introduce `x hx`. Establish `h` using `hM1 _ ((hlatT x).1 hx)`. Rewrite using `[← ContinuousLinearEquiv.apply_symm_apply flat x, ← map_nsmul]`. Conclude with `(hmemL _).2 h`. Establish `h2 : ∀ x ∈ L, M • x ∈ Submodule.span ℤ (Set.range (TiledBoundaries.bT X n))`.

Introduce and unpack `x ⟨γ, hγ, rfl⟩`. Use `(hlatT _).2 fun k => ?_` and prove the remaining obligations. Establish `hfl : (((flat (n` using `n) (ι := Idx X.dim)).toLinearEquiv.restrictScalars ℤ : _ ≃ₗ[ℤ] _) : (Fin n → Vsp X.dim) →ₗ[ℤ] EuclideanSpace ℂ (Fin n × Idx X.dim)) γ = flat γ := rfl`. Rewrite using `[hfl, ← map_nsmul, ContinuousLinearEquiv.symm_apply_apply]`. Conclude with `hM2 γ hγ k`.

Take `⟨b', hb'⟩` from `exists_basis_span_eq_of_commensurable (TiledBoundaries.bT X n) L hM h1 h2`. Use `⟨b', fun γ => ?_⟩` and prove the remaining obligations. Use `show flat γ ∈ Submodule.span ℤ (Set.range b') ↔ _`. Rewrite using `[hb', hmemL]`.
-/
theorem exists_basis_tensorLat (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    ∃ b : Module.Basis (Fin (2 * Fintype.card (Fin n × Idx X.dim))) ℝ
        (EuclideanSpace ℂ (Fin n × Idx X.dim)),
      ∀ γ, flat γ ∈ lat b ↔ γ ∈ tensorLat X Λ' := by
  obtain ⟨M, hM, hM1, hM2⟩ := exists_nsmul_commensurable (X := X) hfg hint hdual
  let L : Submodule ℤ (EuclideanSpace ℂ (Fin n × Idx X.dim)) :=
    (tensorLat X Λ').map
      (((flat (n := n) (ι := Idx X.dim)).toLinearEquiv.restrictScalars ℤ : _ ≃ₗ[ℤ] _) :
        (Fin n → Vsp X.dim) →ₗ[ℤ] EuclideanSpace ℂ (Fin n × Idx X.dim))
  have hmemL : ∀ γ, flat γ ∈ L ↔ γ ∈ tensorLat X Λ' := by
    intro γ
    constructor
    · rintro ⟨γ', hγ', h⟩
      have hγγ : γ' = γ := flat.injective h
      rw [← hγγ]
      exact hγ'
    · intro h
      exact ⟨γ, h, rfl⟩
  have hlatT : ∀ w, w ∈ lat (TiledBoundaries.bT X n) ↔ ∀ k, flat.symm w k ∈ X.L := by
    intro w
    rw [TiledBoundaries.mem_latT, flat_symm_eq_eT_symm]
  have h1 : ∀ x ∈ Submodule.span ℤ (Set.range (TiledBoundaries.bT X n)), M • x ∈ L := by
    intro x hx
    have h := hM1 _ ((hlatT x).1 hx)
    rw [← ContinuousLinearEquiv.apply_symm_apply flat x, ← map_nsmul]
    exact (hmemL _).2 h
  have h2 : ∀ x ∈ L, M • x ∈ Submodule.span ℤ (Set.range (TiledBoundaries.bT X n)) := by
    rintro x ⟨γ, hγ, rfl⟩
    refine (hlatT _).2 fun k => ?_
    have hfl : (((flat (n := n) (ι := Idx X.dim)).toLinearEquiv.restrictScalars ℤ : _ ≃ₗ[ℤ] _) :
        (Fin n → Vsp X.dim) →ₗ[ℤ] EuclideanSpace ℂ (Fin n × Idx X.dim)) γ = flat γ := rfl
    rw [hfl, ← map_nsmul, ContinuousLinearEquiv.symm_apply_apply]
    exact hM2 γ hγ k
  obtain ⟨b', hb'⟩ := exists_basis_span_eq_of_commensurable (TiledBoundaries.bT X n) L hM h1 h2
  refine ⟨b', fun γ => ?_⟩
  show flat γ ∈ Submodule.span ℤ (Set.range b') ↔ _
  rw [hb', hmemL]

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_basis_tensorLat (X := X) hfg hint hdual`. Establish `hmem : ∀ x, x ∈ lat b ↔ flat.symm x ∈ tensorLat X Λ'` using `fun x => by`. Rewrite using `[← hb, ContinuousLinearEquiv.apply_symm_apply]`. Set `g : tensorLat X Λ' →+ lat b` to `{ toFun := fun γ => ⟨flat (γ : Fin n → Vsp X.dim), (hb γ).2 γ.2⟩ map_zero' := by`. Use `ext`.

Simplify using the standard rewrite rules. Use the proof step `map_add' := fun x y => by`. Use `ext`. Simplify using `}`. Use `⟨⟨b, ?_, ?_, fun x => tensorEps w₀ (flat.symm x), ?_⟩, hb, ?_⟩` and prove the remaining obligations.

Introduce `x y hx hy`. Rewrite using `[← HC_flat_symm]`. Conclude with `im_HC_int hfg hint hdual ((hmem x).1 hx) ((hmem y).1 hy)`. Introduce `φ`. Take `⟨γ0, hγ0, hφ⟩` from `exists_im_HC_eq hfg hint hdual (φ.comp g)`.

Use `⟨flat γ0, (hb γ0).2 hγ0, fun y => ?_⟩` and prove the remaining obligations. Establish `hy : flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)) ∈ tensorLat X Λ'` using `(hmem y).1 y.2`. Establish `hyy : g ⟨flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)), hy⟩ = y`. Use `ext`. Simplify using `[g]`.

Establish `h` using `hφ ⟨flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)), hy⟩`. Rewrite `h` using `[AddMonoidHom.comp_apply, hyy]`. Rewrite using `[h]`. Use `show (HC γ0 (flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)))).im = _`. Rewrite using `[← Hf_flat, ContinuousLinearEquiv.apply_symm_apply]`.

Introduce `x _`. Conclude with `norm_tensorEps w₀ _`. Introduce `γ show tensorEps w₀ (flat.symm (flat γ)) = _`. Rewrite using `[ContinuousLinearEquiv.symm_apply_apply]`.
-/
theorem exists_tensorTorus (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') (w₀ : 𝓞 E) :
    ∃ Y : GT (Fin n × Idx X.dim), (∀ γ, flat γ ∈ lat Y.b ↔ γ ∈ tensorLat X Λ') ∧
      ∀ γ, Y.ka (flat γ) = tensorEps w₀ γ := by
  obtain ⟨b, hb⟩ := exists_basis_tensorLat (X := X) hfg hint hdual
  have hmem : ∀ x, x ∈ lat b ↔ flat.symm x ∈ tensorLat X Λ' := fun x => by
    rw [← hb, ContinuousLinearEquiv.apply_symm_apply]
  let g : tensorLat X Λ' →+ lat b :=
    { toFun := fun γ => ⟨flat (γ : Fin n → Vsp X.dim), (hb γ).2 γ.2⟩
      map_zero' := by
        ext
        simp
      map_add' := fun x y => by
        ext
        simp }
  refine ⟨⟨b, ?_, ?_, fun x => tensorEps w₀ (flat.symm x), ?_⟩, hb, ?_⟩
  · intro x y hx hy
    rw [← HC_flat_symm]
    exact im_HC_int hfg hint hdual ((hmem x).1 hx) ((hmem y).1 hy)
  · intro φ
    obtain ⟨γ0, hγ0, hφ⟩ := exists_im_HC_eq hfg hint hdual (φ.comp g)
    refine ⟨flat γ0, (hb γ0).2 hγ0, fun y => ?_⟩
    have hy : flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)) ∈ tensorLat X Λ' :=
      (hmem y).1 y.2
    have hyy : g ⟨flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)), hy⟩ = y := by
      ext
      simp [g]
    have h := hφ ⟨flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)), hy⟩
    rw [AddMonoidHom.comp_apply, hyy] at h
    rw [h]
    show (HC γ0 (flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)))).im = _
    rw [← Hf_flat, ContinuousLinearEquiv.apply_symm_apply]
  · intro x _
    exact norm_tensorEps w₀ _
  · intro γ
    show tensorEps w₀ (flat.symm (flat γ)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]

/- English proof (translation)
Use `⟨exists_tensorTorus hfg hint hdual w₀, ?_, ?_, fun U hU q a F => translate_comp_flat_symm X U hU q a F⟩` and prove the remaining obligations. Introduce `Y hY hka`. Establish `hmem : ∀ x, x ∈ lat Y.b ↔ flat.symm x ∈ tensorLat X Λ'` using `fun x => by`. Rewrite using `[← hY, ContinuousLinearEquiv.apply_symm_apply]`. Establish `hka' : ∀ x, Y.ka x = tensorEps w₀ (flat.symm x)` using `fun x => by`.

Rewrite using `[← hka, ContinuousLinearEquiv.apply_symm_apply]`. Use `⟨fun x hx => ?_, fun x hx y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hka']`. Conclude with `tensorEps_sq_of_mem hfg hint hdual w₀ ((hmem x).1 hx)`. Rewrite using `[hka', hka', hka', map_add, tensorEps_add_of_mem hfg hint hdual w₀ hw ((hmem x).1 hx) ((hmem y).1 hy), HC_flat_symm]`.

Introduce `heps Y hY hka`. Establish `hY' : ∀ γ, flat γ ∈ lat Y.b ↔ ∀ k, γ k ∈ X.L` using `fun γ => by`. Rewrite using `[hY, mem_tensorLat_stdLat]`. Establish `hka1 : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → Y.ka (flat γ) = (∏ k, (X.eps (γ k) : ℂ)) ^ 1` using `fun γ hγ => by`. Rewrite using `[pow_one, hka, tensorEps_eq_prod_eps X w₀ heps hγ]`.

Conclude with `⟨fun F => comp_flat_symm_mem_sec_iff X Y hY' 1 hka1 F, fun F hF => ⟨(comp_flat_symm_mem_sec_iff X Y hY' 1 hka1 F).2 hF, l2_comp_flat_symm_eq_l2 X Y hY' 1 hF⟩⟩`.
-/
theorem principal_torus_of_selfDual (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1) :
    (∃ Y : GT (Fin n × Idx X.dim), (∀ γ, flat γ ∈ lat Y.b ↔ γ ∈ tensorLat X Λ') ∧
      ∀ γ, Y.ka (flat γ) = tensorEps w₀ γ) ∧
    (∀ Y : GT (Fin n × Idx X.dim), (∀ γ, flat γ ∈ lat Y.b ↔ γ ∈ tensorLat X Λ') →
      (∀ γ, Y.ka (flat γ) = tensorEps w₀ γ) →
      (∀ x ∈ lat Y.b, Y.ka x ^ 2 = 1) ∧
      ∀ x ∈ lat Y.b, ∀ y ∈ lat Y.b,
        Y.ka (x + y) = Y.ka x * Y.ka y * cexp (Real.pi * I * (Hf x y).im)) ∧
    ((∀ x ∈ X.L, (X.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im)) →
      ∀ Y : GT (Fin n × Idx X.dim), (∀ γ, flat γ ∈ lat Y.b ↔ γ ∈ tensorLat X (stdLat E n)) →
        (∀ γ, Y.ka (flat γ) = tensorEps w₀ γ) →
        (∀ F, F ∘ flat.symm ∈ Y.Sec 1 ↔ F ∈ X.Sec 1 n) ∧
        ∀ F ∈ X.Sec 1 n, F ∘ flat.symm ∈ Y.Sec 1 ∧ Y.l2 1 (F ∘ flat.symm) = X.l2 1 F) ∧
    (∀ U : ℕ → EuclideanSpace ℂ (Fin n × Idx X.dim) →
        (EuclideanSpace ℂ (Fin n × Idx X.dim) → ℂ) → EuclideanSpace ℂ (Fin n × Idx X.dim) → ℂ,
      (∀ (q : ℕ) a F v,
        U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)) →
      ∀ (q : ℕ) (a : Fin n → Vsp X.dim) (F : (Fin n → Vsp X.dim) → ℂ),
        U q (flat a) (F ∘ flat.symm) = X.U q a F ∘ flat.symm) := by
  refine ⟨exists_tensorTorus hfg hint hdual w₀, ?_, ?_,
    fun U hU q a F => translate_comp_flat_symm X U hU q a F⟩
  · intro Y hY hka
    have hmem : ∀ x, x ∈ lat Y.b ↔ flat.symm x ∈ tensorLat X Λ' := fun x => by
      rw [← hY, ContinuousLinearEquiv.apply_symm_apply]
    have hka' : ∀ x, Y.ka x = tensorEps w₀ (flat.symm x) := fun x => by
      rw [← hka, ContinuousLinearEquiv.apply_symm_apply]
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · rw [hka']
      exact tensorEps_sq_of_mem hfg hint hdual w₀ ((hmem x).1 hx)
    · rw [hka', hka', hka', map_add,
        tensorEps_add_of_mem hfg hint hdual w₀ hw ((hmem x).1 hx) ((hmem y).1 hy), HC_flat_symm]
  · intro heps Y hY hka
    have hY' : ∀ γ, flat γ ∈ lat Y.b ↔ ∀ k, γ k ∈ X.L := fun γ => by
      rw [hY, mem_tensorLat_stdLat]
    have hka1 : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) →
        Y.ka (flat γ) = (∏ k, (X.eps (γ k) : ℂ)) ^ 1 := fun γ hγ => by
      rw [pow_one, hka, tensorEps_eq_prod_eps X w₀ heps hγ]
    exact ⟨fun F => comp_flat_symm_mem_sec_iff X Y hY' 1 hka1 F, fun F hF =>
      ⟨(comp_flat_symm_mem_sec_iff X Y hY' 1 hka1 F).2 hF, l2_comp_flat_symm_eq_l2 X Y hY' 1 hF⟩⟩

/- English proof (translation)
Take `⟨Y, h1, h2⟩` from `exists_tensorTorus (X := X) (n := n) stdLat_fg (fun _ hx => mem_stdLat_iff_herm.1 hx) (fun _ hx => mem_stdLat_iff_herm.2 hx) w₀`. Conclude with `⟨Y, fun γ => (h1 γ).trans mem_tensorLat_stdLat, h2⟩`.
-/
example (X : PT E) (w₀ : 𝓞 E) :
    ∃ Y : GT (Fin n × Idx X.dim), (∀ γ, flat γ ∈ lat Y.b ↔ ∀ k, γ k ∈ X.L) ∧
      ∀ γ, Y.ka (flat γ) = tensorEps w₀ γ := by
  obtain ⟨Y, h1, h2⟩ := exists_tensorTorus (X := X) (n := n) stdLat_fg
    (fun _ hx => mem_stdLat_iff_herm.1 hx) (fun _ hx => mem_stdLat_iff_herm.2 hx) w₀
  exact ⟨Y, fun γ => (h1 γ).trans mem_tensorLat_stdLat, h2⟩

end GlobalTheory.TensorLat
