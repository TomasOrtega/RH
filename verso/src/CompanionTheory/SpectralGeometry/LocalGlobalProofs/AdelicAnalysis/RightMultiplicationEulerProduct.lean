import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LinearChangeEulerProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RmulPF

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

/- English proof (translation)
Establish `hν` using `H (μ.map e) (e.isAddHaarMeasure_map μ he hs)`. Establish `hT : T = e.symm ∘ (B ∘ e)`. Use function extensionality and compare the values at `x`. Simplify using `[← hc x]`. Rewrite using `[hT, ← Measure.map_map hs.measurable (hB.measurable.comp he.measurable), ← Measure.map_map hB.measurable he.measurable, hν, Measure.map_smul, Measure.map_map hs.measurable he.measurable]`.

Establish `: (e.symm ∘ e : W → W) = id`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[this, Measure.map_id]`.
-/
theorem map_eq_of_conj {W V : Type} [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [MeasurableSpace W] [BorelSpace W] [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (e : W ≃+ V) (he : Continuous e) (hs : Continuous e.symm)
    (T : W → W) (B : V → V) (hB : Continuous B) (hc : ∀ x, e (T x) = B (e x)) (c : ℝ≥0)
    (H : ∀ ν : Measure V, ν.IsAddHaarMeasure → ν.map B = c • ν)
    (μ : Measure W) (hμ : μ.IsAddHaarMeasure) : μ.map T = c • μ := by
  have hν := H (μ.map e) (e.isAddHaarMeasure_map μ he hs)
  have hT : T = e.symm ∘ (B ∘ e) := by
    funext x
    simp [← hc x]
  rw [hT, ← Measure.map_map hs.measurable (hB.measurable.comp he.measurable),
    ← Measure.map_map hB.measurable he.measurable, hν, Measure.map_smul,
    Measure.map_map hs.measurable he.measurable]
  have : (e.symm ∘ e : W → W) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Use `conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]`. Rewrite using `[Finset.sum_mul, map_sum, Finsupp.finset_sum_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, Finsupp.smul_apply, Algebra.TensorProduct.basis_apply]`. Simplify using `[inclR, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.basis_repr_tmul]`.
-/
theorem repr_mul_incl (y : R ⊗[F] E) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (y * inclR R e) k =
      ∑ l, (Algebra.TensorProduct.basis R b).repr y l * algebraMap F R (b.repr (b l * e) k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]
  rw [Finset.sum_mul, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, Algebra.TensorProduct.basis_apply]
  simp [inclR, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.basis_repr_tmul]

def coE (n M : ℕ) : (Fin n → Fin M → R ⊗[F] E) ≃+ (Fin n × Fin M × Fin d → R) where
  toFun X p := (Algebra.TensorProduct.basis R b).repr (X p.1 p.2.1) p.2.2
  invFun y a i := (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => y (a, i, k))
  left_inv X := by
    funext a i
    exact (Algebra.TensorProduct.basis R b).equivFun.symm_apply_apply (X a i)
  right_inv y := by
    funext ⟨a, i, k⟩
    exact congrFun ((Algebra.TensorProduct.basis R b).equivFun.apply_symm_apply (fun k => y (a, i, k))) k
  map_add' X Y := by
    funext p
    simp

def coMat {n : ℕ} (g : Matrix (Fin n) (Fin n) E) (M : ℕ) :
    Matrix (Fin n × Fin M × Fin d) (Fin n × Fin M × Fin d) F :=
  fun p q => if p.2.1 = q.2.1 then b.repr (b q.2.2 * g q.1 p.1) p.2.2 else 0

/- English proof (translation)
Use function extensionality and compare the values at `⟨a, i, k⟩`. Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.basis R b).repr (∑ c, X c i * inclR R (g c a)) k = _`. Rewrite using `[map_sum, Finsupp.finset_sum_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[repr_mul_incl, Finset.sum_eq_single i]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `[coMat, coE, mul_comm]`. Introduce `j _ hj`. Simplify using `[coMat, Ne.symm hj]`.

Simplify using the standard rewrite rules.
-/
theorem coE_rmul {n M : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) E) :
    coE b R n M (rmul R X (g.map (inclR R))) = (coMat b g M).map (algebraMap F R) *ᵥ coE b R n M X := by
  funext ⟨a, i, k⟩
  change (Algebra.TensorProduct.basis R b).repr (∑ c, X c i * inclR R (g c a)) k = _
  rw [map_sum, Finsupp.finset_sum_apply]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [repr_mul_incl, Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp [coMat, coE, mul_comm]
  · intro j _ hj
    simp [coMat, Ne.symm hj]
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem rmul_rmul {n M : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (G G' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X G) G' = rmul R X (G * G') := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `[rmul, Matrix.one_apply]`.
-/
theorem rmul_one' {n M : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : rmul R X 1 = X := by
  funext a i
  simp [rmul, Matrix.one_apply]

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `[rmul]`.
-/
theorem rmul_zero' {n M : ℕ} (G : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (0 : Fin n → Fin M → R ⊗[F] E) G = 0 := by
  funext a i
  simp [rmul]

/- English proof (translation)
Introduce `h0`. Take `⟨x, hx, hAx⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Apply `hx` to reduce the goal to its premises. Use `set X := (coE b F n M).symm x with hX`. Establish `h1 : coE b F n M (rmul F X (g.map (inclR (F` using `F) (E := E) F))) = 0 := by`.

Rewrite using `[coE_rmul, hX, AddEquiv.apply_symm_apply]`. Simplify using `using hAx`. Establish `h2 : rmul F X (g.map (inclR (F` using `F) (E := E) F)) = 0 := by`. Simplify using `using h1`. Establish `hu : IsUnit g.det` using `isUnit_iff_ne_zero.mpr hg`.

Establish `h3 : (g.map (inclR (F` using `F) (E := E) F)) * (g⁻¹.map (inclR (F := F) (E := E) F)) = 1 := by`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv g hu]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `h4 : X = 0`. Rewrite using `[← rmul_one' F X, ← h3, ← rmul_rmul, h2, rmul_zero']`.

Use `congrArg (coE b F n M) h4` as an intermediate fact. Simplify `this` using `[hX]`.
-/
theorem coMat_det {n : ℕ} (g : Matrix (Fin n) (Fin n) E) (hg : g.det ≠ 0) (M : ℕ) :
    (coMat b g M).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hx
  set X := (coE b F n M).symm x with hX
  have h1 : coE b F n M (rmul F X (g.map (inclR (F := F) (E := E) F))) = 0 := by
    rw [coE_rmul, hX, AddEquiv.apply_symm_apply]
    simpa using hAx
  have h2 : rmul F X (g.map (inclR (F := F) (E := E) F)) = 0 := by
    simpa using h1
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have h3 : (g.map (inclR (F := F) (E := E) F)) * (g⁻¹.map (inclR (F := F) (E := E) F)) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv g hu]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h4 : X = 0 := by
    rw [← rmul_one' F X, ← h3, ← rmul_rmul, h2, rmul_zero']
  have := congrArg (coE b F n M) h4
  simpa [hX] using this

end Alg

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/- English proof (translation)
Establish `he : Continuous (coE b R n M)`. Use `continuous_pi fun p => ?_` and prove the remaining obligations. Conclude with `(continuous_apply p.2.2).comp (hh.continuous.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))`. Establish `hs : Continuous (coE b R n M).symm`. Establish `hz : (fun z : Fin d → R => (Algebra.TensorProduct.basis R b).equivFun.symm z) = (hh.homeomorph _).symm`.

Use function extensionality and compare the values at `z`. Apply `(hh.homeomorph _).injective` to reduce the goal to its premises. Rewrite using `[Homeomorph.apply_symm_apply]`. Use function extensionality and compare the values at `k`. Conclude with `congrFun ((Algebra.TensorProduct.basis R b).equivFun.apply_symm_apply z) k`.

Use `continuous_pi fun a => continuous_pi fun i => ?_` and prove the remaining obligations. Establish `: (fun y : Fin n × Fin M × Fin d → R => (coE b R n M).symm y a i) = (fun z : Fin d → R => (Algebra.TensorProduct.basis R b).equivFun.symm z) ∘ (fun y k => y (a, i, k))` using `rfl`. Rewrite using `[this, hz]`. Conclude with `(hh.homeomorph _).symm.continuous.comp (continuous_pi fun k => continuous_apply (a, i, k))`. Conclude with `map_eq_of_conj (coE b R n M) he hs _ _ (Continuous.matrix_mulVec continuous_const continuous_id) (fun X => coE_rmul b R X g) c H μ hμ`.
-/
theorem rmul_map_haar (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] [IsTopologicalRing (R ⊗[F] E)]
    {n M : ℕ} (hBor : BorelSpace (Fin n → Fin M → R ⊗[F] E))
    (hh : IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k)
    (g : Matrix (Fin n) (Fin n) E) (c : ℝ≥0)
    (H : ∀ ν : Measure (Fin n × Fin M × Fin d → R), ν.IsAddHaarMeasure →
      ν.map (fun x => (coMat b g M).map (algebraMap F R) *ᵥ x) = c • ν)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun X => rmul R X (g.map (inclR R))) = c • μ := by
  have he : Continuous (coE b R n M) := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2.2).comp
      (hh.continuous.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))
  have hs : Continuous (coE b R n M).symm := by
    have hz : (fun z : Fin d → R => (Algebra.TensorProduct.basis R b).equivFun.symm z) =
        (hh.homeomorph _).symm := by
      funext z
      apply (hh.homeomorph _).injective
      rw [Homeomorph.apply_symm_apply]
      funext k
      exact congrFun ((Algebra.TensorProduct.basis R b).equivFun.apply_symm_apply z) k
    refine continuous_pi fun a => continuous_pi fun i => ?_
    have : (fun y : Fin n × Fin M × Fin d → R => (coE b R n M).symm y a i) =
        (fun z : Fin d → R => (Algebra.TensorProduct.basis R b).equivFun.symm z) ∘
          (fun y k => y (a, i, k)) := rfl
    rw [this, hz]
    exact (hh.homeomorph _).symm.continuous.comp
      (continuous_pi fun k => continuous_apply (a, i, k))
  exact map_eq_of_conj (coE b R n M) he hs _ _
    (Continuous.matrix_mulVec continuous_const continuous_id) (fun X => coE_rmul b R X g) c H μ hμ

end Top

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM n M g hg`. Establish `hfin : Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Set `b` to `Module.finBasis F E`. Take `⟨cinf, c, hU, hinf, hv⟩` from `GlobalTheory.T.addHaar_map_mulVec_eq_smul_at_all_places F (Fin n × Fin M × Fin (Module.finrank F E)) (coMat b g M) (coMat_det b g hg M)`. Use `⟨cinf, c, hU, ?_, ?_⟩` and prove the remaining obligations.

Introduce `μ hμ`. Take `⟨h1, h2, h3, h4, -⟩` from `GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1`. Use `haveI := h1`. Use `haveI := h2`. Use `haveI := h3`.

Use `haveI := h4`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Take `⟨t1, -, -, -, -, -, t7, t8, -, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)`. Use `haveI := t1`. Conclude with `rmul_map_haar b (Ainf F) (t8 n M) (t7 _ b) g cinf hinf μ hμ`.

Introduce `v μ hμ`. Take `⟨h1, h2, h3, h4, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI := h1`. Use `haveI := h2`. Use `haveI := h3`.

Use `haveI := h4`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Take `⟨t1, -, -, -, -, -, t7, t8, -, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)`. Use `haveI := t1`. Conclude with `rmul_map_haar b (Fv F v) (t8 n M) (t7 _ b) g (c v) (hv v) μ hμ`.
-/
theorem rmul_product_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ) (g : Matrix (Fin n) (Fin n) E), g.det ≠ 0 →
    ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧
      (∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
        μ.map (fun X => rmul (Ainf F) X (g.map (inclR (Ainf F)))) = cinf • μ) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
        μ.map (fun X => rmul (Fv F v) X (g.map (inclR (Fv F v)))) = c v • μ) := by
  intro F E _ _ _ _ _ σ hCM n M g hg
  have hfin : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨cinf, c, hU, hinf, hv⟩ := GlobalTheory.T.addHaar_map_mulVec_eq_smul_at_all_places F (Fin n × Fin M × Fin (Module.finrank F E))
    (coMat b g M) (coMat_det b g hg M)
  refine ⟨cinf, c, hU, ?_, ?_⟩
  · intro μ hμ
    obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    obtain ⟨t1, -, -, -, -, -, t7, t8, -, -⟩ :=
      GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
    haveI := t1
    exact rmul_map_haar b (Ainf F) (t8 n M) (t7 _ b) g cinf hinf μ hμ
  · intro v μ hμ
    obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨t1, -, -, -, -, -, t7, t8, -, -⟩ :=
      GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
    haveI := t1
    exact rmul_map_haar b (Fv F v) (t8 n M) (t7 _ b) g (c v) (hv v) μ hμ

end GlobalTheory.CompanionTheory.SW.RmulPF
