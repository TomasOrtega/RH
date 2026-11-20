import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupportStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

/- English proof (translation)
Use `haveI : SigmaFinite (μ.map f) := by rw [h]; infer_instance`. Rewrite using `[Measure.pi_map_pi (f := fun _ => f) (fun _ => hf.aemeasurable)]`. Simplify using `only [h]`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.pi_pi]`.

Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem pi_map_scale {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (f : X → X) (hf : Measurable f) (c : ℝ≥0) (h : μ.map f = c • μ) :
    (Measure.pi fun _ : ι => μ).map (fun x i => f (x i)) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  haveI : SigmaFinite (μ.map f) := by rw [h]; infer_instance
  rw [Measure.pi_map_pi (f := fun _ => f) (fun _ => hf.aemeasurable)]
  simp only [h]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]
  push_cast
  rfl

/- English proof (translation)
Use extensionality with `B hB`. Rewrite using `[Measure.map_apply hf hB, Measure.comap_apply₀ φ P hi him (hf hB).nullMeasurableSet, Measure.smul_apply, Measure.comap_apply₀ φ P hi him hB.nullMeasurableSet]`. Establish `e : φ '' (f ⁻¹' B) = D ⁻¹' (φ '' B)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨f x, hx, hc x⟩`. Introduce and unpack `⟨z, hz, hzy⟩`. Take `⟨x, rfl⟩` from `hs y`. Use `⟨x, ?_, rfl⟩` and prove the remaining obligations.

Establish `: f x = z` using `hi (by rw [hc, hzy])`. Simplify `hz` using `[this]`. Rewrite using `[e, ← MeasurableEquiv.map_apply, hD, Measure.smul_apply]`.
-/
theorem map_comap_scale {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (φ : X → Y)
    (P : Measure Y) (f : X → X) (hf : Measurable f) (D : Y ≃ᵐ Y) (C : ℝ≥0)
    (hs : Function.Surjective φ) (hi : Function.Injective φ)
    (him : ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P)
    (hc : ∀ x, φ (f x) = D (φ x)) (hD : P.map D = C • P) :
    (Measure.comap φ P).map f = C • Measure.comap φ P := by
  ext B hB
  rw [Measure.map_apply hf hB, Measure.comap_apply₀ φ P hi him (hf hB).nullMeasurableSet,
    Measure.smul_apply, Measure.comap_apply₀ φ P hi him hB.nullMeasurableSet]
  have e : φ '' (f ⁻¹' B) = D ⁻¹' (φ '' B) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f x, hx, hc x⟩
    · rintro ⟨z, hz, hzy⟩
      obtain ⟨x, rfl⟩ := hs y
      refine ⟨x, ?_, rfl⟩
      have : f x = z := hi (by rw [hc, hzy])
      simpa [this] using hz
  rw [e, ← MeasurableEquiv.map_apply, hD, Measure.smul_apply]

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite `h1`, `h2` using `[Ideal.span_singleton_le_iff_mem]`. Rewrite `h1`, `h2` using `[← v.intValuation_le_pow_iff_mem]`. Establish `hv : Valued.v (a : Fv F v) = v.intValuation (a : 𝓞 F)`. Use `GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap v (a : 𝓞 F)` as an intermediate fact. Simplify using `using this`.

Establish `h0 : v.intValuation (a : 𝓞 F) ≠ 0` using `v.intValuation_ne_zero _ (by exact_mod_cast ha.ne')`. Establish `hval : v.intValuation (a : 𝓞 F) = WithZero.exp (-(e : ℤ))`. Rewrite `h1`, `h2`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h1`, `h2` using `[WithZero.exp_le_exp]`. Use `congr 1`.

Move the coercions through the operations in `at h2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[FinitePlace.norm_def, hv, hval, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]`. Use `push_cast`. Express the relevant statement in the definitionally equal form `((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e : ℤ)) = _`.

Rewrite using `[zpow_neg, zpow_natCast, inv_pow]`.
-/
theorem norm_natCast (v : HeightOneSpectrum (𝓞 F)) (a e : ℕ) (ha : 0 < a)
    (h1 : (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ e)
    (h2 : ¬ (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ (e + 1)) :
    ‖(a : Fv F v)‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ e := by
  rw [Ideal.span_singleton_le_iff_mem] at h1 h2
  rw [← v.intValuation_le_pow_iff_mem] at h1 h2
  have hv : Valued.v (a : Fv F v) = v.intValuation (a : 𝓞 F) := by
    have := GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap v (a : 𝓞 F)
    simpa using this
  have h0 : v.intValuation (a : 𝓞 F) ≠ 0 :=
     v.intValuation_ne_zero _ (by exact_mod_cast ha.ne')
  have hval : v.intValuation (a : 𝓞 F) = WithZero.exp (-(e : ℤ)) := by
    rw [← WithZero.exp_log h0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    push_cast at h2
    omega
  rw [FinitePlace.norm_def, hv, hval, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  change ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e : ℤ)) = _
  rw [zpow_neg, zpow_natCast, inv_pow]

/- English proof (translation)
Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Take `⟨i1, i2, i3, i4, -⟩` from `GlobalTheory.T.completion_is_local_ring F v`. Establish `hu : IsUnit x` using `hx.isUnit`. Establish `hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ k`. Use `GlobalTheory.GaugeProdFormula.modu_finite F v x hx` as an intermediate fact.

Rewrite `this` using `[GlobalTheory.GaugeEx.modu, dif_pos hu]`. Rewrite using `[this, hk]`. Establish `hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ k)`. Rewrite using `[map_inv]`. Apply `NNReal.coe_injective` to reduce the goal to its premises.

Use `push_cast`. Rewrite using `[hc]`. Simplify using the standard rewrite rules. Establish `hm : Measurable fun y : Fv F v => x * y` using `(continuous_const.mul continuous_id).measurable`. Use extensionality with `B hB`.

Rewrite using `[Measure.map_apply hm hB, Measure.smul_apply]`. Establish `e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B`. Use extensionality with `y`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Simplify using `[Units.smul_def]`.

Rewrite using `[e, ← distribHaarChar_mul, hc']`. Both sides reduce to the same expression.
-/
theorem scale_fv (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) [lam.IsAddHaarMeasure]
    (x : Fv F v) (hx : x ≠ 0) (k : ℕ) (hk : ‖x‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ k) :
    lam.map (fun y => x * y) = ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ k) • lam := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu : IsUnit x := hx.isUnit
  have hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ k := by
    have := GlobalTheory.GaugeProdFormula.modu_finite F v x hx
    rw [GlobalTheory.GaugeEx.modu, dif_pos hu] at this
    rw [this, hk]
  have hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ k) := by
    rw [map_inv]
    apply NNReal.coe_injective
    push_cast
    rw [hc]
    simp
  have hm : Measurable fun y : Fv F v => x * y := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, hc']
  rfl

end GlobalTheory.CompanionTheory.SW.Dil

namespace GlobalTheory.CompanionTheory.SW.Dil

section K
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

def mulPi (ι : Type) (t : R) (ht : t ≠ 0) : (ι → R) ≃ᵐ (ι → R) :=
  MeasurableEquiv.piCongrRight fun _ => (Homeomorph.mulLeft₀ t ht).toMeasurableEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulPi_apply (ι : Type) (t : R) (ht : t ≠ 0) (x : ι → R) (i : ι) :
    mulPi R ι t ht x i = t * x i := rfl

/- English proof (translation)
The claim follows from `pi_map_scale lam (fun y => t * y) (continuous_const.mul continuous_id).measurable c h`.
-/
theorem map_mulPi {ι : Type} [Fintype ι] (lam : Measure R) [SigmaFinite lam] (t : R) (ht : t ≠ 0) (c : ℝ≥0)
    (h : lam.map (fun y => t * y) = c • lam) :
    (Measure.pi fun _ : ι => lam).map (mulPi R ι t ht) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam :=
  pi_map_scale lam (fun y => t * y) (continuous_const.mul continuous_id).measurable c h

/- English proof (translation)
Take `⟨hr, -, -, -, -, -, hh, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R`. Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`. Establish `hb` using `hh d b`. Establish `hemb : MeasurableEmbedding (fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k)` using `hb.homeomorph.toMeasurableEquiv.measurableEmbedding`. Use `map_mulPi (ι := Fin d) R lam t ht c h` as an intermediate fact.

Rewrite `this` using `[Fintype.card_fin]`. Use `map_comap_scale _ _ _ ?_ (mulPi R (Fin d) t ht) _ hb.surjective hb.injective (fun s hs => (hemb.measurableSet_image' hs).nullMeasurableSet) ?_ this` and prove the remaining obligations. Conclude with `(continuous_const.mul continuous_id).measurable`. Introduce `y`. Use function extensionality and compare the values at `k`.

Rewrite using `[mulPi_apply, ← Algebra.smul_def, map_smul]`. Both sides reduce to the same expression.
-/
theorem coordK_map (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [SigmaFinite lam] (t : R) (ht : t ≠ 0) (c : ℝ≥0)
    (h : lam.map (fun y => t * y) = c • lam) :
    (coordK R b lam).map (fun y => algebraMap R (R ⊗[F] E) t * y) = (c ^ d) • coordK R b lam := by
  obtain ⟨hr, -, -, -, -, -, hh, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hb := hh d b
  have hemb : MeasurableEmbedding (fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k) :=
    hb.homeomorph.toMeasurableEquiv.measurableEmbedding
  have := map_mulPi (ι := Fin d) R lam t ht c h
  rw [Fintype.card_fin] at this
  refine map_comap_scale _ _ _ ?_ (mulPi R (Fin d) t ht) _ hb.surjective hb.injective
    (fun s hs => (hemb.measurableSet_image' hs).nullMeasurableSet) ?_ this
  · exact (continuous_const.mul continuous_id).measurable
  · intro y
    funext k
    rw [mulPi_apply, ← Algebra.smul_def, map_smul]
    rfl

end K
end GlobalTheory.CompanionTheory.SW.Dil

namespace GlobalTheory.CompanionTheory.SW.Dil
/- English proof (translation)
Take `rfl : i = 0` from `Subsingleton.elim _ _`. Take `rfl : j = 0` from `Subsingleton.elim _ _`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cT_scalar {A : Type} [CommRing A] (s : A →+* A) (c : A) (hs : s c = c)
    (S : Matrix (Fin 1) (Fin 1) A) (i j : Fin 1) :
    (cT s (Matrix.of fun _ _ => c : Matrix (Fin 1) (Fin 1) A) * S * (Matrix.of fun _ _ => c : Matrix (Fin 1) (Fin 1) A)) i j = c ^ 2 * S i j := by
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, hs]
  ring
end GlobalTheory.CompanionTheory.SW.Dil

namespace GlobalTheory.CompanionTheory.SW.Dil

section H
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

/- English proof (translation)
Establish `e : s ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) s`. Simplify using `[Algebra.TensorProduct.algebraMap_apply]`. Establish `h2 : algebraMap F R (1 / 2) * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap F R) 2, ← map_mul]`. Evaluate the numerical expressions.

Rewrite using `[e, Algebra.trace_algebraMap, Module.finrank_baseChange, hσ.2.2.1, two_nsmul, ← two_mul, ← mul_assoc, h2, one_mul]`.
-/
theorem half_trace_tmul (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (s : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s := by
  have e : s ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) s := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]
    norm_num
  rw [e, Algebra.trace_algebraMap, Module.finrank_baseChange, hσ.2.2.1, two_nsmul, ← two_mul,
    ← mul_assoc, h2, one_mul]

/- English proof (translation)
Take `⟨i1, i2, i3, i4, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R`. Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`. Take `⟨hK, -, hH⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam ‹_›`. Use `haveI := hK`. Use `haveI := hH 1`.

Use `set φ : HermR R σ 1 → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) := fun S => ((fun i : Fin 1 => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)), (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} => (S : Matrix (Fin 1) (F …`. Use `set Q : Measure ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) := Measure.pi fun _ => coordK R b lam with hQ`. Use `set P := (Measure.pi fun _ : Fin 1 => lam).prod Q with hP`. Establish `hν : coordHerm R σ b lam 1 = Measure.comap φ P` using `rfl`. Establish `hemp : ∀ p : {p : Fin 1 × Fin 1 // p.1 < p.2}, False` using `fun p => absurd p.2 (by rw [Subsingleton.elim p.1.1 p.1.2]; exact lt_irrefl _)`.

Establish `hcond : Function.Injective φ ∧ ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P`. Assume the negation of the conclusion as `hc`. Establish `h0 : coordHerm R σ b lam 1 = 0`. Rewrite using `[hν, Measure.comap, dif_neg hc]`. Use `isOpen_univ.measure_pos (coordHerm R σ b lam 1) Set.univ_nonempty` as an intermediate fact.

Simplify using `[h0] at this`. Establish `hs : Function.Surjective φ`. Introduce and unpack `⟨y, w⟩`. Use `⟨hermScal R σ (y 0), Prod.ext ?_ ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Rewrite using `[Subsingleton.elim i 0]`. Conclude with `half_trace_tmul R σ hσ (y 0)`. Use function extensionality and compare the values at `p`. Conclude with `(hemp p).elim`. Establish `hD : P.map ((mulPi R (Fin 1) t ht).prodCongr (MeasurableEquiv.refl _)) = c • P`.

Establish `e` using `Measure.map_prod_map (Measure.pi fun _ : Fin 1 => lam) Q (mulPi R (Fin 1) t ht).measurable (measurable_id)`. Rewrite `e` using `[map_mulPi R lam t ht c h, Measure.map_id]`. Simplify using `only [Fintype.card_fin, pow_one] at e`. Rewrite `e` using `[Measure.prod_smul_left]`. Conclude with `e.symm`.

Rewrite using `[hν]`. Use `map_comap_scale φ P τ hτm _ c hs hcond.1 hcond.2 ?_ hD` and prove the remaining obligations. Introduce `S`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) _ = t * (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) _)`. Rewrite using `[hτ, ← Algebra.smul_def t, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `p`. Conclude with `(hemp p).elim`.
-/
theorem coordHerm_map (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [lam.IsAddHaarMeasure] (t : R) (ht : t ≠ 0) (c : ℝ≥0)
    (h : lam.map (fun y => t * y) = c • lam) (τ : HermR R σ 1 → HermR R σ 1) (hτm : Measurable τ)
    (hτ : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j =
      algebraMap R (R ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j) :
    (coordHerm R σ b lam 1).map τ = c • coordHerm R σ b lam 1 := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam ‹_›
  haveI := hK
  haveI := hH 1
  set φ : HermR R σ 1 → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
    fun S => ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))
    with hφ
  set Q : Measure ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) := Measure.pi fun _ => coordK R b lam with hQ
  set P := (Measure.pi fun _ : Fin 1 => lam).prod Q with hP
  have hν : coordHerm R σ b lam 1 = Measure.comap φ P := rfl
  have hemp : ∀ p : {p : Fin 1 × Fin 1 // p.1 < p.2}, False := fun p =>
    absurd p.2 (by rw [Subsingleton.elim p.1.1 p.1.2]; exact lt_irrefl _)
  have hcond : Function.Injective φ ∧ ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P := by
    by_contra hc
    have h0 : coordHerm R σ b lam 1 = 0 := by
      rw [hν, Measure.comap, dif_neg hc]
    have := isOpen_univ.measure_pos (coordHerm R σ b lam 1) Set.univ_nonempty
    simp [h0] at this
  have hs : Function.Surjective φ := by
    rintro ⟨y, w⟩
    refine ⟨hermScal R σ (y 0), Prod.ext ?_ ?_⟩
    · funext i
      rw [Subsingleton.elim i 0]
      exact half_trace_tmul R σ hσ (y 0)
    · funext p
      exact (hemp p).elim
  have hD : P.map ((mulPi R (Fin 1) t ht).prodCongr (MeasurableEquiv.refl _)) = c • P := by
    have e := Measure.map_prod_map (Measure.pi fun _ : Fin 1 => lam) Q (mulPi R (Fin 1) t ht).measurable
      (measurable_id)
    rw [map_mulPi R lam t ht c h, Measure.map_id] at e
    simp only [Fintype.card_fin, pow_one] at e
    rw [Measure.prod_smul_left] at e
    exact e.symm
  rw [hν]
  refine map_comap_scale φ P τ hτm _ c hs hcond.1 hcond.2 ?_ hD
  intro S
  refine Prod.ext ?_ ?_
  · funext i
    change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) _ =
      t * (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) _)
    rw [hτ, ← Algebra.smul_def t, map_smul, smul_eq_mul]
    ring
  · funext p
    exact (hemp p).elim

end H

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ d b v lam hlam m hm hM a e ha h1 h2 s A hA`. Establish `hloc` using `GlobalTheory.T.completion_is_local_ring F v`. Take `⟨i1, i2, i3, i4, -⟩` from `id hloc`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Use `haveI : lam.IsAddHaarMeasure := hlam.1`.

Take `⟨j1, j2, j3, j4, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)`. Use `haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩`. Take `⟨hK, hW, hH⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›`. Use `haveI := hK`. Establish `hd : d = 2`.

Rewrite using `[← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]`. Substitute `hd` using the available equality. Establish `hnorm` using `norm_natCast v a e ha h1 h2`. Establish `hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `ht : (a : Fv F v) ≠ 0`.

Introduce `h`. Rewrite `hnorm` using `[h, norm_zero]`. Conclude with `(pow_ne_zero e (inv_ne_zero hq)) hnorm.symm`. Establish `ht2 : (a : Fv F v) ^ 2 ≠ 0` using `pow_ne_zero 2 ht`. Establish `hnorm2 : ‖(a : Fv F v) ^ 2‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ (2 * e)`.

Rewrite using `[norm_pow, hnorm, ← pow_mul, mul_comm]`. Establish `hs1` using `scale_fv v lam _ ht e hnorm`. Establish `hs2` using `scale_fv v lam _ ht2 (2 * e) hnorm2`. Use `set q : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) with hqdef`. Use `set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun y => algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) * y with hf`.

Establish `hcast : algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) = (a : Fv F v ⊗[F] E)` using `map_natCast _ _`. Establish `hfm : Measurable f` using `(continuous_const.mul continuous_id).measurable`. Establish `hk` using `coordK_map (Fv F v) σ hσ b lam _ ht _ hs1`. Establish `hk1` using `pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk`. Establish `hk2` using `pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam) (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1`.

Simplify using `only [Fintype.card_fin, pow_one] at hk2`. Set `g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)` to `Matrix.of fun _ _ => (a : Fv F v ⊗[F] E)`. Establish `hg : IsUnit g.det`. Rewrite using `[Matrix.det_fin_one]`. Express the relevant statement in the definitionally equal form `IsUnit (a : Fv F v ⊗[F] E)`.

Rewrite using `[← hcast]`. Conclude with `ht.isUnit.map _`. Establish `hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) = fun X p i => f (X p i)`. Use function extensionality and compare the values at `X p i`. Simplify using `only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf, hcast]`.

Rewrite using `[Subsingleton.elim p 0, mul_comm]`. Set `τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1` to `fun S => (a ^ 2) • S`. Establish `hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j = algebraMap (Fv F v) (Fv F v ⊗[F] E) ((a : Fv F v) ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j`. Introduce `S i j`. Express the relevant statement in the definitionally equal form `(a ^ 2) • (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j = _`.

Rewrite using `[nsmul_eq_mul, map_pow, hcast]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hτm : Measurable τ` using `by haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩`. Conclude with `(continuous_nsmul (a ^ 2)).measurable`.

Establish `hc` using `coordHerm_map (Fv F v) σ hσ b lam _ ht2 _ hs2 τ hτm hτe`. Establish `hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g`. Introduce `S`. Use extensionality with `i j`. Establish `hsig : sigR (Fv F v) σ (a : Fv F v ⊗[F] E) = a` using `map_natCast _ _`.

Rewrite using `[hτe, map_pow, hcast, cT_scalar _ _ hsig]`. Establish `hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g`. Rewrite using `[hrm]`. Conclude with `measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i => hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))`. Establish `key` using `GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Fv F v) hloc 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm g hg τ hτ _ _ (by rw [hrm]; exact hk2) hc (hermScal (Fv F v) σ s)`.

Establish `hτs : τ (hermScal (Fv F v) σ s) = hermScal (Fv F v) σ ((a : Fv F v) ^ 2 * s)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Rewrite using `[hτe]`. Express the relevant statement in the definitionally equal form `_ * (s ⊗ₜ[F] (1 : E)) = ((a : Fv F v) ^ 2 * s) ⊗ₜ[F] (1 : E)`.

Simplify using `[Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite `key` using `[hτs]`. Establish `key2` using `congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' A) key`. Simplify using `only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2`. Establish `e1 : ((q ^ e) ^ 2) ^ M = q ^ (2 * e) * q ^ (e * (2 * M - 2))`.

Rewrite using `[← pow_add, ← pow_mul, ← pow_mul]`. Use `congr 1`. Take `⟨k, rfl⟩ : ∃ k, M = k + 1` from `⟨M - 1, by omega⟩`. Establish `: 2 * (k + 1) - 2 = 2 * k` using `by omega`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `key2` using `[e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc]`. Establish `hq0 : ((q ^ (2 * e) : ℝ≥0) : ℝ≥0∞) ≠ 0`. Rewrite using `[ENNReal.coe_ne_zero]`. Use `pow_ne_zero _ ?_` and prove the remaining obligations.

Rewrite using `[hqdef]`. Conclude with `hq` after adjusting the coercions. Establish `key3` using `(ENNReal.mul_right_inj hq0 ENNReal.coe_ne_top).1 key2`. Establish `hset : {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ A} = (fun X => rmul (Fv F v) X g) ⁻¹' A`. Rewrite using `[hrm]`.

Use extensionality with `X`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, hf, hcast]`. Rewrite using `[hset, ← key3, hqdef]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem dilation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → 1 ≤ M → ∀ (a : ℕ) (e : ℕ), 0 < a → (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ e → ¬ (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ (e + 1) → ∀ (s : Fv F v) (A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet A → m (hermScal (Fv F v) σ s) {X | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (e * (2 * M - 2)) * m (hermScal (Fv F v) σ ((a : Fv F v) ^ 2 * s)) A := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b v lam hlam m hm hM a e ha h1 h2 s A hA
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have hnorm := norm_natCast v a e ha h1 h2
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ht : (a : Fv F v) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact (pow_ne_zero e (inv_ne_zero hq)) hnorm.symm
  have ht2 : (a : Fv F v) ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hnorm2 : ‖(a : Fv F v) ^ 2‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ (2 * e) := by
    rw [norm_pow, hnorm, ← pow_mul, mul_comm]
  have hs1 := scale_fv v lam _ ht e hnorm
  have hs2 := scale_fv v lam _ ht2 (2 * e) hnorm2
  set q : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) with hqdef
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun y => algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) * y with hf
  have hcast : algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) = (a : Fv F v ⊗[F] E) := map_natCast _ _
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := coordK_map (Fv F v) σ hσ b lam _ ht _ hs1
  have hk1 := pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => (a : Fv F v ⊗[F] E)
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    change IsUnit (a : Fv F v ⊗[F] E)
    rw [← hcast]
    exact ht.isUnit.map _
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf, hcast]
    rw [Subsingleton.elim p 0, mul_comm]
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S => (a ^ 2) • S
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) ((a : Fv F v) ^ 2) *
        (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    change (a ^ 2) • (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j = _
    rw [nsmul_eq_mul, map_pow, hcast]
    push_cast
    rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    exact (continuous_nsmul (a ^ 2)).measurable
  have hc := coordHerm_map (Fv F v) σ hσ b lam _ ht2 _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g := by
    intro S
    ext i j
    have hsig : sigR (Fv F v) σ (a : Fv F v ⊗[F] E) = a := map_natCast _ _
    rw [hτe, map_pow, hcast, cT_scalar _ _ hsig]
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Fv F v) hloc 1 (coordW (Fv F v) b lam 1 M)
    (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermScal (Fv F v) σ s)
  have hτs : τ (hermScal (Fv F v) σ s) = hermScal (Fv F v) σ ((a : Fv F v) ^ 2 * s) := by
    apply Subtype.ext
    funext i j
    rw [hτe]
    change _ * (s ⊗ₜ[F] (1 : E)) = ((a : Fv F v) ^ 2 * s) ⊗ₜ[F] (1 : E)
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hτs] at key
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' A) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : ((q ^ e) ^ 2) ^ M = q ^ (2 * e) * q ^ (e * (2 * M - 2)) := by
    rw [← pow_add, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) - 2 = 2 * k := by omega
    rw [this]
    ring
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have hq0 : ((q ^ (2 * e) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    refine pow_ne_zero _ ?_
    rw [hqdef]
    exact_mod_cast hq
  have key3 := (ENNReal.mul_right_inj hq0 ENNReal.coe_ne_top).1 key2
  have hset : {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ A} =
      (fun X => rmul (Fv F v) X g) ⁻¹' A := by
    rw [hrm]
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hf, hcast]
  rw [hset, ← key3, hqdef]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.Dil
