import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingRankOneVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit

/- English proof (translation)
Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Take `⟨i1, i2, i3, i4, -⟩` from `GlobalTheory.T.completion_is_local_ring F v`. Establish `hu : IsUnit x` using `hx.isUnit`. Establish `hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = ‖x‖`. Use `GlobalTheory.GaugeProdFormula.modu_finite F v x hx` as an intermediate fact.

Rewrite `this` using `[GlobalTheory.GaugeEx.modu, dif_pos hu]`. Conclude with `this`. Establish `hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = (‖x‖₊)⁻¹`. Rewrite using `[map_inv]`. Apply `NNReal.coe_injective` to reduce the goal to its premises.

Use `push_cast`. Rewrite using `[hc]`. Establish `hm : Measurable fun y : Fv F v => x * y` using `(continuous_const.mul continuous_id).measurable`. Use extensionality with `B hB`. Rewrite using `[Measure.map_apply hm hB, Measure.smul_apply]`.

Use `open scoped Pointwise in`. Establish `e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B`. Use extensionality with `y`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Simplify using `[Units.smul_def]`.

Rewrite using `[e, ← distribHaarChar_mul, hc']`. Both sides reduce to the same expression.
-/
theorem lam_map_mul {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    [lam.IsAddHaarMeasure] (x : Fv F v) (hx : x ≠ 0) :
    lam.map (fun y => x * y) = (‖x‖₊)⁻¹ • lam := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu : IsUnit x := hx.isUnit
  have hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = ‖x‖ := by
    have := GlobalTheory.GaugeProdFormula.modu_finite F v x hx
    rw [GlobalTheory.GaugeEx.modu, dif_pos hu] at this
    exact this
  have hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = (‖x‖₊)⁻¹ := by
    rw [map_inv]
    apply NNReal.coe_injective
    push_cast
    rw [hc]
  have hm : Measurable fun y : Fv F v => x * y := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  open scoped Pointwise in
  have e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, hc']
  rfl

/- English proof (translation)
Establish `h0 : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Establish `hv : Valued.v x = WithZero.exp (WithZero.log (Valued.v x))` using `(WithZero.exp_log h0).symm`. Use `set n : ℤ := WithZero.log (Valued.v x) with hn`. Establish `hlt : n < 0`. Rewrite `h` using `[hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Conclude with `h`. Establish `h2 : 2 ≤ Ideal.absNorm v.asIdeal` using `GlobalTheory.CompanionTheory.SW.Growth.two_le_norm v`. Rewrite using `[FinitePlace.norm_def, hv, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]`. Use `push_cast`. Express the relevant statement in the definitionally equal form `((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n ≤ _`.

Establish `h1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_le_of_val_lt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v)
    (hx : x ≠ 0) (h : Valued.v x < 1) : ‖x‖ ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hv : Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log h0).symm
  set n : ℤ := WithZero.log (Valued.v x) with hn
  have hlt : n < 0 := by
    rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    exact h
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := GlobalTheory.CompanionTheory.SW.Growth.two_le_norm v
  rw [FinitePlace.norm_def, hv, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  change ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n ≤ _
  have h1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)
  calc ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ h1 (by omega)
    _ = _ := by rw [zpow_neg_one, one_div]

/- English proof (translation)
Establish `hloc` using `GlobalTheory.T.completion_is_local_ring F v`. Take `⟨i1, i2, i3, i4, -⟩` from `id hloc`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Use `haveI : lam.IsAddHaarMeasure := hlam.1`. Take `⟨j1, j2, j3, j4, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)`.

Use `haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩`. Take `⟨hK, hW, hH⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›`. Use `haveI := hK`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)`. Use `set s : Fv F v := Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) with hs`.

Establish `hsu : IsUnit s` using `u.isUnit.map (Algebra.norm (Fv F v))`. Establish `hs0 : s ≠ 0` using `hsu.ne_zero`. Establish `hN' : algebraMap (Fv F v) (Fv F v ⊗[F] E) s = (u : Fv F v ⊗[F] E) * sigR (Fv F v) σ u` using `GlobalTheory.Doubling.algebraMap_norm_eq hσ _`. Use `set q : ℝ≥0 := ‖s‖₊ with hq`. Establish `hq0 : q ≠ 0` using `by rw [hq]; exact nnnorm_ne_zero_iff.2 hs0`.

Establish `hsigs : sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) s) = algebraMap (Fv F v) (Fv F v ⊗[F] E) s`. Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`. Set `g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)` to `Matrix.of fun _ _ => (u : Fv F v ⊗[F] E)`. Establish `hg : IsUnit g.det`. Rewrite using `[Matrix.det_fin_one]`.

Conclude with `u.isUnit`. Set `T : (Fin 1 → Fin N → Fv F v ⊗[F] E) → Fin 1 → Fin N → Fv F v ⊗[F] E` to `fun X a i => (u : Fv F v ⊗[F] E) * X a i`. Set `Ti : (Fin 1 → Fin N → Fv F v ⊗[F] E) → Fin 1 → Fin N → Fv F v ⊗[F] E` to `fun X a i => ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * X a i`. Establish `hrm : (fun X : Fin 1 → Fin N → Fv F v ⊗[F] E => rmul (Fv F v) X g) = T`. Use function extensionality and compare the values at `X p i`.

Simplify using `only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, T]`. Rewrite using `[Subsingleton.elim p 0, mul_comm]`. Establish `hTc : Continuous T` using `continuous_pi fun a => continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp (continuous_apply a))`. Establish `hTic : Continuous Ti` using `continuous_pi fun a => continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp (continuous_apply a))`. Establish `hTT : ∀ X, T (Ti X) = X`.

Introduce `X`. Use function extensionality and compare the values at `a i`. Simplify using `[T, Ti]`. Establish `hTiT : ∀ X, Ti (T X) = X`. Introduce `X`.

Use function extensionality and compare the values at `a i`. Simplify using `[T, Ti]`. Establish `hWb : BorelSpace (Fin 1 → Fin N → Fv F v ⊗[F] E)` using `by infer_instance`. Establish `hTm : Measurable T` using `hTc.measurable`. Establish `hTim : Measurable Ti` using `hTic.measurable`.

Establish `himg : ∀ C : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), T '' C = Ti ⁻¹' C`. Introduce `C`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Y, hY, rfl⟩`.

Simplify `hY` using `[hTiT]`. Introduce `hX`. Conclude with `⟨Ti X, hX, hTT X⟩`. Establish `himg' : ∀ C : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), T ⁻¹' C = Ti '' C`. Introduce `C`.

Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce `hX`. Conclude with `⟨T X, hX, hTiT X⟩`. Introduce and unpack `⟨Y, hY, rfl⟩`.

Simplify `hY` using `[hTT]`. Establish `hnorm_inv : ‖Algebra.norm (Fv F v) ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)‖₊ = q⁻¹`. Establish `h1 : Algebra.norm (Fv F v) ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * s = 1`. Rewrite using `[hs, ← map_mul, Units.inv_mul, map_one]`. Establish `h2` using `congrArg (fun x : Fv F v => ‖x‖₊) h1`.

Simplify using `only [nnnorm_mul, nnnorm_one] at h2`. Conclude with `eq_inv_of_mul_eq_one_left h2`. Establish `hmu : (coordW (Fv F v) b lam 1 N).map (fun X => rmul (Fv F v) X g) = (q⁻¹ ^ N) • coordW (Fv F v) b lam 1 N`. Rewrite using `[hrm]`. Use extensionality with `C hC`.

Rewrite using `[Measure.map_apply hTm hC, himg', Measure.smul_apply]`. Use `GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul F E σ hσ N d b v lam hlam u⁻¹ C hC` as an intermediate fact. Rewrite using `[show (Ti '' C) = ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin N) => ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * X p k) '' C) from rfl, this, hnorm_inv, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]`. Set `τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1` to `fun S => ⟨fun i j => algebraMap (Fv F v) (Fv F v ⊗[F] E) s * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j, by`. Introduce `a c`.

Use `S.2 a c` as an intermediate fact. Simplify using `only [map_mul, hsigs]`. Rewrite using `[this]⟩`. Establish `hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j = algebraMap (Fv F v) (Fv F v ⊗[F] E) s * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j` using `fun _ _ _ => rfl`. Establish `hτm : Measurable τ`.

Take `⟨-, -, -, hBH, -⟩` from `GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Fv F v) 1`. Use `haveI := hBH`. Use `Continuous.measurable ?_` and prove the remaining obligations. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations.

Conclude with `continuous_const.mul ((continuous_apply_apply i j).comp continuous_subtype_val)`. Establish `hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g`. Introduce `S`. Use extensionality with `i j`. Rewrite using `[hτe, hN']`.

Simplify using `only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, g, Matrix.of_apply]`. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc` using `GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam s hs0 q⁻¹ (lam_map_mul v lam s hs0) τ hτm hτe`. Establish `hfree : IsOpen {X : Fin 1 → Fin N → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}` using `GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)`.

Establish `key` using `GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m (hW 1 N) (hH 1) hm hfree g hg τ hτ _ _ hmu hc 0`. Establish `hτ0 : τ 0 = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Express the relevant statement in the definitionally equal form `algebraMap (Fv F v) (Fv F v ⊗[F] E) s * 0 = 0`.

Rewrite using `[mul_zero]`. Rewrite `key` using `[hτ0, hrm]`. Establish `hTB : MeasurableSet (T '' B)`. Rewrite using `[himg]`. Conclude with `hTim hB`.

Establish `key2` using `congrArg (fun μ' : Measure (Fin 1 → Fin N → Fv F v ⊗[F] E) => μ' (T '' B)) key`. Simplify using `only [Measure.smul_apply, Measure.map_apply hTm hTB] at key2`. Establish `hpre : T ⁻¹' (T '' B) = B`. Rewrite using `[himg, ← Set.preimage_comp]`. Establish `: Ti ∘ T = id` using `funext hTiT`.

Rewrite using `[this, Set.preimage_id]`. Rewrite `key2` using `[hpre]`. Establish `hcoe : (q : ℝ≥0∞) ≠ 0` using `ENNReal.coe_ne_zero.2 hq0`. Express the relevant statement in the definitionally equal form `m 0 (T '' B) = _`. Simplify using `only [ENNReal.smul_def, smul_eq_mul] at key2`.

Establish `e1 : ((q ^ N : ℝ≥0) : ℝ≥0∞) * ((q⁻¹ ^ N : ℝ≥0) : ℝ≥0∞) = 1`. Rewrite using `[← ENNReal.coe_mul, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, ENNReal.coe_one]`. Establish `e2 : ((q ^ N : ℝ≥0) : ℝ≥0∞) * ((q⁻¹ : ℝ≥0) : ℝ≥0∞) = ((q ^ (N - 1) : ℝ≥0) : ℝ≥0∞)`. Rewrite using `[← ENNReal.coe_mul]`. Use `congr 1`.

Take `⟨k, rfl⟩ : ∃ k, N = k + 1` from `⟨N - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel, pow_succ, mul_assoc, mul_inv_cancel₀ hq0, mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, e1, one_mul]`. Use `_ = _ := by rw [key2, ← mul_assoc, e2]`.
-/
theorem fibre_zero_image_mul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (N : ℕ) (hN : 1 ≤ N) (J : Matrix (Fin N) (Fin N) E) (hJ : IsHermND σ J)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    (hlam : IsStdV v lam) (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E))
    (hm : IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m)
    (u : (Fv F v ⊗[F] E)ˣ) (B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E)) (hB : MeasurableSet B) :
    m 0 ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (u : Fv F v ⊗[F] E) * X a i) '' B) =
      ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ (N - 1) : ℝ≥0) : ℝ≥0∞) * m 0 B := by
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  set s : Fv F v := Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) with hs
  have hsu : IsUnit s := u.isUnit.map (Algebra.norm (Fv F v))
  have hs0 : s ≠ 0 := hsu.ne_zero
  have hN' : algebraMap (Fv F v) (Fv F v ⊗[F] E) s = (u : Fv F v ⊗[F] E) * sigR (Fv F v) σ u :=
    GlobalTheory.Doubling.algebraMap_norm_eq hσ _
  set q : ℝ≥0 := ‖s‖₊ with hq
  have hq0 : q ≠ 0 := by rw [hq]; exact nnnorm_ne_zero_iff.2 hs0
  have hsigs : sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) s) = algebraMap (Fv F v) (Fv F v ⊗[F] E) s := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => (u : Fv F v ⊗[F] E)
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact u.isUnit
  let T : (Fin 1 → Fin N → Fv F v ⊗[F] E) → Fin 1 → Fin N → Fv F v ⊗[F] E :=
    fun X a i => (u : Fv F v ⊗[F] E) * X a i
  let Ti : (Fin 1 → Fin N → Fv F v ⊗[F] E) → Fin 1 → Fin N → Fv F v ⊗[F] E :=
    fun X a i => ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * X a i
  have hrm : (fun X : Fin 1 → Fin N → Fv F v ⊗[F] E => rmul (Fv F v) X g) = T := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, T]
    rw [Subsingleton.elim p 0, mul_comm]
  have hTc : Continuous T := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hTic : Continuous Ti := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hTT : ∀ X, T (Ti X) = X := by
    intro X; funext a i; simp [T, Ti]
  have hTiT : ∀ X, Ti (T X) = X := by
    intro X; funext a i; simp [T, Ti]
  have hWb : BorelSpace (Fin 1 → Fin N → Fv F v ⊗[F] E) := by infer_instance
  have hTm : Measurable T := hTc.measurable
  have hTim : Measurable Ti := hTic.measurable
  have himg : ∀ C : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), T '' C = Ti ⁻¹' C := by
    intro C
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      simpa [hTiT] using hY
    · intro hX
      exact ⟨Ti X, hX, hTT X⟩
  have himg' : ∀ C : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), T ⁻¹' C = Ti '' C := by
    intro C
    ext X
    constructor
    · intro hX
      exact ⟨T X, hX, hTiT X⟩
    · rintro ⟨Y, hY, rfl⟩
      simpa [hTT] using hY
  have hnorm_inv : ‖Algebra.norm (Fv F v) ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)‖₊ = q⁻¹ := by
    have h1 : Algebra.norm (Fv F v) ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * s = 1 := by
      rw [hs, ← map_mul, Units.inv_mul, map_one]
    have h2 := congrArg (fun x : Fv F v => ‖x‖₊) h1
    simp only [nnnorm_mul, nnnorm_one] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hmu : (coordW (Fv F v) b lam 1 N).map (fun X => rmul (Fv F v) X g) =
      (q⁻¹ ^ N) • coordW (Fv F v) b lam 1 N := by
    rw [hrm]
    ext C hC
    rw [Measure.map_apply hTm hC, himg', Measure.smul_apply]
    have := GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul F E σ hσ N d b v lam hlam u⁻¹ C hC
    rw [show (Ti '' C) = ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin N) =>
      ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * X p k) '' C) from rfl, this, hnorm_inv, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S =>
    ⟨fun i j => algebraMap (Fv F v) (Fv F v ⊗[F] E) s * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j, by
      intro a c
      have := S.2 a c
      simp only [map_mul, hsigs]
      rw [this]⟩
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) s * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := fun _ _ _ => rfl
  have hτm : Measurable τ := by
    obtain ⟨-, -, -, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Fv F v) 1
    haveI := hBH
    refine Continuous.measurable ?_
    refine Continuous.subtype_mk ?_ _
    refine continuous_matrix fun i j => ?_
    exact continuous_const.mul ((continuous_apply_apply i j).comp continuous_subtype_val)
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g := by
    intro S
    ext i j
    rw [hτe, hN']
    simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, g, Matrix.of_apply]
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    ring
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam s hs0 q⁻¹ (lam_map_mul v lam s hs0) τ hτm hτe
  have hfree : IsOpen {X : Fin 1 → Fin N → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m (hW 1 N) (hH 1) hm hfree g hg τ hτ _ _ hmu hc 0
  have hτ0 : τ 0 = 0 := by
    apply Subtype.ext
    funext i j
    change algebraMap (Fv F v) (Fv F v ⊗[F] E) s * 0 = 0
    rw [mul_zero]
  rw [hτ0, hrm] at key
  have hTB : MeasurableSet (T '' B) := by
    rw [himg]; exact hTim hB
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin N → Fv F v ⊗[F] E) => μ' (T '' B)) key
  simp only [Measure.smul_apply, Measure.map_apply hTm hTB] at key2
  have hpre : T ⁻¹' (T '' B) = B := by
    rw [himg, ← Set.preimage_comp]
    have : Ti ∘ T = id := funext hTiT
    rw [this, Set.preimage_id]
  rw [hpre] at key2
  have hcoe : (q : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hq0
  change m 0 (T '' B) = _
  simp only [ENNReal.smul_def, smul_eq_mul] at key2
  have e1 : ((q ^ N : ℝ≥0) : ℝ≥0∞) * ((q⁻¹ ^ N : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.coe_mul, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, ENNReal.coe_one]
  have e2 : ((q ^ N : ℝ≥0) : ℝ≥0∞) * ((q⁻¹ : ℝ≥0) : ℝ≥0∞) = ((q ^ (N - 1) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_assoc, mul_inv_cancel₀ hq0, mul_one]
  calc m 0 (T '' B) = ((q ^ N : ℝ≥0) : ℝ≥0∞) * (((q⁻¹ ^ N : ℝ≥0) : ℝ≥0∞) * m 0 (T '' B)) := by
        rw [← mul_assoc, e1, one_mul]
    _ = _ := by rw [key2, ← mul_assoc, e2]

/- English proof (translation)
Establish `h1` using `HeightOneSpectrum.Support.finite (𝓞 F) a`. Establish `h2` using `HeightOneSpectrum.Support.finite (𝓞 F) a⁻¹`. Use `Filter.eventually_cofinite.2 ((h1.union h2).subset ?_)` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hc`.

Establish `hc1 : ¬ 1 < v.valuation F a` using `fun h => hc (Or.inl h)`. Establish `hc2 : ¬ 1 < v.valuation F a⁻¹` using `fun h => hc (Or.inr h)`. Apply `hv` to reduce the goal to its premises. Rewrite using `[GlobalTheory.CompanionTheory.SW.Growth.val_alg]`. Establish `hne : v.valuation F a ≠ 0` using `(Valuation.ne_zero_iff _).2 ha`.

Rewrite `hc1`, `hc2` using `[not_lt]`. Rewrite `hc2` using `[map_inv₀]`. Conclude with `le_antisymm hc1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 hc2)`.
-/
theorem val_eq_one_eventually {F : Type} [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) a) = 1 := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 F) a
  have h2 := HeightOneSpectrum.Support.finite (𝓞 F) a⁻¹
  refine Filter.eventually_cofinite.2 ((h1.union h2).subset ?_)
  intro v hv
  by_contra hc
  have hc1 : ¬ 1 < v.valuation F a := fun h => hc (Or.inl h)
  have hc2 : ¬ 1 < v.valuation F a⁻¹ := fun h => hc (Or.inr h)
  apply hv
  rw [GlobalTheory.CompanionTheory.SW.Growth.val_alg]
  have hne : v.valuation F a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  rw [not_lt] at hc1 hc2
  rw [map_inv₀] at hc2
  exact le_antisymm hc1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 hc2)

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)`. Establish `hb1 : b.repr 1 ≠ 0`. Introduce `h`. Conclude with `one_ne_zero (b.repr.map_eq_zero_iff.1 h)`. Choose the witnesses or unpack the hypotheses as in `⟨k0, hk0⟩ : ∃ k, b.repr 1 k ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hb1 (Finsupp.ext hcon)`. Use `filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ hσ d b, val_eq_one_eventually _ hk0] with v hgood hv O hO c hc hcu`. Take `⟨O', hO', hσO', -⟩` from `hgood`.

Use `set s : Fv F v := Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E) with hs`. Establish `hs0 : s ≠ 0` using `(hcu.map (Algebra.norm (Fv F v))).ne_zero`. Establish `hN' : algebraMap (Fv F v) (Fv F v ⊗[F] E) s = (c : Fv F v ⊗[F] E) * sigR (Fv F v) σ c` using `GlobalTheory.Doubling.algebraMap_norm_eq hσ _`. Establish `hσc : sigR (Fv F v) σ c ∈ O` using `(hO _).2 ((hO' _).1 (hσO' _ ((hO' _).2 ((hO _).1 c.2))))`. Establish `hy : algebraMap (Fv F v) (Fv F v ⊗[F] E) s ∈ O`.

Rewrite using `[hN']`. Conclude with `O.mul_mem c.2 hσc`. Establish `hrepr : ∀ (r : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d), (Algebra.TensorProduct.basis (Fv F v) b).repr (algebraMap (Fv F v) (Fv F v ⊗[F] E) r * y) k = r * (Algebra.TensorProduct.basis (Fv F v) b).repr y k`. Introduce `r y k`. Rewrite using `[← Algebra.smul_def, map_smul]`.

Both sides reduce to the same expression. Establish `hone : (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k0 = algebraMap F (Fv F v) (b.repr 1 k0)`. Rewrite using `[Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using the standard rewrite rules. Establish `hs1 : Valued.v s ≤ 1`.

Establish `h` using `(hO _).1 hy k0`. Rewrite `h` using `[← mul_one (algebraMap (Fv F v) (Fv F v ⊗[F] E) s), hrepr, hone, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hv, mul_one]`. Conclude with `h`. Establish `hlt : Valued.v s < 1`. Use `lt_of_le_of_ne hs1 fun h1 => hc ?_` and prove the remaining obligations.

Establish `hw : algebraMap (Fv F v) (Fv F v ⊗[F] E) s⁻¹ * sigR (Fv F v) σ c ∈ O`. Use `(hO _).2 fun k => ?_` and prove the remaining obligations. Establish `h` using `(hO _).1 hσc k`. Rewrite `h`, the goal using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite using `[hrepr, map_mul, map_inv₀, h1, inv_one, one_mul]`.

Conclude with `h`. Establish `hcw : c * (⟨_, hw⟩ : O) = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(c : Fv F v ⊗[F] E) * (algebraMap (Fv F v) (Fv F v ⊗[F] E) s⁻¹ * sigR (Fv F v) σ c) = 1`. Rewrite using `[mul_left_comm, ← hN', ← map_mul, inv_mul_cancel₀ hs0, map_one]`.

Conclude with `IsUnit.of_mul_eq_one _ hcw`. Conclude with `norm_le_of_val_lt v s hs0 hlt`.
-/
theorem norm_le_of_nonunit (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (d : ℕ) (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E),
      (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) →
      ∀ c : O, ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) →
        ‖Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E)‖ ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hb1 : b.repr 1 ≠ 0 := by
    intro h
    exact one_ne_zero (b.repr.map_eq_zero_iff.1 h)
  obtain ⟨k0, hk0⟩ : ∃ k, b.repr 1 k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hb1 (Finsupp.ext hcon)
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ hσ d b, val_eq_one_eventually _ hk0]
    with v hgood hv O hO c hc hcu
  obtain ⟨O', hO', hσO', -⟩ := hgood
  set s : Fv F v := Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E) with hs
  have hs0 : s ≠ 0 := (hcu.map (Algebra.norm (Fv F v))).ne_zero
  have hN' : algebraMap (Fv F v) (Fv F v ⊗[F] E) s = (c : Fv F v ⊗[F] E) * sigR (Fv F v) σ c :=
    GlobalTheory.Doubling.algebraMap_norm_eq hσ _
  have hσc : sigR (Fv F v) σ c ∈ O :=
    (hO _).2 ((hO' _).1 (hσO' _ ((hO' _).2 ((hO _).1 c.2))))
  have hy : algebraMap (Fv F v) (Fv F v ⊗[F] E) s ∈ O := by
    rw [hN']
    exact O.mul_mem c.2 hσc
  have hrepr : ∀ (r : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d),
      (Algebra.TensorProduct.basis (Fv F v) b).repr (algebraMap (Fv F v) (Fv F v ⊗[F] E) r * y) k =
        r * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
    intro r y k
    rw [← Algebra.smul_def, map_smul]
    rfl
  have hone : (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k0 =
      algebraMap F (Fv F v) (b.repr 1 k0) := by
    rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]
    simp
  have hs1 : Valued.v s ≤ 1 := by
    have h := (hO _).1 hy k0
    rw [← mul_one (algebraMap (Fv F v) (Fv F v ⊗[F] E) s), hrepr, hone,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hv, mul_one] at h
    exact h
  have hlt : Valued.v s < 1 := by
    refine lt_of_le_of_ne hs1 fun h1 => hc ?_
    have hw : algebraMap (Fv F v) (Fv F v ⊗[F] E) s⁻¹ * sigR (Fv F v) σ c ∈ O := by
      refine (hO _).2 fun k => ?_
      have h := (hO _).1 hσc k
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h ⊢
      rw [hrepr, map_mul, map_inv₀, h1, inv_one, one_mul]
      exact h
    have hcw : c * (⟨_, hw⟩ : O) = 1 := by
      apply Subtype.ext
      change (c : Fv F v ⊗[F] E) * (algebraMap (Fv F v) (Fv F v ⊗[F] E) s⁻¹ * sigR (Fv F v) σ c) = 1
      rw [mul_left_comm, ← hN', ← map_mul, inv_mul_cancel₀ hs0, map_one]
    exact IsUnit.of_mul_eq_one _ hcw
  exact norm_le_of_val_lt v s hs0 hlt

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ N J hJ hN d b`. Use `filter_upwards [norm_le_of_nonunit F E σ hσ d b] with v hv O hO lam hlam m hm h₂ c hc hcu B hB`. Establish `hn` using `hv O hO c hc hcu`. Take `⟨u, hu⟩` from `hcu`. Establish `h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Simplify using `[hermOf]`. Rewrite using `[h0]`. Establish `key` using `fibre_zero_image_mul F E σ hσ N (by omega) J hJ d b v lam hlam m hm u B hB`.

Rewrite `key` using `[hu]`. Rewrite using `[key]`. Use `gcongr`. Rewrite using `[← ENNReal.ofReal_coe_nnreal]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Use `push_cast`. Use `set x : ℝ := ‖Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E)‖ with hx`. Establish `hx0 : 0 ≤ x` using `norm_nonneg _`. Establish `h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ)` using `by exact_mod_cast GlobalTheory.CompanionTheory.SW.Growth.two_le_norm v`. Establish `hq1 : 1 / (Ideal.absNorm v.asIdeal : ℝ) ≤ 1`.

Rewrite using `[div_le_one (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx1 : x ≤ 1` using `hn.trans hq1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fibre_zero_image_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), IsHermND σ J → 3 ≤ N → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (c : O), ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) → ∀ B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), MeasurableSet B → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * X a i) '' B) ≤ ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) B := by
  intro F E _ _ _ _ _ σ hσ N J hJ hN d b
  filter_upwards [norm_le_of_nonunit F E σ hσ d b] with v hv O hO lam hlam m hm h₂ c hc hcu B hB
  have hn := hv O hO c hc hcu
  obtain ⟨u, hu⟩ := hcu
  have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0 := by
    apply Subtype.ext
    funext i j
    simp [hermOf]
  rw [h0]
  have key := fibre_zero_image_mul F E σ hσ N (by omega) J hJ d b v lam hlam m hm u B hB
  rw [hu] at key
  rw [key]
  gcongr
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  set x : ℝ := ‖Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E)‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast GlobalTheory.CompanionTheory.SW.Growth.two_le_norm v
  have hq1 : 1 / (Ideal.absNorm v.asIdeal : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hx1 : x ≤ 1 := hn.trans hq1
  calc x ^ (N - 1) ≤ x ^ 2 := pow_le_pow_of_le_one hx0 hx1 (by omega)
    _ ≤ (1 / (Ideal.absNorm v.asIdeal : ℝ)) ^ 2 := pow_le_pow_left₀ hx0 hn 2
    _ = 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by rw [one_div_pow]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit
