import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib

open scoped Pointwise in

/- English proof (translation)
Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Take `⟨i1, i2, i3, i4, -⟩` from `GlobalTheory.T.completion_is_local_ring F v`. Establish `hu : IsUnit x` using `hx.isUnit`. Establish `hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = (a : ℝ)⁻¹`. Use `GlobalTheory.GaugeProdFormula.modu_finite F v x hx` as an intermediate fact.

Rewrite `this` using `[GlobalTheory.GaugeEx.modu, dif_pos hu]`. Rewrite using `[this, ha]`. Establish `hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = a`. Rewrite using `[map_inv]`. Apply `NNReal.coe_injective` to reduce the goal to its premises.

Use `push_cast`. Rewrite using `[hc]`. Simplify using the standard rewrite rules. Establish `hm : Measurable fun y : Fv F v => x * y` using `(continuous_const.mul continuous_id).measurable`. Use extensionality with `B hB`.

Rewrite using `[Measure.map_apply hm hB, Measure.smul_apply]`. Establish `e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B`. Use extensionality with `y`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Simplify using `[Units.smul_def]`.

Rewrite using `[e, ← distribHaarChar_mul, hc']`. Both sides reduce to the same expression.
-/
theorem map_mul_fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    [lam.IsAddHaarMeasure] (x : Fv F v) (hx : x ≠ 0) (a : ℝ≥0) (ha : ‖x‖ = (a : ℝ)⁻¹) :
    lam.map (fun y => x * y) = a • lam := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu : IsUnit x := hx.isUnit
  have hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = (a : ℝ)⁻¹ := by
    have := GlobalTheory.GaugeProdFormula.modu_finite F v x hx
    rw [GlobalTheory.GaugeEx.modu, dif_pos hu] at this
    rw [this, ha]
  have hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = a := by
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

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ hM h₂ d b v lam hlam m hm c a t hcu ha hk hts hnorm A hA`. Establish `hloc` using `GlobalTheory.T.completion_is_local_ring F v`. Take `⟨i1, i2, i3, i4, -⟩` from `id hloc`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Use `haveI : lam.IsAddHaarMeasure := hlam.1`.

Take `⟨j1, j2, j3, j4, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)`. Use `haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩`. Take `⟨hK, hW, hH⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›`. Use `haveI := hK`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)`.

Establish `hd : d = 2`. Rewrite using `[← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]`. Substitute `hd` using the available equality. Establish `ha' : (a : ℝ) ≠ 0` using `by exact_mod_cast ha`. Establish `ht : t ≠ 0`.

Introduce `h`. Rewrite `hnorm` using `[h, norm_zero]`. Conclude with `inv_ne_zero ha' hnorm.symm`. Establish `hs` using `map_mul_fv v lam t ht a hnorm`. Use `set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun y => c * y with hf`.

Establish `hfm : Measurable f` using `(continuous_const.mul continuous_id).measurable`. Establish `hk1` using `GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk`. Establish `hk2` using `GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam) (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1`. Simplify using `only [Fintype.card_fin, pow_one] at hk2`. Set `g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)` to `Matrix.of fun _ _ => c`.

Establish `hg : IsUnit g.det`. Rewrite using `[Matrix.det_fin_one]`. Conclude with `hcu`. Establish `hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) = fun X p i => f (X p i)`. Use function extensionality and compare the values at `X p i`.

Simplify using `only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf]`. Rewrite using `[Subsingleton.elim p 0, mul_comm]`. Take `⟨-, -, -, hmem, -⟩` from `GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Fv F v) 1`. Set `τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1` to `fun S => ⟨cT (sigR (Fv F v) σ) g * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) * g, hmem S g⟩`. Establish `hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g` using `fun S => rfl`.

Establish `hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j = algebraMap (Fv F v) (Fv F v ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j`. Introduce `S i j`. Rewrite using `[hτ, hts]`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Take `rfl : j = 0` from `Subsingleton.elim _ _`.

Simplify using `only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, g, Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hτm : Measurable τ` using `by haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩`. Establish `h1 : Continuous τ` using `((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _`. Conclude with `h1.measurable`.

Establish `hc` using `GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam t ht a hs τ hτm hτe`. Establish `hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g`. Rewrite using `[hrm]`. Conclude with `measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i => hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))`. Establish `hfree : IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}` using `GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)`.

Establish `key` using `GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm hfree g hg τ hτ _ _ (by rw [hrm]; exact hk2) hc (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)`. Establish `hτs : τ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) = hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂`. Establish `h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`.

Simplify using `[hermOf]`. Rewrite using `[h0]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hτ]`. Simplify using the standard rewrite rules.

Rewrite `key` using `[hτs]`. Establish `key2` using `congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' A) key`. Simplify using `only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2`. Establish `e1 : a ^ M = a * a ^ (M - 1)`. Rewrite using `[← pow_succ', Nat.sub_add_cancel hM]`.

Rewrite `key2` using `[e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc]`. Establish `ha0 : (a : ℝ≥0∞) ≠ 0` using `by exact_mod_cast ha`. Establish `key3` using `(ENNReal.mul_right_inj ha0 ENNReal.coe_ne_top).1 key2`. Establish `hset : {y : Fin 1 → Fin M → Fv F v ⊗[F] E | scalT c y ∈ A} = (fun X => rmul (Fv F v) X g) ⁻¹' A`. Rewrite using `[hrm]`.

Both sides reduce to the same expression. Rewrite using `[hset, ← key3]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem mass_scalT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (c : Fv F v ⊗[F] E) (a : ℝ≥0) (t : Fv F v), IsUnit c → a ≠ 0 → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = (a : ℝ)⁻¹ → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), MeasurableSet A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) {y | scalT c y ∈ A} = (a : ℝ≥0∞) ^ (M - 1) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) A := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₂ d b v lam hlam m hm c a t hcu ha hk hts hnorm A hA
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have ht : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact inv_ne_zero ha' hnorm.symm
  have hs := map_mul_fv v lam t ht a hnorm
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun y => c * y with hf
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk1 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => c
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact hcu
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf]
    rw [Subsingleton.elim p 0, mul_comm]
  obtain ⟨-, -, -, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Fv F v) 1
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S =>
    ⟨cT (sigR (Fv F v) σ) g * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) * g, hmem S g⟩
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g :=
    fun S => rfl
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    rw [hτ, hts]
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, g,
      Matrix.of_apply]
    ring
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    have h1 : Continuous τ :=
      ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
    exact h1.measurable
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam t ht a hs τ hτm hτe
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hfree : IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm hfree g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
  have hτs : τ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) =
      hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ := by
    have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0 := by
      apply Subtype.ext
      funext i j
      simp [hermOf]
    rw [h0]
    apply Subtype.ext
    rw [hτ]
    simp
  rw [hτs] at key
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' A) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : a ^ M = a * a ^ (M - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hM]
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  have key3 := (ENNReal.mul_right_inj ha0 ENNReal.coe_ne_top).1 key2
  have hset : {y : Fin 1 → Fin M → Fv F v ⊗[F] E | scalT c y ∈ A} =
      (fun X => rmul (Fv F v) X g) ⁻¹' A := by
    rw [hrm]
    rfl
  rw [hset, ← key3]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib
