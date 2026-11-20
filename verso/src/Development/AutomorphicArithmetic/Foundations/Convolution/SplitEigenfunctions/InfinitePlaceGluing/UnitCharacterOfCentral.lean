import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.AdmissibleRightTranslate
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.DiagInvVal
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitary
import Development.AutomorphicArithmetic.WhittakerHecke.RatIdeleEqDiagonalMulUnitOfAbsEqOne
import Development.AutomorphicArithmetic.WhittakerHecke.CuspSubspaceTranslateEqSmulSpecialTranslate

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private noncomputable def Bt (M : Meas ℚ) (Φ : GL (Fin 2) (A E) → ℂ) (t : IdeleGroup ℚ) : ℂ :=
  ∫ g in M.D, Φ (em E (gl g * dM t)) ∂M.μ

/- English proof (translation)
Establish `h : Continuous (AdeleBaseChange.adeleMap ℚ E)` using `AdeleBaseChange.continuous_adeleMap`. Use `continuous_adelicGL2_of_continuous_entries (fun i j => ?_) (fun i j => ?_)` and prove the remaining obligations. Conclude with `h.comp ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (A ℚ))).matrix_elem i j)`. Establish `e : (fun x : GL (Fin 2) (A ℚ) => (((em E x)⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) i j) = fun x => AdeleBaseChange.adeleMap ℚ E (((x⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)`. Use function extensionality and compare the values at `x`.

Rewrite using `[← map_inv]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h.comp (((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (A ℚ))).comp continuous_inv).matrix_elem i j)`.
-/
private theorem continuous_em : Continuous (em E) := by
  have h : Continuous (AdeleBaseChange.adeleMap ℚ E) := AdeleBaseChange.continuous_adeleMap
  refine continuous_adelicGL2_of_continuous_entries (fun i j => ?_) (fun i j => ?_)
  · exact h.comp ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (A ℚ))).matrix_elem i j)
  · have e : (fun x : GL (Fin 2) (A ℚ) => (((em E x)⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) i j) =
        fun x => AdeleBaseChange.adeleMap ℚ E (((x⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
      funext x
      rw [← map_inv]
      rfl
    rw [e]
    exact h.comp (((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (A ℚ))).comp continuous_inv).matrix_elem i j)

/- English proof (translation)
Use `⟨Matrix.GeneralLinearGroup.map (algebraMap ℚ E) γ, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[ratGL_apply, show ((em E) ((ratGL ℚ 2) γ)).val i j = AdeleBaseChange.adeleMap ℚ E (((ratGL ℚ 2) γ).val i j) from rfl, ratGL_apply]`. Conclude with `AdeleBaseChange.adeleMap_algebraMap _`.
-/
private theorem exists_em_ratGL (γ : GL (Fin 2) ℚ) : ∃ γ', em E (ratGL ℚ 2 γ) = ratGL E 2 γ' := by
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap ℚ E) γ, ?_⟩
  apply Units.ext
  ext i j
  rw [ratGL_apply, show ((em E) ((ratGL ℚ 2) γ)).val i j = AdeleBaseChange.adeleMap ℚ E (((ratGL ℚ 2) γ).val i j) from rfl, ratGL_apply]
  exact AdeleBaseChange.adeleMap_algebraMap _

/- English proof (translation)
Establish `hv : M.μ M.D < ⊤` using `_root_.UpperTheory.ConvolutionTheory.R2.M.volD ℚ M`. Establish `hcc : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ (em E (gl p.2 * dM p.1))` using `hc.comp (continuous_em.comp ((continuous_gl.comp continuous_snd).mul (continuous_dM.comp continuous_fst)))`. Use `continuous_of_dominated (bound := fun _ => C) (fun t => ?_) (fun t => ?_) ?_ ?_` and prove the remaining obligations. Conclude with `(hcc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable`. Conclude with `ae_of_all _ fun g => hb _`.

Use `haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using hv⟩`. Conclude with `integrable_const _`. Conclude with `ae_of_all _ fun g => hc.comp (continuous_em.comp (continuous_const.mul continuous_dM))`.
-/
private theorem Bt_cont (M : Meas ℚ) {Φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous Φ) {C : ℝ} (hb : ∀ g, ‖Φ g‖ ≤ C) :
    Continuous (Bt M Φ) := by
  have hv : M.μ M.D < ⊤ := _root_.UpperTheory.ConvolutionTheory.R2.M.volD ℚ M
  have hcc : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ (em E (gl p.2 * dM p.1)) :=
    hc.comp (continuous_em.comp ((continuous_gl.comp continuous_snd).mul (continuous_dM.comp continuous_fst)))
  refine continuous_of_dominated (bound := fun _ => C) (fun t => ?_) (fun t => ?_) ?_ ?_
  · exact (hcc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ fun g => hb _
  · haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using hv⟩
    exact integrable_const _
  · exact ae_of_all _ fun g => hc.comp (continuous_em.comp (continuous_const.mul continuous_dM))

/- English proof (translation)
The claim follows from `norm_setIntegral_le_of_norm_le_const (_root_.UpperTheory.ConvolutionTheory.R2.M.volD ℚ M) fun g _ => hb _`.
-/
private theorem Bt_bdd (M : Meas ℚ) {Φ : GL (Fin 2) (A E) → ℂ} {C : ℝ} (hb : ∀ g, ‖Φ g‖ ≤ C) (t : IdeleGroup ℚ) :
    ‖Bt M Φ t‖ ≤ C * M.μ.real M.D :=
  norm_setIntegral_le_of_norm_le_const (_root_.UpperTheory.ConvolutionTheory.R2.M.volD ℚ M) fun g _ => hb _

/- English proof (translation)
Use `set u : G1 ℚ → ℂ := fun g => Φ (em E (gl g * dM t)) with hu`. Establish `hinv : ∀ γ g, u (ratS ℚ γ * g) = u g` using `fun γ g => by`. Take `⟨γ', h'⟩` from `exists_em_ratGL (E := E) (Matrix.SpecialLinearGroup.toGL γ)`. Simplify using `only [hu]`. Rewrite using `[gl_mul, gl_ratS, mul_assoc, map_mul, h', hl]`.

Establish `hd` using `(_root_.UpperTheory.ConvolutionTheory.R2.M.dConj ℚ M u hinv r⁻¹).2`. Unfold `Bt`. Rewrite using `[← hd]`. Use `integral_congr_ae (ae_of_all _ fun g => ?_)` and prove the remaining obligations. Take `⟨γ, hγ⟩` from `exists_ratGL_dM (F := ℚ) r`.

Take `⟨γ', h'⟩` from `exists_em_ratGL (E := E) γ`. Establish `e : gl g * dM (IdeleGroup.diagonal ℚ r * t) = ratGL ℚ 2 γ * (gl (cD (IdeleGroup.diagonal ℚ r⁻¹) g) * dM t)`. Rewrite using `[hγ, dM_mul, ← mul_assoc, ← mul_assoc, dM_mul_gl, ← cD_mul_left, ← map_mul, mul_inv_cancel, map_one, cD_one_left]`. Simplify using `only [hu]`. Rewrite using `[e, map_mul, h', hl]`.
-/
private theorem Bt_rat (M : Meas ℚ) {Φ : GL (Fin 2) (A E) → ℂ} (hl : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) (r : ℚˣ) (t : IdeleGroup ℚ) :
    Bt M Φ (IdeleGroup.diagonal ℚ r * t) = Bt M Φ t := by
  set u : G1 ℚ → ℂ := fun g => Φ (em E (gl g * dM t)) with hu
  have hinv : ∀ γ g, u (ratS ℚ γ * g) = u g := fun γ g => by
    obtain ⟨γ', h'⟩ := exists_em_ratGL (E := E) (Matrix.SpecialLinearGroup.toGL γ)
    simp only [hu]
    rw [gl_mul, gl_ratS, mul_assoc, map_mul, h', hl]
  have hd := (_root_.UpperTheory.ConvolutionTheory.R2.M.dConj ℚ M u hinv r⁻¹).2
  unfold Bt
  rw [← hd]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  obtain ⟨γ, hγ⟩ := exists_ratGL_dM (F := ℚ) r
  obtain ⟨γ', h'⟩ := exists_em_ratGL (E := E) γ
  have e : gl g * dM (IdeleGroup.diagonal ℚ r * t) = ratGL ℚ 2 γ * (gl (cD (IdeleGroup.diagonal ℚ r⁻¹) g) * dM t) := by
    rw [hγ, dM_mul, ← mul_assoc, ← mul_assoc, dM_mul_gl, ← cD_mul_left, ← map_mul, mul_inv_cancel, map_one, cD_one_left]
  simp only [hu]
  rw [e, map_mul, h', hl]

end

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Unfold `UPer UI SLP Bt`. Use `integral_congr_ae (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Simplify using `only []`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (ae_of_all _ fun g => ?_)` and prove the remaining obligations.

Simplify using `only []`. Take `⟨-, -, -, -, -, -, -, -, hs, -⟩` from `szLaws E D`. Rewrite using `[hs, ← hcen]`. Use `congr 1`. Rewrite using `[dM_mul, map_mul (em E) (gl g), map_mul (em E) (dM _), ← mul_assoc, ← mul_assoc, ← mul_assoc, UpperTheory.ConvolutionTheory.R2.scalar_comm (z : (A E)ˣ) (em E (gl g))]`.
-/
private theorem UPer_eq (D : Dat ℚ E) (M : Meas ℚ) {ω : HChar ℚ} {Φ : GL (Fin 2) (A E) → ℂ}
    (hcen : ∀ z g, Φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 (ideleNorm ℚ E z) : ℂˣ) : ℂ) * Φ g) (t : IdeleGroup ℚ) :
    UPer D M (fun x => Φ (x * em E (dM t))) =
      ∫ z in normOneFundamentalDomain E, ((ω.1 (ideleNorm ℚ E (z : IdeleGroup E)) : ℂˣ) : ℂ) *
        Bt M Φ ((ideleNorm ℚ E (z : IdeleGroup E))⁻¹ * t) ∂normOneMeasure E := by
  unfold UPer UI SLP Bt
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only []
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only []
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := szLaws E D
  rw [hs, ← hcen]
  congr 1
  rw [dM_mul, map_mul (em E) (gl g), map_mul (em E) (dM _), ← mul_assoc, ← mul_assoc, ← mul_assoc, UpperTheory.ConvolutionTheory.R2.scalar_comm (z : (A E)ˣ) (em E (gl g))]

/- English proof (translation)
Establish `hu : P.IsUnitary` using `GlobalTheory.SpehPair.isUnitary_of_isNormalised hN`. Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 P.ne_bot`. Take `⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0` from `Function.ne_iff.1 fun e => h0 (Subtype.ext e)`. Establish `hfr : Module.finrank ℚ E = 2` using `by rw [Module.finrank_eq_card_basis D.b]; simp`. Introduce `a`.

Establish `h1` using `hC φ hφ (ideleEmbedding ℚ E a) g`. Establish `h2` using `hu.norm_eq hφ (ideleEmbedding ℚ E a) g`. Rewrite `h2` using `[h1, norm_mul, ideleNorm_ideleEmbedding, hfr, map_pow, Units.val_pow_eq_pow_val, norm_pow]`. Establish `h3 : ‖((ω.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1` using `(mul_eq_right₀ (norm_ne_zero_iff.2 hg)).1 h2`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3`.
-/
private theorem unitCharacter_of_central {P : CuspSub E 2} (D : Dat ℚ E) {ω : HChar ℚ} (hN : GlobalTheory.DiscSpec.IsNormalised P) (hC : CenN P ω) : Unit1 ω := by
  have hu : P.IsUnitary := GlobalTheory.SpehPair.isUnitary_of_isNormalised hN
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 P.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
  have hfr : Module.finrank ℚ E = 2 := by rw [Module.finrank_eq_card_basis D.b]; simp
  intro a
  have h1 := hC φ hφ (ideleEmbedding ℚ E a) g
  have h2 := hu.norm_eq hφ (ideleEmbedding ℚ E a) g
  rw [h1, norm_mul, ideleNorm_ideleEmbedding, hfr, map_pow, Units.val_pow_eq_pow_val, norm_pow] at h2
  have h3 : ‖((ω.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := (mul_eq_right₀ (norm_ne_zero_iff.2 hg)).1 h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

/- English proof (translation)
Take `⟨C, hC⟩` from `hA.bdd`. Use `haveI := U.prob`. Establish `hBc` using `Bt_cont M hA.cont hC`. Establish `hBb` using `Bt_bdd M hC`. Establish `hdiag : ∀ (χ : HChar ℚ) (r : ℚˣ), χ.1 (IdeleGroup.diagonal ℚ r) = 1` using `fun χ r => χ.2.2 r`.

Establish `hcm : ∀ t, (ω⁻¹ * ε).1 t = (ω.1 t)⁻¹ * ε.1 t` using `fun _ => rfl`. Use `set c : IdeleGroup ℚ → ℂ := fun t => (((ω⁻¹ * ε).1 t : ℂˣ) : ℂ) with hc`. Establish `hcc : Continuous c` using `Units.continuous_val.comp (ω⁻¹ * ε).2.1`. Establish `hcn : ∀ t, ‖c t‖ = 1` using `fun t => by`. Simplify using `only [hc, hcm, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]`.

Rewrite using `[hω t, hε t]`. Simplify using the standard rewrite rules. Use `set N : IdeleGroup.normOneSubgroup E → IdeleGroup ℚ := fun z => ideleNorm ℚ E (z : IdeleGroup E) with hNdef`. Establish `hN : Continuous N` using `continuous_ideleNorm.comp continuous_subtype_val`. Use `set e : IdeleGroup.normOneSubgroup E → ℂ := fun z => ((ω.1 (N z) : ℂˣ) : ℂ) with he`.

Establish `hec : Continuous e` using `Units.continuous_val.comp (ω.2.1.comp hN)`. Set `f : IdeleGroup ℚ → IdeleGroup.normOneSubgroup E → ℂ` to `fun t z => c t * (e z * Bt M Φ ((N z)⁻¹ * t))`. Set `ν` to `(normOneMeasure E).restrict (normOneFundamentalDomain E)`. Use `haveI : IsFiniteMeasure ν := ⟨by simpa [ν] using normOneMeasure_normOneFundamentalDomain_lt_top E⟩`. Establish `hfc : Continuous (Function.uncurry f)` using `(hcc.comp continuous_fst).mul ((hec.comp continuous_snd).mul (hBc.comp ((hN.comp continuous_snd).inv.mul continuous_fst)))`.

Establish `hint : Integrable (Function.uncurry f) (U.υ.prod ν)`. Use `Integrable.of_bound hfc.aestronglyMeasurable (C * M.μ.real M.D) (ae_of_all _ fun p => ?_)` and prove the remaining obligations. Simplify using `only [Function.uncurry, f, norm_mul, hcn, one_mul]`. Rewrite using `[show ‖e p.2‖ = 1 from hω _, one_mul]`. Conclude with `hBb _`.

Establish `hsw` using `integral_integral_swap hint`. Establish `h1 : ∫ t, ∫ z, f t z ∂ν ∂U.υ = 0`. Establish `: ∀ t, ∫ z, f t z ∂ν = 0` using `fun t => by`. Simplify using `only [f]`. Rewrite using `[integral_const_mul]`.

Establish `h` using `UPer_eq D M hA.cen t`. Rewrite `h` using `[hU t]`. Rewrite using `[show ∫ z, e z * Bt M Φ ((N z)⁻¹ * t) ∂ν = 0 from h.symm, mul_zero]`. Simplify using `[this]`. Establish `h2 : ∀ z, ∫ t, f t z ∂U.υ = Per M U (ω⁻¹ * ε) Φ`.

Introduce `z`. Establish `hab : ab (N z)⁻¹ = 1`. Rewrite using `[ab_inv]`. Establish `: ab (N z) = 1`. Establish `h` using `GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ) (L := E) (z : IdeleGroup E)`.

Simplify using `only [ab, hNdef]`. Rewrite using `[h]`. Establish `hz : IdeleGroup.ideleModule E (z : IdeleGroup E) = 1` using `z.2`. Rewrite using `[hz]`. Both sides reduce to the same expression.

Rewrite using `[this, inv_one]`. Take `⟨r, u, hu, e1⟩` from `UpperTheory.rat_idele_eq_diagonal_mul_unit_of_abs_eq_one _ hab`. Establish `hεu : ε.1 u = 1`. Establish `h` using `congrArg ε.1 e1`. Rewrite `h` using `[map_inv, hεN, map_mul, hdiag, inv_one, one_mul]`.

Conclude with `h.symm`. Establish `hωu : ω.1 u = (ω.1 (N z)⁻¹)`. Rewrite using `[e1, map_mul, hdiag, one_mul]`. Establish `hcu : c u = e z`. Simplify using `only [hc, he, hcm, hεu, hωu, mul_one, map_inv, inv_inv]`.

Use `set G : IdeleGroup ℚ → ℂ := fun t => c t * Bt M Φ t with hG`. Establish `hGc : Continuous G` using `hcc.mul hBc`. Establish `hfG : ∀ t, f t z = G (u * t)` using `fun t => by`. Simplify using `only [f, hG, e1, mul_assoc]`. Rewrite using `[Bt_rat M hA.left]`.

Establish `: c (u * t) = c u * c t`. Simplify using `only [hc, map_mul, Units.val_mul]`. Rewrite using `[this, hcu]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hfG]`.

Establish `hm : Measurable fun x : IdeleGroup ℚ => (u * x : (A ℚ)ˣ)` using `(continuous_const.mul continuous_id).measurable`. Use `integral_map (μ := U.υ) hm.aemeasurable (f := G) hGc.aestronglyMeasurable` as an intermediate fact. Rewrite `this` using `[U.inv u hu]`. Conclude with `this.symm`. Rewrite `hsw` using `[h1]`.

Simplify using `only [h2, integral_const] at hsw`. Establish `hν : ν.real Set.univ ≠ 0`. Establish `hne : (normOneMeasure E) (normOneFundamentalDomain E) ≠ 0` using `(isFundamentalDomain_normOneFundamentalDomain E (normOneMeasure E)).measure_ne_zero (NeZero.ne _)`. Simplify using `only [ν, measureReal_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]`. Conclude with `ENNReal.toReal_ne_zero.2 ⟨hne, (normOneMeasure_normOneFundamentalDomain_lt_top E).ne⟩`.

Conclude with `(smul_eq_zero.1 hsw.symm).resolve_left hν`.
-/
private theorem per_zero (D : Dat ℚ E) (M : Meas ℚ) (U : UMeas) {ω ε : HChar ℚ} {Φ : GL (Fin 2) (A E) → ℂ}
    (hA : admitted D ω Φ) (hω : Unit1 ω) (hε : Unit1 ε) (hεN : ∀ z, ε.1 (ideleNorm ℚ E z) = 1)
    (hU : ∀ t, UPer D M (fun x => Φ (x * em E (dM t))) = 0) : Per M U (ω⁻¹ * ε) Φ = 0 := by
  obtain ⟨C, hC⟩ := hA.bdd
  haveI := U.prob
  have hBc := Bt_cont M hA.cont hC
  have hBb := Bt_bdd M hC
  have hdiag : ∀ (χ : HChar ℚ) (r : ℚˣ), χ.1 (IdeleGroup.diagonal ℚ r) = 1 := fun χ r => χ.2.2 r
  have hcm : ∀ t, (ω⁻¹ * ε).1 t = (ω.1 t)⁻¹ * ε.1 t := fun _ => rfl
  set c : IdeleGroup ℚ → ℂ := fun t => (((ω⁻¹ * ε).1 t : ℂˣ) : ℂ) with hc
  have hcc : Continuous c := Units.continuous_val.comp (ω⁻¹ * ε).2.1
  have hcn : ∀ t, ‖c t‖ = 1 := fun t => by
    simp only [hc, hcm, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
    rw [hω t, hε t]; simp
  set N : IdeleGroup.normOneSubgroup E → IdeleGroup ℚ := fun z => ideleNorm ℚ E (z : IdeleGroup E) with hNdef
  have hN : Continuous N := continuous_ideleNorm.comp continuous_subtype_val
  set e : IdeleGroup.normOneSubgroup E → ℂ := fun z => ((ω.1 (N z) : ℂˣ) : ℂ) with he
  have hec : Continuous e := Units.continuous_val.comp (ω.2.1.comp hN)
  let f : IdeleGroup ℚ → IdeleGroup.normOneSubgroup E → ℂ := fun t z => c t * (e z * Bt M Φ ((N z)⁻¹ * t))
  let ν := (normOneMeasure E).restrict (normOneFundamentalDomain E)
  haveI : IsFiniteMeasure ν := ⟨by simpa [ν] using normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  have hfc : Continuous (Function.uncurry f) :=
    (hcc.comp continuous_fst).mul ((hec.comp continuous_snd).mul
      (hBc.comp ((hN.comp continuous_snd).inv.mul continuous_fst)))
  have hint : Integrable (Function.uncurry f) (U.υ.prod ν) := by
    refine Integrable.of_bound hfc.aestronglyMeasurable (C * M.μ.real M.D) (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, f, norm_mul, hcn, one_mul]
    rw [show ‖e p.2‖ = 1 from hω _, one_mul]
    exact hBb _
  have hsw := integral_integral_swap hint
  have h1 : ∫ t, ∫ z, f t z ∂ν ∂U.υ = 0 := by
    have : ∀ t, ∫ z, f t z ∂ν = 0 := fun t => by
      simp only [f]
      rw [integral_const_mul]
      have h := UPer_eq D M hA.cen t
      rw [hU t] at h
      rw [show ∫ z, e z * Bt M Φ ((N z)⁻¹ * t) ∂ν = 0 from h.symm, mul_zero]
    simp [this]
  have h2 : ∀ z, ∫ t, f t z ∂U.υ = Per M U (ω⁻¹ * ε) Φ := by
    intro z
    have hab : ab (N z)⁻¹ = 1 := by
      rw [ab_inv]
      have : ab (N z) = 1 := by
        have h := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ) (L := E) (z : IdeleGroup E)
        simp only [ab, hNdef]
        rw [h]
        have hz : IdeleGroup.ideleModule E (z : IdeleGroup E) = 1 := z.2
        rw [hz]; rfl
      rw [this, inv_one]
    obtain ⟨r, u, hu, e1⟩ := UpperTheory.rat_idele_eq_diagonal_mul_unit_of_abs_eq_one _ hab
    have hεu : ε.1 u = 1 := by
      have h := congrArg ε.1 e1
      rw [map_inv, hεN, map_mul, hdiag, inv_one, one_mul] at h
      exact h.symm
    have hωu : ω.1 u = (ω.1 (N z)⁻¹) := by
      rw [e1, map_mul, hdiag, one_mul]
    have hcu : c u = e z := by
      simp only [hc, he, hcm, hεu, hωu, mul_one, map_inv, inv_inv]
    set G : IdeleGroup ℚ → ℂ := fun t => c t * Bt M Φ t with hG
    have hGc : Continuous G := hcc.mul hBc
    have hfG : ∀ t, f t z = G (u * t) := fun t => by
      simp only [f, hG, e1, mul_assoc]
      rw [Bt_rat M hA.left]
      have : c (u * t) = c u * c t := by
        simp only [hc, map_mul, Units.val_mul]
      rw [this, hcu]
      ring
    simp only [hfG]
    have hm : Measurable fun x : IdeleGroup ℚ => (u * x : (A ℚ)ˣ) := (continuous_const.mul continuous_id).measurable
    have := integral_map (μ := U.υ) hm.aemeasurable (f := G) hGc.aestronglyMeasurable
    rw [U.inv u hu] at this
    exact this.symm
  rw [h1] at hsw
  simp only [h2, integral_const] at hsw
  have hν : ν.real Set.univ ≠ 0 := by
    have hne : (normOneMeasure E) (normOneFundamentalDomain E) ≠ 0 :=
      (isFundamentalDomain_normOneFundamentalDomain E (normOneMeasure E)).measure_ne_zero (NeZero.ne _)
    simp only [ν, measureReal_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.toReal_ne_zero.2 ⟨hne, (normOneMeasure_normOneFundamentalDomain_lt_top E).ne⟩
  exact (smul_eq_zero.1 hsw.symm).resolve_left hν

end

end UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Introduce `E _ _ _ D W M _ P U ω hN hC hZ`. Establish `h1 : Unit1 ω` using `unitCharacter_of_central D hN hC`. Establish `hT : ∀ φ ∈ Tr P, admitted D ω φ` using `trAdm_of decE E D P ω ω⁻¹ hC h1 (fun a => by`. Rewrite using `[show (ω⁻¹ : HChar ℚ).1 a = (ω.1 a)⁻¹ from rfl, inv_mul_cancel, one_pow])`. Establish `key : ∀ ε : HChar ℚ, Unit1 ε → (∀ z, ε.1 (ideleNorm ℚ E z) = 1) → NoPer M U (ω⁻¹ * ε) P`.

Introduce `ε h1ε hεN f hf h`. Use `per_zero D M U (hT _ (Submodule.subset_span ⟨f, hf, h, rfl⟩)) h1 h1ε hεN fun t => ?_` and prove the remaining obligations. Take `⟨c, f', h', hf', e⟩` from `UpperTheory.cuspSubspace_translate_eq_smul_special_translate E P ω hC f hf (em E (dM t) * h)`. Establish `e2 : (fun x => (fun g => f.1 (g * h)) (x * em E (dM t))) = fun x => c * f'.1 (x * gl h')`. Use function extensionality and compare the values at `x`.

Simplify using `only [mul_assoc, e]`. Rewrite using `[e2]`. Establish `hZ'` using `hZ f' hf' h'`. Unfold `UPer UI SLP at hZ' ⊢`. Simplify using `only [mul_assoc] at hZ' ⊢`.

Simplify using `only [integral_const_mul]`. Rewrite using `[hZ', mul_zero]`. Establish `hη : Unit1 W.η⁻¹` using `fun a => by`. Establish `h` using `W.η_sq a`. Establish `h2 : ‖((W.η.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1`.

Rewrite using `[← norm_pow, ← Units.val_pow_eq_pow_val, h]`. Simplify using the standard rewrite rules. Establish `h3` using `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2`. Rewrite using `[show (W.η⁻¹ : HChar ℚ).1 a = (W.η.1 a)⁻¹ from rfl, Units.val_inv_eq_inv_val, norm_inv, h3, inv_one]`. Establish `k1` using `key 1 (fun a => by simp) (fun z => rfl)`.

Establish `k2` using `key W.η⁻¹ hη (fun z => by`. Rewrite using `[show (W.η⁻¹ : HChar ℚ).1 (ideleNorm ℚ E z) = (W.η.1 (ideleNorm ℚ E z))⁻¹ from rfl, W.η_norm, inv_one])`. Rewrite `k1` using `[mul_one]`. Rewrite using `[mul_inv]`. Conclude with `⟨k1, k2⟩`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.perU_of :
    PerU := by
  intro E _ _ _ D W M _ P U ω hN hC hZ
  have h1 : Unit1 ω := unitCharacter_of_central D hN hC
  have hT : ∀ φ ∈ Tr P, admitted D ω φ := trAdm_of decE E D P ω ω⁻¹ hC h1 (fun a => by
    rw [show (ω⁻¹ : HChar ℚ).1 a = (ω.1 a)⁻¹ from rfl, inv_mul_cancel, one_pow])
  have key : ∀ ε : HChar ℚ, Unit1 ε → (∀ z, ε.1 (ideleNorm ℚ E z) = 1) → NoPer M U (ω⁻¹ * ε) P := by
    intro ε h1ε hεN f hf h
    refine per_zero D M U (hT _ (Submodule.subset_span ⟨f, hf, h, rfl⟩)) h1 h1ε hεN fun t => ?_
    obtain ⟨c, f', h', hf', e⟩ := UpperTheory.cuspSubspace_translate_eq_smul_special_translate E P ω hC f hf (em E (dM t) * h)
    have e2 : (fun x => (fun g => f.1 (g * h)) (x * em E (dM t))) = fun x => c * f'.1 (x * gl h') := by
      funext x
      simp only [mul_assoc, e]
    rw [e2]
    have hZ' := hZ f' hf' h'
    unfold UPer UI SLP at hZ' ⊢
    simp only [mul_assoc] at hZ' ⊢
    simp only [integral_const_mul]
    rw [hZ', mul_zero]
  have hη : Unit1 W.η⁻¹ := fun a => by
    have h := W.η_sq a
    have h2 : ‖((W.η.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, h]; simp
    have h3 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
    rw [show (W.η⁻¹ : HChar ℚ).1 a = (W.η.1 a)⁻¹ from rfl, Units.val_inv_eq_inv_val, norm_inv, h3, inv_one]
  have k1 := key 1 (fun a => by simp) (fun z => rfl)
  have k2 := key W.η⁻¹ hη (fun z => by
    rw [show (W.η⁻¹ : HChar ℚ).1 (ideleNorm ℚ E z) = (W.η.1 (ideleNorm ℚ E z))⁻¹ from rfl, W.η_norm, inv_one])
  rw [mul_one] at k1
  rw [mul_inv]
  exact ⟨k1, k2⟩
