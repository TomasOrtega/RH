import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.AbsUnf
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.QuadraticFormRationalPoints
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.BddE
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DiagInvVal
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CdMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
open scoped Classical ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private noncomputable def hoD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : G1 F ≃ₜ G1 F :=
  ⟨⟨cD t, cD t⁻¹, fun g => by rw [← cD_mul_left, inv_mul_cancel, cD_one_left],
      fun g => by rw [← cD_mul_left, mul_inv_cancel, cD_one_left]⟩,
    M.continuous_cD t, M.continuous_cD t⁻¹⟩

/- English proof (translation)
The claim follows from `(hoD t).measurableEmbedding`.
-/
private theorem emb_cD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : MeasurableEmbedding (cD t : G1 F → G1 F) :=
  (hoD t).measurableEmbedding

private noncomputable def tau {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (z : (A E)ˣ) : (A E)ˣ :=
  Units.map ((am E : A ℚ →+* A E) : A ℚ →* A E) (ideleNorm ℚ E z)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [em, dM, Matrix.GeneralLinearGroup.map]`.
-/
private theorem em_dM {E : Type} [Field E] [NumberField E] (t : (A ℚ)ˣ) :
    em E (dM t) = dM (Units.map ((am E : A ℚ →+* A E) : A ℚ →* A E) t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [em, dM, Matrix.GeneralLinearGroup.map]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, hsc, -, -⟩` from `UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D`. Establish `e : em E (dM (ideleNorm ℚ E z)⁻¹) = (dM (tau z))⁻¹`. Rewrite using `[em_dM, map_inv, dM_inv]`. Both sides reduce to the same expression. Rewrite using `[hsc, e, gl_cD]`.

Rewrite using `[← mul_assoc, ← UpperTheory.ConvolutionTheory.R2.scalar_comm z (gl u)]`. Use `group`.
-/
private theorem gl_scalarCenter_commute {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ) (u : G1 E) :
    gl u * sZ D z = sZ D z * gl (cD (tau z) u) := by
  obtain ⟨-, -, -, -, -, -, -, -, hsc, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  have e : em E (dM (ideleNorm ℚ E z)⁻¹) = (dM (tau z))⁻¹ := by
    rw [em_dM, map_inv, dM_inv]; rfl
  rw [hsc, e, gl_cD]
  rw [← mul_assoc, ← UpperTheory.ConvolutionTheory.R2.scalar_comm z (gl u)]
  group

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, hc, -, -, -⟩` from `UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D`. Apply `gl_injective` to reduce the goal to its premises. Establish `h1` using `gl_scalarCenter_commute D z (j (cD (ideleNorm ℚ E z)⁻¹ g))`. Rewrite `h1` using `[hj, ← hc, ← hj]`. Conclude with `(mul_left_cancel h1).symm`.
-/
private theorem cD_j {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ)
    (j : G1 ℚ →* G1 E) (hj : ∀ g, gl (j g) = em E (gl g)) (g : G1 ℚ) :
    cD (tau z) (j (cD (ideleNorm ℚ E z)⁻¹ g)) = j g := by
  obtain ⟨-, -, -, -, -, -, -, hc, -, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  apply gl_injective
  have h1 := gl_scalarCenter_commute D z (j (cD (ideleNorm ℚ E z)⁻¹ g))
  rw [hj, ← hc, ← hj] at h1
  exact (mul_left_cancel h1).symm

/- English proof (translation)
Take `⟨-, -, -, -, ha, -, -, -, -, -, -⟩` from `UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D`. Establish `h0 : D.act (sZ D z)⁻¹ (rp X0) = rp X0` using `by conv_lhs => rw [← ha z]`. Conclude with `D.act_inv_act _ _`. Substitute `huh` using the available equality. Rewrite using `[← D.act_mul, gl_mul, mul_assoc, gl_scalarCenter_commute D z u]`.

Establish `: (gl r * (sZ D z * gl (cD (tau z) u)))⁻¹ * gl r = (gl (cD (tau z) u))⁻¹ * (sZ D z)⁻¹` using `by group`. Rewrite using `[this, D.act_mul, h0]`.
-/
private theorem galoisBaseChangeSchemeAction_comp_snd {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ) (h u r : G1 E)
    (huh : h = r * u) :
    D.act (gl h * sZ D z)⁻¹ (D.act (gl r) (rp X0)) = D.act (gl (cD (tau z) u))⁻¹ (rp X0) := by
  obtain ⟨-, -, -, -, ha, -, -, -, -, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  have h0 : D.act (sZ D z)⁻¹ (rp X0) = rp X0 := by
    conv_lhs => rw [← ha z]
    exact D.act_inv_act _ _
  subst huh
  rw [← D.act_mul, gl_mul, mul_assoc, gl_scalarCenter_commute D z u]
  have : (gl r * (sZ D z * gl (cD (tau z) u)))⁻¹ * gl r = (gl (cD (tau z) u))⁻¹ * (sZ D z)⁻¹ := by group
  rw [this, D.act_mul, h0]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem pY_eq {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (z : ↥(IdeleGroup.normOneSubgroup E)) (p : G1 E × Orb D.δ) :
    pY D (z, p) = D.act (gl p.1 * sZ D (z : IdeleGroup E))⁻¹ (rp p.2.1) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem el_eq {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (z : ↥(IdeleGroup.normOneSubgroup E)) (p : G1 E × Orb D.δ) :
    el D (z, p) = gl p.1 * sZ D (z : IdeleGroup E) := rfl

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

/- English proof (translation)
Introduce `E _ _ _ D W M N P φ hφ j hj c hc hcs Ψ hΨ z`. Take `⟨j', r, hj', hjc, hji, hr, hjΓ, hu⟩` from `UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.reps E D`. Establish `hjj : j' = j` using `MonoidHom.ext fun g => gl_injective ((hj' g).trans (hj g).symm)`. Substitute `hjj` using the available equality. Use `haveI := N.haar`.

Use `haveI := N.right`. Use `haveI := M.haar`. Use `haveI := M.right`. Use `haveI : DiscreteMeasurableSpace (Orb D.δ) := ⟨fun _ => trivial⟩`. Use `haveI : Countable (Orb D.δ) := inferInstance`.

Take `⟨hcont, hleft⟩` from `(UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ).1`. Simplify using `only [pY_eq, el_eq]`. Generalize the expression as in `((z : IdeleGroup E) : (A E)ˣ) = zz`. Establish `hmpE : MeasurePreserving (cD (tau zz)) N.μ N.μ` using `(UpperTheory.ConvolutionTheory.RankTwoDescent.invE E N).1 _`. Establish `hmpQ : MeasurePreserving (cD (ideleNorm ℚ E zz)⁻¹ : G1 ℚ → G1 ℚ) M.μ M.μ` using `UpperTheory.ConvolutionTheory.R2.M.cdMeas ℚ M _`.

Establish `hq : ∀ F : G1 ℚ → ℂ, ∫ g, F (cD (ideleNorm ℚ E zz)⁻¹ g) ∂M.μ = ∫ g, F g ∂M.μ` using `fun F => hmpQ.integral_comp (emb_cD _) F`. Take `⟨cs, hcsd⟩ : ∃ cs : G1 E → ℂ, ∀ y, cs y = c (cD (tau zz) y)` from `⟨_, fun _ => rfl⟩`. Take `⟨f, hfd⟩ : ∃ f : G1 E → ℂ, ∀ x, f x = φ.1 (gl x * sZ D zz)` from `⟨_, fun _ => rfl⟩`. Establish `hcsC : Continuous cs`. Rewrite using `[show cs = c ∘ cD (tau zz) from funext hcsd]`.

Conclude with `hc.comp (UpperTheory.ConvolutionTheory.R2.M.continuous_cD _)`. Establish `hfC : Continuous f`. Rewrite using `[show f = fun x => φ.1 (gl x * sZ D zz) from funext hfd]`. Conclude with `hcont.comp (continuous_gl.mul continuous_const)`. Establish `hcsS : HasCompactSupport cs`.

Rewrite using `[show cs = c ∘ hoD (tau zz) from funext hcsd]`. Conclude with `hcs.comp_homeomorph _`. Establish `hΨ' : ∀ (h : G1 E) (ξ : Orb D.δ), Ψ (D.act (gl h * sZ D zz)⁻¹ (rp ξ.1)) = ∫ g, cs (j' g * ((r ξ)⁻¹ * h)) ∂M.μ`. Introduce `h ξ`. Establish `e1 : D.act (gl h * sZ D zz)⁻¹ (rp ξ.1) = D.act (gl (cD (tau zz) ((r ξ)⁻¹ * h)))⁻¹ (rp X0)`.

Rewrite using `[(hr ξ).2]`. Conclude with `galoisBaseChangeSchemeAction_comp_snd D zz h _ (r ξ) (by group)`. Rewrite using `[e1, hΨ, ← hq fun g => cs (j' g * ((r ξ)⁻¹ * h))]`. Use `integral_congr_ae (ae_of_all _ fun g => ?_)` and prove the remaining obligations. Simplify using `only [hcsd]`.

Rewrite using `[UpperTheory.ConvolutionTheory.R2.cD_mul _ (j' _) _, cD_j D zz j' hj' g]`. Establish `hB : ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B`. Take `⟨B, hB⟩` from `UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.bddE E P φ hφ {sZ D zz} isCompact_singleton`. Conclude with `⟨B, fun x => by rw [hfd]; exact hB x _ rfl⟩`. Establish `hinv : ∀ γ ∈ Gam E, ∀ x, f (γ * x) = f x`.

Introduce and unpack `_ ⟨γ, rfl⟩ x`. Rewrite using `[hfd, hfd, gl_mul, gl_ratS, mul_assoc, hleft]`. Take `⟨h1, h2⟩` from `UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.absUnf (G1 E) (G1 ℚ) (Orb D.δ) N.μ M.μ j' (Gam E) (Gam ℚ) N.D M.D r f cs hjc hji N.fund M.fund (UpperTheory.ConvolutionTheory.R2.M.volD ℚ M) (fun i => (hr i).1) hjΓ hu hfC.measurable hinv hB hcsC.measurable (hcsC.integrable_of_hasCo …`. Establish `hL : ∀ p : G1 E × Orb D.δ, Ψ (D.act (gl p.1 * sZ D zz)⁻¹ (rp p.2.1)) * φ.1 (gl p.1 * sZ D zz) = (∫ g, cs (j' g * ((r p.2)⁻¹ * p.1)) ∂M.μ) * f p.1`. Introduce and unpack `⟨h, ξ⟩`.

Rewrite using `[hΨ', hfd]`. Use `⟨fun B hBB => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [hL]`. Use `(h1 B (fun h => by rw [hfd]; exact hBB h)).trans_eq ?_` and prove the remaining obligations. Rewrite using `[show (∫⁻ y, ‖cs y‖ₑ ∂N.μ) = ∫⁻ y, ‖c y‖ₑ ∂N.μ by`.

Simplify using `only [hcsd]`. Conclude with `hmpE.lintegral_comp_emb (emb_cD _) fun y => ‖c y‖ₑ]`. Simplify using `only [hL]`. Rewrite using `[h2]`. Use `hmpE.integral_comp (emb_cD (tau zz)) fun y => c y * SLP M fun x => φ.1 (x * sZ D zz * gl y)` as an intermediate fact.

Rewrite using `[← this]`. Use `integral_congr_ae (ae_of_all _ fun y => ?_)` and prove the remaining obligations. Simplify using `only [hcsd, SLP]`. Use `congr 1`. Use `integral_congr_ae (ae_of_all _ fun g => ?_)` and prove the remaining obligations.

Simplify using `only [hfd]`. Rewrite using `[gl_mul, hj', mul_assoc, gl_scalarCenter_commute D zz y, mul_assoc]`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.zOne :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.ZOne := by
  intro E _ _ _ D W M N P φ hφ j hj c hc hcs Ψ hΨ z
  obtain ⟨j', r, hj', hjc, hji, hr, hjΓ, hu⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.reps E D
  have hjj : j' = j := MonoidHom.ext fun g => gl_injective ((hj' g).trans (hj g).symm)
  subst hjj
  haveI := N.haar
  haveI := N.right
  haveI := M.haar
  haveI := M.right
  haveI : DiscreteMeasurableSpace (Orb D.δ) := ⟨fun _ => trivial⟩
  haveI : Countable (Orb D.δ) := inferInstance
  obtain ⟨hcont, hleft⟩ := (UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ).1
  simp only [pY_eq, el_eq]
  generalize ((z : IdeleGroup E) : (A E)ˣ) = zz
  have hmpE : MeasurePreserving (cD (tau zz)) N.μ N.μ := (UpperTheory.ConvolutionTheory.RankTwoDescent.invE E N).1 _
  have hmpQ : MeasurePreserving (cD (ideleNorm ℚ E zz)⁻¹ : G1 ℚ → G1 ℚ) M.μ M.μ := UpperTheory.ConvolutionTheory.R2.M.cdMeas ℚ M _
  have hq : ∀ F : G1 ℚ → ℂ, ∫ g, F (cD (ideleNorm ℚ E zz)⁻¹ g) ∂M.μ = ∫ g, F g ∂M.μ :=
    fun F => hmpQ.integral_comp (emb_cD _) F
  obtain ⟨cs, hcsd⟩ : ∃ cs : G1 E → ℂ, ∀ y, cs y = c (cD (tau zz) y) := ⟨_, fun _ => rfl⟩
  obtain ⟨f, hfd⟩ : ∃ f : G1 E → ℂ, ∀ x, f x = φ.1 (gl x * sZ D zz) := ⟨_, fun _ => rfl⟩
  have hcsC : Continuous cs := by
    rw [show cs = c ∘ cD (tau zz) from funext hcsd]
    exact hc.comp (UpperTheory.ConvolutionTheory.R2.M.continuous_cD _)
  have hfC : Continuous f := by
    rw [show f = fun x => φ.1 (gl x * sZ D zz) from funext hfd]
    exact hcont.comp (continuous_gl.mul continuous_const)
  have hcsS : HasCompactSupport cs := by
    rw [show cs = c ∘ hoD (tau zz) from funext hcsd]
    exact hcs.comp_homeomorph _
  have hΨ' : ∀ (h : G1 E) (ξ : Orb D.δ), Ψ (D.act (gl h * sZ D zz)⁻¹ (rp ξ.1)) = ∫ g, cs (j' g * ((r ξ)⁻¹ * h)) ∂M.μ := by
    intro h ξ
    have e1 : D.act (gl h * sZ D zz)⁻¹ (rp ξ.1) = D.act (gl (cD (tau zz) ((r ξ)⁻¹ * h)))⁻¹ (rp X0) := by
      rw [(hr ξ).2]
      exact galoisBaseChangeSchemeAction_comp_snd D zz h _ (r ξ) (by group)
    rw [e1, hΨ, ← hq fun g => cs (j' g * ((r ξ)⁻¹ * h))]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hcsd]
    rw [UpperTheory.ConvolutionTheory.R2.cD_mul _ (j' _) _, cD_j D zz j' hj' g]
  have hB : ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B := by
    obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.bddE E P φ hφ {sZ D zz} isCompact_singleton
    exact ⟨B, fun x => by rw [hfd]; exact hB x _ rfl⟩
  have hinv : ∀ γ ∈ Gam E, ∀ x, f (γ * x) = f x := by
    rintro _ ⟨γ, rfl⟩ x
    rw [hfd, hfd, gl_mul, gl_ratS, mul_assoc, hleft]
  obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.absUnf (G1 E) (G1 ℚ) (Orb D.δ) N.μ M.μ j' (Gam E) (Gam ℚ) N.D M.D r f cs hjc hji N.fund M.fund
    (UpperTheory.ConvolutionTheory.R2.M.volD ℚ M) (fun i => (hr i).1) hjΓ hu hfC.measurable hinv hB hcsC.measurable (hcsC.integrable_of_hasCompactSupport hcsS)
  have hL : ∀ p : G1 E × Orb D.δ, Ψ (D.act (gl p.1 * sZ D zz)⁻¹ (rp p.2.1)) * φ.1 (gl p.1 * sZ D zz) =
      (∫ g, cs (j' g * ((r p.2)⁻¹ * p.1)) ∂M.μ) * f p.1 := by
    rintro ⟨h, ξ⟩
    rw [hΨ', hfd]
  refine ⟨fun B hBB => ?_, ?_⟩
  · simp only [hL]
    refine (h1 B (fun h => by rw [hfd]; exact hBB h)).trans_eq ?_
    rw [show (∫⁻ y, ‖cs y‖ₑ ∂N.μ) = ∫⁻ y, ‖c y‖ₑ ∂N.μ by
      simp only [hcsd]; exact hmpE.lintegral_comp_emb (emb_cD _) fun y => ‖c y‖ₑ]
  · simp only [hL]
    rw [h2]
    have := hmpE.integral_comp (emb_cD (tau zz)) fun y => c y * SLP M fun x => φ.1 (x * sZ D zz * gl y)
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hcsd, SLP]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hfd]
    rw [gl_mul, hj', mul_assoc, gl_scalarCenter_commute D zz y, mul_assoc]
