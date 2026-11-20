import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Use `haveI : Countable K := by`. Establish `: Module.Finite ℚ K` using `inferInstance`. Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' ℚ K`. Conclude with `hf.countable`. Use `haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))`.

Use `haveI : Countable (Matrix.SpecialLinearGroup (Fin 2) K) := Function.Injective.countable (f := fun g => (g.1 : Matrix (Fin 2) (Fin 2) K)) Subtype.val_injective`. Unfold `Gam`. Conclude with `(Set.countable_range (ratS K)).to_subtype`.
-/
private lemma countable_gam (K : Type) [Field K] [NumberField K] : Countable (Gam K) := by
  haveI : Countable K := by
    have : Module.Finite ℚ K := inferInstance
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℚ K
    exact hf.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Function.Injective.countable (f := fun g => (g.1 : Matrix (Fin 2) (Fin 2) K)) Subtype.val_injective
  unfold Gam
  exact (Set.countable_range (ratS K)).to_subtype

/- English proof (translation)
Use `haveI := M.haar`. Use `haveI := M.right`. Use `haveI := countable_gam K`. Establish `hmp : MeasurePreserving (· * k) M.μ M.μ` using `measurePreserving_mul_right M.μ k`. Establish `hemb : MeasurableEmbedding (· * k : G1 K → G1 K)` using `(MeasurableEquiv.mulRight k).measurableEmbedding`.

Establish `hfd : IsFundamentalDomain (Gam K) ((Equiv.mulRight k) '' M.D) M.μ`. Use `M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_` and prove the remaining obligations. Conclude with `(measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving`. Introduce `g x`. Simplify using `[Subgroup.smul_def, mul_assoc]`.

Establish `hinv : ∀ (g : Gam K) x, u (g • x) = u x`. Introduce and unpack `⟨_, γ, rfl⟩ x`. Simplify `hu γ x` using `[Subgroup.smul_def]`. Establish `hpre : (· * k : G1 K → G1 K) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Establish `h3` using `hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)`. Rewrite `h3` using `[hpre]`. Rewrite using `[h3]`. Conclude with `hfd.setIntegral_eq M.fund hinv`.
-/
private lemma setIntegral_mul_right (K : Type) [Field K] [NumberField K] (M : Meas K) (u : G1 K → ℂ)
    (hu : ∀ γ g, u (ratS K γ * g) = u g) (k : G1 K) :
    ∫ g in M.D, u (g * k) ∂M.μ = ∫ g in M.D, u g ∂M.μ := by
  haveI := M.haar
  haveI := M.right
  haveI := countable_gam K
  have hmp : MeasurePreserving (· * k) M.μ M.μ := measurePreserving_mul_right M.μ k
  have hemb : MeasurableEmbedding (· * k : G1 K → G1 K) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd : IsFundamentalDomain (Gam K) ((Equiv.mulRight k) '' M.D) M.μ := by
    refine M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  have hinv : ∀ (g : Gam K) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : (· * k : G1 K → G1 K) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D := by
    ext x; simp
  have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq M.fund hinv

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W M f hf φ g₀`. Use function extensionality and compare the values at `h`. Establish `hu : ∀ γ g, (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) (ratS F γ * g) = (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) g`. Introduce `γ g`. Establish `h1 : gl (ratS F γ * g) * dM (nu F h) * gl g₀⁻¹ = ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * (gl g * dM (nu F h) * gl g₀⁻¹)`.

Rewrite using `[gl_mul, gl_ratS]`. Use `group`. Establish `h2 : W.Om (ratS F γ * g) (W.L h φ) = W.Om (ratS F γ) (W.Om g (W.L h φ))`. Rewrite using `[map_mul, Module.End.mul_apply]`. Use `show f (gl (ratS F γ * g) * dM (nu F h) * gl g₀⁻¹) * Th (W.Om (ratS F γ * g) (W.L h φ)).1 = _`.

Rewrite using `[h1, hf, h2, W.th_Om]`. Establish `key` using `setIntegral_mul_right F M (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) hu (cD (nu F h) g₀)`. Use `Eq.trans (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)) key` and prove the remaining obligations. Establish `h1 : gl (g * cD (nu F h) g₀) * dM (nu F h) * gl g₀⁻¹ = gl g * dM (nu F h)`. Establish `hi : gl g₀⁻¹ = (gl g₀)⁻¹` using `map_inv Matrix.SpecialLinearGroup.toGL g₀`.

Rewrite using `[gl_mul, gl_cD, hi]`. Use `group`. Establish `h2 : W.L h (W.Om g₀ φ) = W.Om (cD (nu F h) g₀) (W.L h φ)`. Use `congrArg (fun T : Module.End ℂ (S4 F) => T φ) (W.comm h g₀)` as an intermediate fact. Simplify `this` using `only [Module.End.mul_apply]`.

Establish `h3 : W.Om (g * cD (nu F h) g₀) (W.L h φ) = W.Om g (W.L h (W.Om g₀ φ))`. Rewrite using `[h2, map_mul, Module.End.mul_apply]`. Use `show f (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om g₀ φ))).1 = f (gl (g * cD (nu F h) g₀) * dM (nu F h) * gl g₀⁻¹) * Th (W.Om (g * cD (nu F h) g₀) (W.L h φ)).1`. Rewrite using `[h1, h3]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.moveG :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ), (∀ γ g, f (ratGL F 2 γ * g) = f g) → ∀ (φ : S4 F) (g₀ : G1 F),
    lift W M f (W.Om g₀ φ) = lift W M (fun x => f (x * gl g₀⁻¹)) φ := by
  intro F E _ _ _ _ _ _ _ D W M f hf φ g₀
  funext h
  have hu : ∀ γ g, (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) (ratS F γ * g) =
      (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) g := by
    intro γ g
    have h1 : gl (ratS F γ * g) * dM (nu F h) * gl g₀⁻¹ =
        ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * (gl g * dM (nu F h) * gl g₀⁻¹) := by
      rw [gl_mul, gl_ratS]; group
    have h2 : W.Om (ratS F γ * g) (W.L h φ) = W.Om (ratS F γ) (W.Om g (W.L h φ)) := by
      rw [map_mul, Module.End.mul_apply]
    show f (gl (ratS F γ * g) * dM (nu F h) * gl g₀⁻¹) * Th (W.Om (ratS F γ * g) (W.L h φ)).1 = _
    rw [h1, hf, h2, W.th_Om]
  have key := setIntegral_mul_right F M (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) hu (cD (nu F h) g₀)
  refine Eq.trans (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)) key
  have h1 : gl (g * cD (nu F h) g₀) * dM (nu F h) * gl g₀⁻¹ = gl g * dM (nu F h) := by
    have hi : gl g₀⁻¹ = (gl g₀)⁻¹ := map_inv Matrix.SpecialLinearGroup.toGL g₀
    rw [gl_mul, gl_cD, hi]; group
  have h2 : W.L h (W.Om g₀ φ) = W.Om (cD (nu F h) g₀) (W.L h φ) := by
    have := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (W.comm h g₀)
    simpa only [Module.End.mul_apply] using this
  have h3 : W.Om (g * cD (nu F h) g₀) (W.L h φ) = W.Om g (W.L h (W.Om g₀ φ)) := by
    rw [h2, map_mul, Module.End.mul_apply]
  show f (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om g₀ φ))).1 =
    f (gl (g * cD (nu F h) g₀) * dM (nu F h) * gl g₀⁻¹) * Th (W.Om (g * cD (nu F h) g₀) (W.L h φ)).1
  rw [h1, h3]
