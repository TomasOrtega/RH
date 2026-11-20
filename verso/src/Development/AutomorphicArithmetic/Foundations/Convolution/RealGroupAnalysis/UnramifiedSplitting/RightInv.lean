import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
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
Introduce `K _ _ M u hu hint k`. Use `haveI := M.haar`. Use `haveI := M.right`. Use `haveI := countable_gam K`. Establish `hmp : MeasurePreserving (· * k) M.μ M.μ` using `measurePreserving_mul_right M.μ k`.

Establish `hemb : MeasurableEmbedding (· * k : G1 K → G1 K)` using `(MeasurableEquiv.mulRight k).measurableEmbedding`. Establish `hfd : IsFundamentalDomain (Gam K) ((Equiv.mulRight k) '' M.D) M.μ`. Use `M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_` and prove the remaining obligations. Conclude with `(measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving`. Introduce `g x`.

Simplify using `[Subgroup.smul_def, mul_assoc]`. Establish `hinv : ∀ (g : Gam K) x, u (g • x) = u x`. Introduce and unpack `⟨_, γ, rfl⟩ x`. Simplify `hu γ x` using `[Subgroup.smul_def]`. Establish `hpre : (· * k : G1 K → G1 K) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Establish `h1 : IntegrableOn u ((Equiv.mulRight k) '' M.D) M.μ` using `(M.fund.integrableOn_iff hfd hinv).1 hint`. Establish `h2` using `(hmp.integrableOn_comp_preimage hemb).2 h1`.

Rewrite `h2` using `[hpre]`. Then use the resulting hypothesis. Establish `h3` using `hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)`. Rewrite `h3` using `[hpre]`. Rewrite using `[h3]`. Conclude with `hfd.setIntegral_eq M.fund hinv`.
-/
theorem UpperTheory.ConvolutionTheory.R2.H.rightInv :
    ∀ (K : Type) [Field K] [NumberField K] (M : Meas K) (u : G1 K → ℂ), (∀ γ g, u (ratS K γ * g) = u g) → IntegrableOn u M.D M.μ →
      ∀ k, IntegrableOn (fun g => u (g * k)) M.D M.μ ∧ ∫ g in M.D, u (g * k) ∂M.μ = ∫ g in M.D, u g ∂M.μ := by
  intro K _ _ M u hu hint k
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
  constructor
  · have h1 : IntegrableOn u ((Equiv.mulRight k) '' M.D) M.μ :=
      (M.fund.integrableOn_iff hfd hinv).1 hint
    have h2 := (hmp.integrableOn_comp_preimage hemb).2 h1
    rwa [hpre] at h2
  · have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)
    rw [hpre] at h3
    rw [h3]
    exact hfd.setIntegral_eq M.fund hinv
