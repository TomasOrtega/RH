import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Introduce `E _ _ β hc hinv`. Establish `hf : Continuous fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E)` using `hc.comp continuous_subtype_val`. Establish `hcl` using `isCompact_closure_normOneFundamentalDomain E`. Establish `hinv' : ∀ (k : Eˣ) (u : IdeleGroup.normOneSubgroup E), β ((u * diagonalToNormOne E k : IdeleGroup.normOneSubgroup E) : IdeleGroup E) = β (u : IdeleGroup E)`. Introduce `k u`.

Establish `h` using `hinv k (u : IdeleGroup E)`. Rewrite `h` using `[mul_comm]`. Conclude with `h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hf.continuousOn.integrableOn_compact hcl).mono_set subset_closure`.

Take `⟨B, hB⟩` from `hcl.exists_bound_of_continuousOn hf.continuousOn`. Use `⟨B, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hm : t ∈ IdeleGroup.normOneSubgroup E`. Use `MonoidHom.mem_ker.2 (Subtype.ext ?_)` and prove the remaining obligations. Conclude with `ht`.

Take `⟨k, hk, -⟩` from `existsUnique_mul_mem_normOneFundamentalDomain E ⟨t, hm⟩`. Establish `h` using `hB _ (subset_closure hk)`. Rewrite `h` using `[hinv' k ⟨t, hm⟩]`. Then use the resulting hypothesis. Introduce `d hd`. Establish `hm : d ∈ IdeleGroup.normOneSubgroup E`.

Use `MonoidHom.mem_ker.2 (Subtype.ext ?_)` and prove the remaining obligations. Conclude with `hd`. Use `set b : IdeleGroup.normOneSubgroup E := ⟨d, hm⟩ with hb`. Use `set g : IdeleGroup.normOneSubgroup E → ℂ := fun z => β (z : IdeleGroup E) with hg`. Establish `hD` using `isFundamentalDomain_normOneFundamentalDomain E (normOneMeasure E)`.

Establish `hD'` using `hD.smul_of_comm b`. Establish `hI : ∀ (γ : (diagonalNormOne E).op) (x : IdeleGroup.normOneSubgroup E), g (γ • x) = g x`. Introduce and unpack `⟨γ, hγ⟩ x`. Take `⟨k, hk⟩` from `Subgroup.mem_op.1 hγ`. Establish `e : γ.unop = diagonalToNormOne E k` using `Subtype.ext hk.symm`.

Express the relevant statement in the definitionally equal form `g (x * γ.unop) = g x`. Rewrite using `[e]`. Conclude with `hinv' k x`. Establish `h1` using `hD.setIntegral_eq hD' hI`. Establish `h2` using `(measurePreserving_mul_left (normOneMeasure E) b).setIntegral_image_emb (MeasurableEquiv.mulLeft b).measurableEmbedding g (normOneFundamentalDomain E)`.

Unfold `UI`. Express the relevant statement in the definitionally equal form `∫ z in normOneFundamentalDomain E, g (z * b) ∂normOneMeasure E = ∫ z in normOneFundamentalDomain E, g z ∂normOneMeasure E`. Rewrite using `[h1]`. Repeatedly rewrite using `[mul_comm _ b]`. Conclude with `h2.symm`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.uiLaws :
    UILaws := by
  intro E _ _ β hc hinv
  have hf : Continuous fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E) :=
    hc.comp continuous_subtype_val
  have hcl := isCompact_closure_normOneFundamentalDomain E
  have hinv' : ∀ (k : Eˣ) (u : IdeleGroup.normOneSubgroup E),
      β ((u * diagonalToNormOne E k : IdeleGroup.normOneSubgroup E) : IdeleGroup E) = β (u : IdeleGroup E) := by
    intro k u
    have h := hinv k (u : IdeleGroup E)
    rw [mul_comm] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · exact (hf.continuousOn.integrableOn_compact hcl).mono_set subset_closure
  · obtain ⟨B, hB⟩ := hcl.exists_bound_of_continuousOn hf.continuousOn
    refine ⟨B, fun t ht => ?_⟩
    have hm : t ∈ IdeleGroup.normOneSubgroup E := by
      refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
      exact ht
    obtain ⟨k, hk, -⟩ := existsUnique_mul_mem_normOneFundamentalDomain E ⟨t, hm⟩
    have h := hB _ (subset_closure hk)
    rwa [hinv' k ⟨t, hm⟩] at h
  · intro d hd
    have hm : d ∈ IdeleGroup.normOneSubgroup E := by
      refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
      exact hd
    set b : IdeleGroup.normOneSubgroup E := ⟨d, hm⟩ with hb
    set g : IdeleGroup.normOneSubgroup E → ℂ := fun z => β (z : IdeleGroup E) with hg
    have hD := isFundamentalDomain_normOneFundamentalDomain E (normOneMeasure E)
    have hD' := hD.smul_of_comm b
    have hI : ∀ (γ : (diagonalNormOne E).op) (x : IdeleGroup.normOneSubgroup E), g (γ • x) = g x := by
      rintro ⟨γ, hγ⟩ x
      obtain ⟨k, hk⟩ := Subgroup.mem_op.1 hγ
      have e : γ.unop = diagonalToNormOne E k := Subtype.ext hk.symm
      change g (x * γ.unop) = g x
      rw [e]
      exact hinv' k x
    have h1 := hD.setIntegral_eq hD' hI
    have h2 := (measurePreserving_mul_left (normOneMeasure E) b).setIntegral_image_emb
      (MeasurableEquiv.mulLeft b).measurableEmbedding g (normOneFundamentalDomain E)
    unfold UI
    change ∫ z in normOneFundamentalDomain E, g (z * b) ∂normOneMeasure E = ∫ z in normOneFundamentalDomain E, g z ∂normOneMeasure E
    rw [h1]
    simp_rw [mul_comm _ b]
    exact h2.symm
