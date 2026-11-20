import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
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
