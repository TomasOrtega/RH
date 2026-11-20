import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section SlopeTestRemainingChoices

variable {V M : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup M] [NormedSpace ℝ M]

end SlopeTestRemainingChoices

open LineDeriv in
/- English proof (translation)
Unfold `UpperTheory.V.Af.Smo.PftMul`. Introduce `V M _ _ _ _ _ _ _ _ G`. Establish `hbd : ∃ C, ∀ (z : V × M), ‖pft (⇑G) z‖ ≤ C` using `by set k : ℕ := Module.finrank ℝ V + 1 with hk set C0 : ℝ := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) G with hC0`. Establish `hint : Integrable (fun ξ : V ↦ (1 + ‖ξ‖) ^ (-(k : ℝ)))`. Apply `integrable_one_add_norm` to reduce the goal to its premises.

Rewrite using `[hk]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨C0 * ∫ ξ : V, (1 + ‖ξ‖) ^ (-(k : ℝ)), fun z ↦ ?_⟩` and prove the remaining obligations. Establish `hpt : ∀ ξ : V, ‖G (ξ, z.2)‖ ≤ C0 * (1 + ‖ξ‖) ^ (-(k : ℝ))`.

Introduce `ξ`. Establish `h` using `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (le_refl k) (le_refl 0) G (ξ, z.2)`. Rewrite `h` using `[norm_iteratedFDeriv_zero]`. Establish `hpos : 0 < 1 + ‖ξ‖` using `by positivity`. Establish `hn : ‖ξ‖ ≤ ‖((ξ, z.2) : V × M)‖` using `norm_fst_le ((ξ, z.2) : V × M)`.

Establish `hle : (1 + ‖ξ‖) ^ k ≤ (1 + ‖((ξ, z.2) : V × M)‖) ^ k` using `by gcongr`. Rewrite using `[Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm]`. Use `gcongr`.

Use `_ ≤ C0 := h`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [pft, Real.fourier_eq]`. Use `_ ≤ ∫ ξ : V, ‖𝐞 (-⟪ξ, z.1⟫) • G (ξ, z.2)‖ := norm_integral_le_integral_norm _`. Use `_ = ∫ ξ : V, ‖G (ξ, z.2)‖ := by simp [Circle.norm_smul]`.

Use `_ ≤ ∫ ξ : V, C0 * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by`. Apply `integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) (hint.const_mul C0)` to reduce the goal to its premises. Conclude with `Filter.Eventually.of_forall hpt`. Use `_ = C0 * ∫ ξ : V, (1 + ‖ξ‖) ^ (-(k : ℝ)) := integral_const_mul _ _`. Use `⟨hbd, fun l ↦ ?_⟩` and prove the remaining obligations.

Use `set l1 : V →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ V M) with hl1`. Use `set w : V := (InnerProductSpace.toDual ℝ V).symm l1 with hw`. Establish `hwl : ∀ ξ : V, ⟪ξ, w⟫ = l1 ξ`. Introduce `ξ`. Rewrite using `[real_inner_comm, hw, InnerProductSpace.toDual_symm_apply]`.

Use `set L2 : V × M →L[ℝ] ℂ := Complex.ofRealCLM.comp (l.comp ((ContinuousLinearMap.inr ℝ V M).comp (ContinuousLinearMap.snd ℝ V M))) with hL2`. Establish `hL2t : Function.HasTemperateGrowth (⇑L2)` using `L2.hasTemperateGrowth`. Use `set c : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹ with hc`. Use `⟨c • LineDeriv.lineDerivOp ((w, (0 : M)) : V × M) G + SchwartzMap.smulLeftCLM ℂ (⇑L2) G, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`.

Take `⟨v, m⟩` from `z`. Establish `hg : Function.HasTemperateGrowth (fun ξ : V => (ξ, m))`. Establish `h1 : Function.HasTemperateGrowth (fun ξ : V => ((ContinuousLinearMap.inl ℝ V M) ξ + ((0 : V), m)))` using `(ContinuousLinearMap.inl ℝ V M).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)`. Use `h1 using 2 with ξ` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules.

Establish `hgu : ∃ (k : ℕ) (C : ℝ), ∀ ξ : V, ‖ξ‖ ≤ C * (1 + ‖((ξ, m) : V × M)‖) ^ k`. Use `⟨1, 1, fun ξ ↦ ?_⟩` and prove the remaining obligations. Establish `hn : ‖ξ‖ ≤ ‖((ξ, m) : V × M)‖` using `norm_fst_le ((ξ, m) : V × M)`. Simplify using `only [pow_one, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set S : 𝓢(V, ℂ) := SchwartzMap.compCLM ℝ hg hgu G with hS`. Establish `hSa : ∀ ξ, S ξ = G (ξ, m)` using `fun ξ ↦ by`. Rewrite using `[hS, SchwartzMap.compCLM_apply]`. Both sides reduce to the same expression. Establish `hder : ∀ ξ : V, fderiv ℝ (⇑S) ξ w = fderiv ℝ (⇑G) (ξ, m) (w, 0)`.

Introduce `ξ`. Establish `hgd : HasFDerivAt (fun η : V => ((η, m) : V × M)) ((ContinuousLinearMap.id ℝ V).prod 0) ξ` using `(hasFDerivAt_id ξ).prodMk (hasFDerivAt_const m ξ)`. Establish `hGd : HasFDerivAt (⇑G) (fderiv ℝ (⇑G) (ξ, m)) (ξ, m)` using `(G.differentiableAt).hasFDerivAt`. Establish `hc'` using `hGd.comp ξ hgd`. Establish `hSf : (⇑S) = (⇑G) ∘ (fun η : V => ((η, m) : V × M))`.

Use function extensionality and compare the values at `η`. Conclude with `hSa η`. Rewrite using `[hSf, hc'.fderiv]`. Simplify using the standard rewrite rules. Establish `key : (fun ξ : V => (c • LineDeriv.lineDerivOp ((w, (0 : M)) : V × M) G + SchwartzMap.smulLeftCLM ℂ (⇑L2) G) (ξ, m)) = ⇑(c • LineDeriv.lineDerivOp w S + ((l (0, m) : ℝ) : ℂ) • S)`.

Use function extensionality and compare the values at `ξ`. Simplify using `only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL2t, SchwartzMap.lineDerivOp_apply_eq_fderiv, hder, hSa]`. Simplify using `[hL2, smul_eq_mul]`. Simplify using `only [pft]`. Rewrite using `[key, ← SchwartzMap.fourier_coe]`.

Simplify using `only [FourierTransform.fourier_add, FourierTransform.fourier_smul, SchwartzMap.fourier_lineDerivOp_eq]`. Establish `hSf' : (fun ξ : V => G (ξ, m)) = ⇑S`. Use function extensionality and compare the values at `ξ`. Conclude with `(hSa ξ).symm`. Establish `hit : Function.HasTemperateGrowth (fun x : V ↦ ⟪x, w⟫)` using `((innerSL ℝ).flip w).hasTemperateGrowth`.

Rewrite using `[hSf', ← SchwartzMap.fourier_coe]`. Simplify using `only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hit]`. Simplify using `only [hwl]`. Establish `hlv : l (v, m) = l1 v + l (0, m)`. Rewrite using `[hl1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ← map_add]`.

Simplify using the standard rewrite rules. Rewrite using `[hlv, hc]`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Simplify using `only [smul_eq_mul, Complex.real_smul]`. Clear the denominators using the available nonvanishing facts.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Af.Smo.pftMul :
    UpperTheory.V.Af.Smo.PftMul := by
  unfold UpperTheory.V.Af.Smo.PftMul
  intro V M _ _ _ _ _ _ _ _ G
  have hbd : ∃ C, ∀ (z : V × M), ‖pft (⇑G) z‖ ≤ C := by
    set k : ℕ := Module.finrank ℝ V + 1 with hk
    set C0 : ℝ := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) G with hC0
    have hint : Integrable (fun ξ : V ↦ (1 + ‖ξ‖) ^ (-(k : ℝ))) := by
      apply integrable_one_add_norm
      rw [hk]; push_cast; linarith
    refine ⟨C0 * ∫ ξ : V, (1 + ‖ξ‖) ^ (-(k : ℝ)), fun z ↦ ?_⟩
    have hpt : ∀ ξ : V, ‖G (ξ, z.2)‖ ≤ C0 * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
      intro ξ
      have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (le_refl k) (le_refl 0) G (ξ, z.2)
      rw [norm_iteratedFDeriv_zero] at h
      have hpos : 0 < 1 + ‖ξ‖ := by positivity
      have hn : ‖ξ‖ ≤ ‖((ξ, z.2) : V × M)‖ := norm_fst_le ((ξ, z.2) : V × M)
      have hle : (1 + ‖ξ‖) ^ k ≤ (1 + ‖((ξ, z.2) : V × M)‖) ^ k := by
        gcongr
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖G (ξ, z.2)‖ * (1 + ‖ξ‖) ^ k ≤ (1 + ‖((ξ, z.2) : V × M)‖) ^ k * ‖G (ξ, z.2)‖ := by
            rw [mul_comm]; gcongr
        _ ≤ C0 := h
    calc ‖pft (⇑G) z‖ = ‖∫ ξ : V, 𝐞 (-⟪ξ, z.1⟫) • G (ξ, z.2)‖ := by
          simp only [pft, Real.fourier_eq]
      _ ≤ ∫ ξ : V, ‖𝐞 (-⟪ξ, z.1⟫) • G (ξ, z.2)‖ := norm_integral_le_integral_norm _
      _ = ∫ ξ : V, ‖G (ξ, z.2)‖ := by simp [Circle.norm_smul]
      _ ≤ ∫ ξ : V, C0 * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) (hint.const_mul C0)
          exact Filter.Eventually.of_forall hpt
      _ = C0 * ∫ ξ : V, (1 + ‖ξ‖) ^ (-(k : ℝ)) := integral_const_mul _ _
  refine ⟨hbd, fun l ↦ ?_⟩
  set l1 : V →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ V M) with hl1
  set w : V := (InnerProductSpace.toDual ℝ V).symm l1 with hw
  have hwl : ∀ ξ : V, ⟪ξ, w⟫ = l1 ξ := by
    intro ξ
    rw [real_inner_comm, hw, InnerProductSpace.toDual_symm_apply]
  set L2 : V × M →L[ℝ] ℂ := Complex.ofRealCLM.comp
    (l.comp ((ContinuousLinearMap.inr ℝ V M).comp (ContinuousLinearMap.snd ℝ V M))) with hL2
  have hL2t : Function.HasTemperateGrowth (⇑L2) := L2.hasTemperateGrowth
  set c : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹ with hc
  refine ⟨c • LineDeriv.lineDerivOp ((w, (0 : M)) : V × M) G + SchwartzMap.smulLeftCLM ℂ (⇑L2) G, ?_⟩
  funext z
  obtain ⟨v, m⟩ := z
  have hg : Function.HasTemperateGrowth (fun ξ : V => (ξ, m)) := by
    have h1 : Function.HasTemperateGrowth (fun ξ : V => ((ContinuousLinearMap.inl ℝ V M) ξ + ((0 : V), m))) :=
      (ContinuousLinearMap.inl ℝ V M).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    convert h1 using 2 with ξ
    simp
  have hgu : ∃ (k : ℕ) (C : ℝ), ∀ ξ : V, ‖ξ‖ ≤ C * (1 + ‖((ξ, m) : V × M)‖) ^ k := by
    refine ⟨1, 1, fun ξ ↦ ?_⟩
    have hn : ‖ξ‖ ≤ ‖((ξ, m) : V × M)‖ := norm_fst_le ((ξ, m) : V × M)
    simp only [pow_one, one_mul]
    linarith
  set S : 𝓢(V, ℂ) := SchwartzMap.compCLM ℝ hg hgu G with hS
  have hSa : ∀ ξ, S ξ = G (ξ, m) := fun ξ ↦ by
    rw [hS, SchwartzMap.compCLM_apply]; rfl
  have hder : ∀ ξ : V, fderiv ℝ (⇑S) ξ w = fderiv ℝ (⇑G) (ξ, m) (w, 0) := by
    intro ξ
    have hgd : HasFDerivAt (fun η : V => ((η, m) : V × M)) ((ContinuousLinearMap.id ℝ V).prod 0) ξ :=
      (hasFDerivAt_id ξ).prodMk (hasFDerivAt_const m ξ)
    have hGd : HasFDerivAt (⇑G) (fderiv ℝ (⇑G) (ξ, m)) (ξ, m) := (G.differentiableAt).hasFDerivAt
    have hc' := hGd.comp ξ hgd
    have hSf : (⇑S) = (⇑G) ∘ (fun η : V => ((η, m) : V × M)) := by
      funext η; exact hSa η
    rw [hSf, hc'.fderiv]
    simp
  have key : (fun ξ : V => (c • LineDeriv.lineDerivOp ((w, (0 : M)) : V × M) G + SchwartzMap.smulLeftCLM ℂ (⇑L2) G) (ξ, m))
      = ⇑(c • LineDeriv.lineDerivOp w S + ((l (0, m) : ℝ) : ℂ) • S) := by
    funext ξ
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL2t,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, hder, hSa]
    simp [hL2, smul_eq_mul]
  simp only [pft]
  rw [key, ← SchwartzMap.fourier_coe]
  simp only [FourierTransform.fourier_add, FourierTransform.fourier_smul, SchwartzMap.fourier_lineDerivOp_eq]
  have hSf' : (fun ξ : V => G (ξ, m)) = ⇑S := by
    funext ξ; exact (hSa ξ).symm
  have hit : Function.HasTemperateGrowth (fun x : V ↦ ⟪x, w⟫) := ((innerSL ℝ).flip w).hasTemperateGrowth
  rw [hSf', ← SchwartzMap.fourier_coe]
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hit]
  simp only [hwl]
  have hlv : l (v, m) = l1 v + l (0, m) := by
    rw [hl1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ← map_add]
    simp
  rw [hlv, hc]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [smul_eq_mul, Complex.real_smul]
  field_simp
  push_cast
  ring
