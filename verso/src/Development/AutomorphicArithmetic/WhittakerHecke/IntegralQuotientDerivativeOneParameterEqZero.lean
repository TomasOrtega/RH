import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapRDefs
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

/- English proof (translation)
Establish `hc : Continuous fun p : Y × ℝ => D (T p.2 p.1)` using `hD.comp hT`. Establish `h1 : ∀ y, ∫ u in Set.Ioc (0 : ℝ) 1, D (T u y) = H (T 1 y) - H (T 0 y)` using `fun y => by`. Rewrite using `[← intervalIntegral.integral_of_le zero_le_one]`. Conclude with `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd y u) ((hc.comp (Continuous.prodMk_right y)).intervalIntegrable _ _)`. Establish `hi : Integrable (Function.uncurry fun y u => D (T u y)) (ν.prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))`.

Use `(integrable_prod_iff' hc.aestronglyMeasurable).2 ⟨.of_forall fun u => ((hm u).integrable_comp_emb (he u)).2 iD, ?_⟩` and prove the remaining obligations. Establish `: (fun u => ∫ y, ‖D (T u y)‖ ∂ν) = fun _ => ∫ y, ‖D y‖ ∂ν` using `funext fun u => (hm u).integral_comp (he u) fun y => ‖D y‖`. Conclude with `this ▸ integrable_const _`. Establish `h2` using `integral_integral_swap hi`. Simplify using `only [h1, fun u => (hm u).integral_comp (he u) D] at h2`.

Establish `i : ∀ u, Integrable (fun x => H (T u x)) ν` using `fun u => ((hm u).integrable_comp_emb (he u)).2 iH`. Rewrite `h2` using `[integral_sub (i 1) (i 0), (hm 1).integral_comp (he 1) H, (hm 0).integral_comp (he 0) H]`. Simplify using `using h2.symm`.
-/
private theorem flow_abs {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    (ν : Measure Y) [SFinite ν] (T : ℝ → Y → Y) (hT : Continuous fun p : Y × ℝ => T p.2 p.1)
    (hm : ∀ u, MeasurePreserving (T u) ν ν) (he : ∀ u, MeasurableEmbedding (T u)) (H D : Y → ℂ) (hD : Continuous D)
    (iH : Integrable H ν) (iD : Integrable D ν) (hd : ∀ y u, HasDerivAt (fun s => H (T s y)) (D (T u y)) u) :
    ∫ y, D y ∂ν = 0 := by
  have hc : Continuous fun p : Y × ℝ => D (T p.2 p.1) := hD.comp hT
  have h1 : ∀ y, ∫ u in Set.Ioc (0 : ℝ) 1, D (T u y) = H (T 1 y) - H (T 0 y) := fun y => by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd y u)
      ((hc.comp (Continuous.prodMk_right y)).intervalIntegrable _ _)
  have hi : Integrable (Function.uncurry fun y u => D (T u y)) (ν.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine (integrable_prod_iff' hc.aestronglyMeasurable).2 ⟨.of_forall fun u => ((hm u).integrable_comp_emb (he u)).2 iD, ?_⟩
    have : (fun u => ∫ y, ‖D (T u y)‖ ∂ν) = fun _ => ∫ y, ‖D y‖ ∂ν := funext fun u => (hm u).integral_comp (he u) fun y => ‖D y‖
    exact this ▸ integrable_const _
  have h2 := integral_integral_swap hi
  simp only [h1, fun u => (hm u).integral_comp (he u) D] at h2
  have i : ∀ u, Integrable (fun x => H (T u x)) ν := fun u => ((hm u).integrable_comp_emb (he u)).2 iH
  rw [integral_sub (i 1) (i 0),
    (hm 1).integral_comp (he 1) H, (hm 0).integral_comp (he 0) H] at h2
  simpa using h2.symm

/- English proof (translation)
The claim follows from `(continuous_rightMul_prod Γ).comp (f := fun p : RightCosetSpace Γ × ℝ => (p.1, c p.2)) (continuous_fst.prodMk (hc.comp continuous_snd))`.
-/
private theorem flow_cont {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) (c : ℝ → G)
    (hc : Continuous c) : Continuous fun p : RightCosetSpace Γ × ℝ => rightMul Γ (c p.2) p.1 :=
  (continuous_rightMul_prod Γ).comp (f := fun p : RightCosetSpace Γ × ℝ => (p.1, c p.2))
    (continuous_fst.prodMk (hc.comp continuous_snd))

/- English proof (translation)
Introduce `E _ _ r h D c hh hD cD cc _ cadd c1 hd ih iD`. Establish `e : ∀ {f : GA E r → ℂ} (hf : AutomorphicForm.IsLeftInvariant f), onQ f = CuspidalSpectrum.cuspQuot hf` using `fun hf => by`. Use function extensionality and compare the values at `y`. Use `conv_rhs => rw [← Quotient.out_eq y]`. Both sides reduce to the same expression.

Rewrite `ih` using `[e hh]`. Rewrite `iD`, the goal using `[e hD]`. Use `haveI : IsFiniteMeasure (muQ E r) := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)`. Use `haveI : SigmaFinite (muQ E r) := IsFiniteMeasure.toSigmaFinite _`. Use `haveI : SFinite (muQ E r) := instSFiniteOfSigmaFinite`.

Use `flow_abs (muQ E r) (fun u => rightMul (rationalGLOne E r) ⟨c u, c1 u⟩) ?_ (fun u => measurePreserving_rightMul (Γ := rationalGLOne E r) (mu1 E r) _) (fun u => (rightMulHomeomorph (rationalGLOne E r) _).measurableEmbedding) _ _ ?_ ih iD fun y u => ?_` and prove the remaining obligations. Conclude with `flow_cont (rationalGLOne E r) (fun u => ⟨c u, c1 u⟩) (cc.subtype_mk c1)`. Conclude with `(isOpenQuotientMap_mk (rationalGLOne E r)).isQuotientMap.continuous_iff.2 (cD.comp continuous_subtype_val)`. Take `⟨g, rfl⟩` from `mk_surjective (rationalGLOne E r) y`. Establish `h1` using `(hd (g * c u)).scomp_of_eq u ((hasDerivAt_id u).sub_const u) (by simp)`.

Rewrite `h1` using `[one_smul]`. Use `h1.congr_of_eventuallyEq (.of_forall fun s => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `h (g * c s) = h (g * c u * c (s - u))`. Rewrite using `[mul_assoc, ← cadd, add_sub_cancel]`.
-/
theorem UpperTheory.integral_quotient_derivative_oneParameter_eq_zero :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (h D : GA E r → ℂ) (c : ℝ → GA E r),
          AutomorphicForm.IsLeftInvariant h → AutomorphicForm.IsLeftInvariant D → Continuous D → Continuous c → c 0 = 1 →
          (∀ s t, c (s + t) = c s * c t) → (∀ s, c s ∈ normOneGL E r) → (∀ g, HasDerivAt (fun s => h (g * c s)) (D g) 0) →
          Integrable (onQ h) (muQ E r) → Integrable (onQ D) (muQ E r) → ∫ y, onQ D y ∂muQ E r = 0 := by
  intro E _ _ r h D c hh hD cD cc _ cadd c1 hd ih iD
  have e : ∀ {f : GA E r → ℂ} (hf : AutomorphicForm.IsLeftInvariant f), onQ f = CuspidalSpectrum.cuspQuot hf := fun hf => by
    funext y
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  rw [e hh] at ih
  rw [e hD] at iD ⊢
  haveI : IsFiniteMeasure (muQ E r) := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
  haveI : SigmaFinite (muQ E r) := IsFiniteMeasure.toSigmaFinite _
  haveI : SFinite (muQ E r) := instSFiniteOfSigmaFinite
  refine flow_abs (muQ E r) (fun u => rightMul (rationalGLOne E r) ⟨c u, c1 u⟩) ?_
    (fun u => measurePreserving_rightMul (Γ := rationalGLOne E r) (mu1 E r) _)
    (fun u => (rightMulHomeomorph (rationalGLOne E r) _).measurableEmbedding) _ _ ?_ ih iD fun y u => ?_
  · exact flow_cont (rationalGLOne E r) (fun u => ⟨c u, c1 u⟩) (cc.subtype_mk c1)
  · exact (isOpenQuotientMap_mk (rationalGLOne E r)).isQuotientMap.continuous_iff.2 (cD.comp continuous_subtype_val)
  · obtain ⟨g, rfl⟩ := mk_surjective (rationalGLOne E r) y
    have h1 := (hd (g * c u)).scomp_of_eq u ((hasDerivAt_id u).sub_const u) (by simp)
    rw [one_smul] at h1
    refine h1.congr_of_eventuallyEq (.of_forall fun s => ?_)
    change h (g * c s) = h (g * c u * c (s - u))
    rw [mul_assoc, ← cadd, add_sub_cancel]
