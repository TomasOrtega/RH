import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.StepFin
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.SphAct
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.PolyMem
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Unfold `cf`. Rewrite using `[map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]`.
-/
private theorem hf_cf_self (w : Pl K) (y : GL (Fin n) (w.adicCompletion K)) (x : AdelicGLn.FiniteAdelicGL K n) :
    cf w (AdelicGLn.localEmbedding w y * x) = y * cf w x := by
  unfold cf
  rw [map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]

/- English proof (translation)
Unfold `cf`. Rewrite using `[map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.1 v hv, one_mul]`.
-/
private theorem hf_cf_ne {w v : Pl K} (hv : v ≠ w) (y : GL (Fin n) (w.adicCompletion K))
    (x : AdelicGLn.FiniteAdelicGL K n) : cf v (AdelicGLn.localEmbedding w y * x) = cf v x := by
  unfold cf
  rw [map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.1 v hv, one_mul]

/- English proof (translation)
The claim follows from `(continuous_finAt w).comp continuous_finEmb`.
-/
private theorem hf_cont (w : Pl K) : Continuous (cf (n := n) w) :=
  (continuous_finAt w).comp continuous_finEmb

/- English proof (translation)
Establish `hl` using `(UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1`. Establish `key : ∀ x, r x = e₀ (AdelicGLn.localEmbedding w (cf w x)⁻¹ * x)`. Introduce `x`. Rewrite using `[h₀, hf_cf_self, inv_mul_cancel, hr, Set.indicator_of_mem (by exact one_mem _)]`. Simplify using the standard rewrite rules.

Establish `hrc : Continuous r`. Rewrite using `[funext key]`. Conclude with `(map_continuous e₀).comp ((hl.comp (hf_cont w).inv).mul continuous_id)`. Establish `h1 : Continuous fun x => r x * h (cf w x)` using `hrc.mul (hc.comp (hf_cont w))`. Establish `h2 : HasCompactSupport fun x => r x * h (cf w x)`.

Establish `hK : IsCompact ((fun q : GL (Fin n) (w.adicCompletion K) × AdelicGLn.FiniteAdelicGL K n => AdelicGLn.localEmbedding w q.1 * q.2) '' (tsupport h ×ˢ tsupport e₀))` using `(hs.isCompact.prod e₀.hasCompactSupport.isCompact).image ((hl.comp continuous_fst).mul continuous_snd)`. Use `HasCompactSupport.intro hK fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Apply `hx` to reduce the goal to its premises. Use `⟨(cf w x, AdelicGLn.localEmbedding w (cf w x)⁻¹ * x), ⟨subset_tsupport _ (right_ne_zero_of_mul hne), subset_tsupport _ ?_⟩, ?_⟩` and prove the remaining obligations.

Use `left_ne_zero_of_mul hne` as an intermediate fact. Rewrite `this` using `[key]`. Then use the resulting hypothesis. Simplify using `only [map_inv, mul_inv_cancel_left]`. Conclude with `⟨⟨⟨_, h1⟩, h2⟩, fun _ => rfl⟩`.
-/
private theorem hf_ex (w : Pl K) (h : GL (Fin n) (w.adicCompletion K) → ℂ) (hc : Continuous h) (hs : HasCompactSupport h)
    (r : AdelicGLn.FiniteAdelicGL K n → ℂ) (hr : Free w r) (e₀ : TF K n)
    (h₀ : ∀ x, e₀ x = r x * (GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1 (cf w x)) :
    ∃ e : TF K n, ∀ x, e x = r x * h (cf w x) := by
  have hl := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
  have key : ∀ x, r x = e₀ (AdelicGLn.localEmbedding w (cf w x)⁻¹ * x) := by
    intro x
    rw [h₀, hf_cf_self, inv_mul_cancel, hr, Set.indicator_of_mem (by exact one_mem _)]
    simp
  have hrc : Continuous r := by
    rw [funext key]
    exact (map_continuous e₀).comp ((hl.comp (hf_cont w).inv).mul continuous_id)
  have h1 : Continuous fun x => r x * h (cf w x) := hrc.mul (hc.comp (hf_cont w))
  have h2 : HasCompactSupport fun x => r x * h (cf w x) := by
    have hK : IsCompact ((fun q : GL (Fin n) (w.adicCompletion K) × AdelicGLn.FiniteAdelicGL K n =>
        AdelicGLn.localEmbedding w q.1 * q.2) '' (tsupport h ×ˢ tsupport e₀)) :=
      (hs.isCompact.prod e₀.hasCompactSupport.isCompact).image ((hl.comp continuous_fst).mul continuous_snd)
    refine HasCompactSupport.intro hK fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨(cf w x, AdelicGLn.localEmbedding w (cf w x)⁻¹ * x), ⟨subset_tsupport _ (right_ne_zero_of_mul hne),
      subset_tsupport _ ?_⟩, ?_⟩
    · have := left_ne_zero_of_mul hne
      rwa [key] at this
    · simp only [map_inv, mul_inv_cancel_left]
  exact ⟨⟨⟨_, h1⟩, h2⟩, fun _ => rfl⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `K _ _ n hn μ _ m _ 𝔞 ev hev T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `_ p h _ r _ e₀ e₁ h₀ h₁`. Establish `: e₁ = e₀`.

Use extensionality with `x`. Rewrite using `[h₀, h₁, Finset.prod_empty, Finset.prod_empty]`. Rewrite using `[this, Finset.prod_empty, map_one, map_one]`. Both sides reduce to the same expression. Consider the case `insert w T hw ih`.

Introduce `hS p h hsph r hr e₀ e₁ h₀ h₁`. Establish `hwm : w ∈ insert w T` using `Finset.mem_insert_self w T`. Establish `hne : ∀ v ∈ T, v ≠ w` using `fun v hv hvw => hw (hvw ▸ hv)`. Take `⟨hlc, hcs, hinv⟩` from `(sphEx K n hn w).2.2 (p w) (h w) (hsph w hwm)`. Use `set r' : AdelicGLn.FiniteAdelicGL K n → ℂ := fun x => r x * ∏ v ∈ T, (GLnLocal.integralGL (v.adicCompletion K) n : Set _).indicator 1 (cf v x) with hr'`.

Establish `hfree : Free w r'`. Introduce `y x`. Simplify using `only [hr']`. Rewrite using `[hr w hwm y x]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun v hv => by rw [hf_cf_ne (hne v hv)]`. Establish `h₀' : ∀ x, e₀ x = r' x * (GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1 (cf w x)`. Introduce `x`. Rewrite using `[h₀, Finset.prod_insert hw]`. Simplify using `only [hr']`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨e, he⟩` from `hf_ex w (h w) hlc.continuous hcs r' hfree e₀ h₀'`. Take `⟨hfix, hstep⟩` from `stepFin K n hn μ m w (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isOpen_integralGL _ n) (h w) hcs (fun k hk x => (hinv k hk x).2) r' hfree e₀ e h₀' he`. Establish `hA : Ofin μ m e = ev (map C (atPl w (p w))) ∘L Ofin μ m e₀`. Rewrite using `[hstep]`.

Use `ContinuousLinearMap.ext fun u => ?_` and prove the remaining obligations. Conclude with `sphAct K n hn μ 𝔞 ev hev w (hS w hwm) (p w) (h w) (hsph w hwm) _ (hfix u)`. Establish `hB` using `ih (fun v hv => hS v (Finset.mem_insert_of_mem hv)) p h (fun v hv => hsph v (Finset.mem_insert_of_mem hv)) (fun x => r x * h w (cf w x)) (fun v hv y x => by show r _ * h w _ = r x * h w _`. Rewrite using `[hr v (Finset.mem_insert_of_mem hv) y x, hf_cf_ne (hne v hv).symm]) e e₁`. Use the proof step `(fun x => by`.

Rewrite using `[he]`. Simplify using `only [hr']`. Use the proof step `ring)`. Use the proof step `(fun x => by`. Rewrite using `[h₁, Finset.prod_insert hw]`.

Use the proof step `ring)`. Rewrite using `[hB, hA, Finset.prod_insert hw, mul_comm (atPl w (p w)), map_mul, map_mul]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.ConvolutionTheory.GM.heckeFin :
    HeckeFin := by
  intro K _ _ n hn μ _ m _ 𝔞 ev hev T
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _ p h _ r _ e₀ e₁ h₀ h₁
    have : e₁ = e₀ := by
      ext x
      rw [h₀, h₁, Finset.prod_empty, Finset.prod_empty]
    rw [this, Finset.prod_empty, map_one, map_one]
    rfl
  | insert w T hw ih =>
    intro hS p h hsph r hr e₀ e₁ h₀ h₁
    have hwm : w ∈ insert w T := Finset.mem_insert_self w T
    have hne : ∀ v ∈ T, v ≠ w := fun v hv hvw => hw (hvw ▸ hv)
    obtain ⟨hlc, hcs, hinv⟩ := (sphEx K n hn w).2.2 (p w) (h w) (hsph w hwm)
    set r' : AdelicGLn.FiniteAdelicGL K n → ℂ := fun x =>
      r x * ∏ v ∈ T, (GLnLocal.integralGL (v.adicCompletion K) n : Set _).indicator 1 (cf v x) with hr'
    have hfree : Free w r' := by
      intro y x
      simp only [hr']
      rw [hr w hwm y x]
      congr 1
      exact Finset.prod_congr rfl fun v hv => by rw [hf_cf_ne (hne v hv)]
    have h₀' : ∀ x, e₀ x = r' x * (GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1 (cf w x) := by
      intro x
      rw [h₀, Finset.prod_insert hw]
      simp only [hr']
      ring
    obtain ⟨e, he⟩ := hf_ex w (h w) hlc.continuous hcs r' hfree e₀ h₀'
    obtain ⟨hfix, hstep⟩ := stepFin K n hn μ m w (GLnLocal.integralGL (w.adicCompletion K) n)
      (GLnLocal.isOpen_integralGL _ n) (h w) hcs (fun k hk x => (hinv k hk x).2) r' hfree e₀ e h₀' he
    have hA : Ofin μ m e = ev (map C (atPl w (p w))) ∘L Ofin μ m e₀ := by
      rw [hstep]
      refine ContinuousLinearMap.ext fun u => ?_
      exact sphAct K n hn μ 𝔞 ev hev w (hS w hwm) (p w) (h w) (hsph w hwm) _ (hfix u)
    have hB := ih (fun v hv => hS v (Finset.mem_insert_of_mem hv)) p h
      (fun v hv => hsph v (Finset.mem_insert_of_mem hv)) (fun x => r x * h w (cf w x))
      (fun v hv y x => by
        show r _ * h w _ = r x * h w _
        rw [hr v (Finset.mem_insert_of_mem hv) y x, hf_cf_ne (hne v hv).symm]) e e₁
      (fun x => by
        rw [he]
        simp only [hr']
        ring)
      (fun x => by
        rw [h₁, Finset.prod_insert hw]
        ring)
    rw [hB, hA, Finset.prod_insert hw, mul_comm (atPl w (p w)), map_mul, map_mul]
    rfl
