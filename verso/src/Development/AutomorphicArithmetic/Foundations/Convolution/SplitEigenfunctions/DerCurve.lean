import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UILaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.IILaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc UpperTheory.ConvolutionTheory.R2.Ff
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hb : Bd (fun _ : GL (Fin 2) (A E) => (1 : ℂ))` using `⟨continuous_const, fun _ _ => rfl, fun _ _ => ⟨1, fun _ _ _ => by simp⟩⟩`. Establish `h` using `(meanLaws E N _ hb).1 1`. Establish `h' : IntegrableOn (fun _ : G1 E => (1 : ℂ)) N.D N.μ` using `h`. Conclude with `(integrableOn_const_iff (by simp)).1 h' |>.resolve_left (by simp)`.
-/
private theorem vol_lt (N : MeasE E) : N.μ N.D < ⊤ := by
  have hb : Bd (fun _ : GL (Fin 2) (A E) => (1 : ℂ)) :=
    ⟨continuous_const, fun _ _ => rfl, fun _ _ => ⟨1, fun _ _ _ => by simp⟩⟩
  have h := (meanLaws E N _ hb).1 1
  have h' : IntegrableOn (fun _ : G1 E => (1 : ℂ)) N.D N.μ := h
  exact (integrableOn_const_iff (by simp)).1 h' |>.resolve_left (by simp)

/- English proof (translation)
Take `⟨B, hB⟩` from `hQ.bdd ((fun u => y * g u) '' Metric.closedBall s 1) ((isCompact_closedBall s 1).image (continuous_const.mul hg))`. Use `haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using vol_lt N⟩`. Establish `hm : ∀ {P : GL (Fin 2) (A E) → ℂ}, Continuous P → ∀ k, AEStronglyMeasurable (fun h : G1 E => P (gl h * k)) (N.μ.restrict N.D)` using `fun hP k => (hP.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)).aestronglyMeasurable`. Use `(hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := N.μ.restrict N.D) (F := fun u h => Ψ (gl h * (y * g u))) (F' := fun u h => Q (gl h * (y * g u))) (x₀ := s) (s := Metric.ball s 1) (bound := fun _ => B) (Metric.ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2` and prove the remaining obligations. Conclude with `Eventually.of_forall fun u => hm hΨ.cont _`.

Conclude with `(meanLaws E N Ψ hΨ).1 _`. Conclude with `hm hQ.cont _`. Conclude with `ae_of_all _ fun h u hu => hB h _ ⟨u, Metric.ball_subset_closedBall hu, rfl⟩`. Conclude with `integrable_const _`. Use `ae_of_all _ fun h u _ => ?_` and prove the remaining obligations.

Use `hd (gl h * y) u` as an intermediate fact. Simplify `this` using `only [mul_assoc]`.
-/
private theorem inner_der (N : MeasE E) {Ψ Q : GL (Fin 2) (A E) → ℂ} (hΨ : Bd Ψ) (hQ : Bd Q)
    {g : ℝ → GL (Fin 2) (A E)} (hg : Continuous g)
    (hd : ∀ y s, HasDerivAt (fun u => Ψ (y * g u)) (Q (y * g s)) s) (y : GL (Fin 2) (A E)) (s : ℝ) :
    HasDerivAt (fun u => mean N fun x => Ψ (x * (y * g u))) (mean N fun x => Q (x * (y * g s))) s := by
  obtain ⟨B, hB⟩ := hQ.bdd ((fun u => y * g u) '' Metric.closedBall s 1)
    ((isCompact_closedBall s 1).image (continuous_const.mul hg))
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using vol_lt N⟩
  have hm : ∀ {P : GL (Fin 2) (A E) → ℂ}, Continuous P → ∀ k,
      AEStronglyMeasurable (fun h : G1 E => P (gl h * k)) (N.μ.restrict N.D) := fun hP k =>
    (hP.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := N.μ.restrict N.D)
    (F := fun u h => Ψ (gl h * (y * g u))) (F' := fun u h => Q (gl h * (y * g u)))
    (x₀ := s) (s := Metric.ball s 1) (bound := fun _ => B)
    (Metric.ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun u => hm hΨ.cont _
  · exact (meanLaws E N Ψ hΨ).1 _
  · exact hm hQ.cont _
  · exact ae_of_all _ fun h u hu => hB h _ ⟨u, Metric.ball_subset_closedBall hu, rfl⟩
  · exact integrable_const _
  · refine ae_of_all _ fun h u _ => ?_
    have := hd (gl h * y) u
    simpa only [mul_assoc] using this

/- English proof (translation)
Use `set Mp : GL (Fin 2) (A E) → ℂ := fun y => mean N fun x => Ψ (x * y) with hMp`. Use `set Mq : GL (Fin 2) (A E) → ℂ := fun y => mean N fun x => Q (x * y) with hMq`. Establish `cp : Continuous Mp` using `(meanLaws E N Ψ hΨ).2.1`. Establish `cq : Continuous Mq` using `(meanLaws E N Q hQ).2.1`. Establish `ip : ∀ γ y, Mp (ratGL E 2 γ * y) = Mp y` using `(meanLaws E N Ψ hΨ).2.2.2`.

Establish `iq : ∀ γ y, Mq (ratGL E 2 γ * y) = Mq y` using `(meanLaws E N Q hQ).2.2.2`. Establish `inv : ∀ (M : GL (Fin 2) (A E) → ℂ), (∀ γ y, M (ratGL E 2 γ * y) = M y) → ∀ k (e : Eˣ) t, M (aE (IdeleGroup.diagonal E e * t) * k) = M (aE t * k)`. Introduce `M hM k e t`. Take `⟨γ, hγ⟩` from `exists_ratGL_aE (F := E) e`. Rewrite using `[aE_mul, ← hγ, mul_assoc, hM]`.

Establish `hK : IsCompact (Metric.closedBall (0 : ℝ) 1)` using `isCompact_closedBall 0 1`. Use `set b : (A E)ˣ → ℝ := fun t => sSup ((fun s => ‖Mq (aE t * g s)‖) '' Metric.closedBall (0 : ℝ) 1) with hb`. Establish `cb : Continuous b` using `IsCompact.continuous_sSup (f := fun t s => ‖Mq (aE t * g s)‖) hK (cq.comp ((continuous_aE.comp continuous_fst).mul (hg.comp continuous_snd))).norm`. Establish `ib : ∀ (e : Eˣ) t, b (IdeleGroup.diagonal E e * t) = b t` using `fun e t => by`. Simplify using `only [hb, inv Mq iq]`.

Take `⟨-, ⟨B, hB⟩, -⟩` from `uiLaws E (fun t => (b t : ℂ)) (Complex.continuous_ofReal.comp cb) (fun e t => by simp only [ib])`. Establish `hbd : ∀ z : IdeleGroup.normOneSubgroup E, ∀ s ∈ Metric.closedBall (0 : ℝ) 1, ‖Mq (aE (z : IdeleGroup E) * g s)‖ ≤ B`. Introduce `z s hs`. Establish `hab : ab (z : IdeleGroup E) = 1` using `congrArg Subtype.val (MonoidHom.mem_ker.1 z.2)`. Establish `h1 : ‖Mq (aE (z : IdeleGroup E) * g s)‖ ≤ b z` using `le_csSup (hK.image (cq.comp (continuous_const.mul hg)).norm).bddAbove ⟨s, hs, rfl⟩`.

Combine the equalities or inequalities in the displayed calculation. Use `haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) := ⟨by simpa using normOneMeasure_normOneFundamentalDomain_lt_top E⟩`. Establish `hint : ∀ (M : GL (Fin 2) (A E) → ℂ), Continuous M → (∀ γ y, M (ratGL E 2 γ * y) = M y) → ∀ k, IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => M (aE (z : IdeleGroup E) * k)) (normOneFundamentalDomain E) (normOneMeasure E)` using `fun M cM iM k => (uiLaws E (fun t => M (aE t * k)) (cM.comp (continuous_aE.mul continuous_const)) (inv M iM k)).1`. Establish `e1 : ∀ s, (II N fun x => Ψ (x * g s)) = ∫ z in normOneFundamentalDomain E, Mp (aE (z : IdeleGroup E) * g s) ∂normOneMeasure E`. Introduce `s`.

Simplify using `only [II, UI, hMp, mul_assoc]`. Establish `e2 : II N Q = ∫ z in normOneFundamentalDomain E, Mq (aE (z : IdeleGroup E) * g 0) ∂normOneMeasure E`. Simplify using `only [II, UI, hMq, g0, mul_one]`. Simplify using `only [e1]`. Rewrite using `[e2]`.

Use `(hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := (normOneMeasure E).restrict (normOneFundamentalDomain E)) (F := fun s z => Mp (aE (z : IdeleGroup E) * g s)) (F' := fun s z => Mq (aE (z : IdeleGroup E) * g s)) (x₀ := 0) (s := Metric.ball (0 : ℝ) 1) (bound := fun _ …` and prove the remaining obligations. Conclude with `Eventually.of_forall fun s => (hint Mp cp ip (g s)).aestronglyMeasurable`. Conclude with `hint Mp cp ip (g 0)`. Conclude with `(hint Mq cq iq (g 0)).aestronglyMeasurable`. Conclude with `ae_of_all _ fun z s hs => hbd z s (Metric.ball_subset_closedBall hs)`.

Conclude with `integrable_const _`. Conclude with `ae_of_all _ fun z s _ => inner_der N hΨ hQ hg hd _ s`.
-/
private theorem outer_der (N : MeasE E) {Ψ Q : GL (Fin 2) (A E) → ℂ} (hΨ : Bd Ψ) (hQ : Bd Q)
    {g : ℝ → GL (Fin 2) (A E)} (hg : Continuous g) (g0 : g 0 = 1)
    (hd : ∀ y s, HasDerivAt (fun u => Ψ (y * g u)) (Q (y * g s)) s) :
    HasDerivAt (fun s => II N fun x => Ψ (x * g s)) (II N Q) 0 := by
  set Mp : GL (Fin 2) (A E) → ℂ := fun y => mean N fun x => Ψ (x * y) with hMp
  set Mq : GL (Fin 2) (A E) → ℂ := fun y => mean N fun x => Q (x * y) with hMq
  have cp : Continuous Mp := (meanLaws E N Ψ hΨ).2.1
  have cq : Continuous Mq := (meanLaws E N Q hQ).2.1
  have ip : ∀ γ y, Mp (ratGL E 2 γ * y) = Mp y := (meanLaws E N Ψ hΨ).2.2.2
  have iq : ∀ γ y, Mq (ratGL E 2 γ * y) = Mq y := (meanLaws E N Q hQ).2.2.2
  have inv : ∀ (M : GL (Fin 2) (A E) → ℂ), (∀ γ y, M (ratGL E 2 γ * y) = M y) → ∀ k (e : Eˣ) t,
      M (aE (IdeleGroup.diagonal E e * t) * k) = M (aE t * k) := by
    intro M hM k e t
    obtain ⟨γ, hγ⟩ := exists_ratGL_aE (F := E) e
    rw [aE_mul, ← hγ, mul_assoc, hM]
  have hK : IsCompact (Metric.closedBall (0 : ℝ) 1) := isCompact_closedBall 0 1
  set b : (A E)ˣ → ℝ := fun t => sSup ((fun s => ‖Mq (aE t * g s)‖) '' Metric.closedBall (0 : ℝ) 1) with hb
  have cb : Continuous b := IsCompact.continuous_sSup (f := fun t s => ‖Mq (aE t * g s)‖) hK
    (cq.comp ((continuous_aE.comp continuous_fst).mul (hg.comp continuous_snd))).norm
  have ib : ∀ (e : Eˣ) t, b (IdeleGroup.diagonal E e * t) = b t := fun e t => by
    simp only [hb, inv Mq iq]
  obtain ⟨-, ⟨B, hB⟩, -⟩ := uiLaws E (fun t => (b t : ℂ)) (Complex.continuous_ofReal.comp cb)
    (fun e t => by simp only [ib])
  have hbd : ∀ z : IdeleGroup.normOneSubgroup E, ∀ s ∈ Metric.closedBall (0 : ℝ) 1,
      ‖Mq (aE (z : IdeleGroup E) * g s)‖ ≤ B := by
    intro z s hs
    have hab : ab (z : IdeleGroup E) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 z.2)
    have h1 : ‖Mq (aE (z : IdeleGroup E) * g s)‖ ≤ b z :=
      le_csSup (hK.image (cq.comp (continuous_const.mul hg)).norm).bddAbove ⟨s, hs, rfl⟩
    calc _ ≤ b z := h1
      _ ≤ ‖(b z : ℂ)‖ := by rw [Complex.norm_real]; exact le_abs_self _
      _ ≤ B := hB _ hab
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by simpa using normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  have hint : ∀ (M : GL (Fin 2) (A E) → ℂ), Continuous M → (∀ γ y, M (ratGL E 2 γ * y) = M y) → ∀ k,
      IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => M (aE (z : IdeleGroup E) * k))
        (normOneFundamentalDomain E) (normOneMeasure E) := fun M cM iM k =>
    (uiLaws E (fun t => M (aE t * k)) (cM.comp (continuous_aE.mul continuous_const)) (inv M iM k)).1
  have e1 : ∀ s, (II N fun x => Ψ (x * g s)) =
      ∫ z in normOneFundamentalDomain E, Mp (aE (z : IdeleGroup E) * g s) ∂normOneMeasure E := by
    intro s
    simp only [II, UI, hMp, mul_assoc]
  have e2 : II N Q = ∫ z in normOneFundamentalDomain E, Mq (aE (z : IdeleGroup E) * g 0) ∂normOneMeasure E := by
    simp only [II, UI, hMq, g0, mul_one]
  simp only [e1]
  rw [e2]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (μ := (normOneMeasure E).restrict (normOneFundamentalDomain E))
    (F := fun s z => Mp (aE (z : IdeleGroup E) * g s)) (F' := fun s z => Mq (aE (z : IdeleGroup E) * g s))
    (x₀ := 0) (s := Metric.ball (0 : ℝ) 1) (bound := fun _ => B)
    (Metric.ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s => (hint Mp cp ip (g s)).aestronglyMeasurable
  · exact hint Mp cp ip (g 0)
  · exact (hint Mq cq iq (g 0)).aestronglyMeasurable
  · exact ae_of_all _ fun z s hs => hbd z s (Metric.ball_subset_closedBall hs)
  · exact integrable_const _
  · exact ae_of_all _ fun z s _ => inner_der N hΨ hQ hg hd _ s

variable [IsTotallyComplex E]

/- English proof (translation)
Establish `h` using `(exPar E X).1 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `left_eq_mul.1 h`.
-/
private theorem ex_zero' (X : Lie E 2) : ex X 0 = 1 := by
  have h := (exPar E X).1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

/- English proof (translation)
Establish `h1` using `GlobalTheory.CuspRep.hasDerivAt_curve Φ (y * infGL E 2 (ex X s)) (ex X) X (ex_zero' X) (exPar E X).2.2.1`. Establish `h2 : HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X s) * infGL E 2 (ex X (u - s)))) ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s))) s` using `HasDerivAt.comp_sub_const s s (by simpa using h1)`. Use `h2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `show Φ.1 (y * infGL E 2 (ex X u)) = Φ.1 (y * infGL E 2 (ex X s) * infGL E 2 (ex X (u - s)))`. Rewrite using `[mul_assoc, ← map_mul, ← (exPar E X).1, add_sub_cancel]`.
-/
private theorem der_curve (Φ : Sm E 2) (X : Lie E 2) (y : GL (Fin 2) (A E)) (s : ℝ) :
    HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X u))) ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s))) s := by
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve Φ (y * infGL E 2 (ex X s)) (ex X) X (ex_zero' X) (exPar E X).2.2.1
  have h2 : HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X s) * infGL E 2 (ex X (u - s))))
      ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s))) s :=
    HasDerivAt.comp_sub_const s s (by simpa using h1)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
  show Φ.1 (y * infGL E 2 (ex X u)) = Φ.1 (y * infGL E 2 (ex X s) * infGL E 2 (ex X (u - s)))
  rw [mul_assoc, ← map_mul, ← (exPar E X).1, add_sub_cancel]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Introduce `E _ _ _ N Φ φ X h0 hP h1 h2`. Establish `hg : Continuous fun s => infGL E 2 (ex X s)` using `(GlobalTheory.CompanionTheory.LieSkew.continuous_infGL_map E 2).comp (exPar E X).2.1`. Establish `g0 : infGL E 2 (ex X 0) = 1` using `by rw [ex_zero', map_one]`. Establish `hQ : Bd fun x => (act (.lie X) Φ).1 x * φ.1 x + (1 : ℂ) * (Φ.1 x * (act (.lie X) φ).1 x)`. Use `⟨h1.cont.add (continuous_const.mul h2.cont), fun γ g => ?_, fun C hC => ?_⟩` and prove the remaining obligations.

Conclude with `congrArg₂ (fun p q => p + (1 : ℂ) * q) (h1.left γ g) (h2.left γ g)`. Take `⟨B₁, hB₁⟩` from `h1.bdd C hC`. Take `⟨B₂, hB₂⟩` from `h2.bdd C hC`. Use `⟨B₁ + B₂, fun h k hk => ?_⟩` and prove the remaining obligations. Establish `a` using `hB₁ h k hk`.

Establish `b` using `hB₂ h k hk`. Rewrite using `[one_mul]`. Conclude with `(norm_add_le _ _).trans (add_le_add a b)`. Establish `hd : ∀ y s, HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X u)) * φ.1 (y * infGL E 2 (ex X u))) ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s)) * φ.1 (y * infGL E 2 (ex X s)) + (1 : ℂ) * (Φ.1 (y * infGL E 2 (ex X s)) * (act (.lie X) φ).1 (y * infGL E 2 (ex X s)))) s`. Introduce `y s`.

Rewrite using `[one_mul]`. Conclude with `(der_curve Φ X y s).mul (der_curve φ X y s)`. Establish `hD` using `outer_der N h0 hQ hg g0 hd`. Establish `hc : (fun s => II N fun x => Φ.1 (x * infGL E 2 (ex X s)) * φ.1 (x * infGL E 2 (ex X s))) = fun _ => II N fun x => Φ.1 x * φ.1 x`. Use function extensionality and compare the values at `fun s => (iiLaws E N _ h0).2 hP (infGL E 2 (ex X s))`.

Rewrite `hD` using `[hc]`. Establish `hz` using `hD.unique (hasDerivAt_const (0 : ℝ) _)`. Rewrite `hz` using `[(iiLaws E N _ h1).1 _ h2 1, one_mul]`. Conclude with `hz`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.iiLie :
    IILie := by
  intro E _ _ _ N Φ φ X h0 hP h1 h2
  have hg : Continuous fun s => infGL E 2 (ex X s) :=
    (GlobalTheory.CompanionTheory.LieSkew.continuous_infGL_map E 2).comp (exPar E X).2.1
  have g0 : infGL E 2 (ex X 0) = 1 := by rw [ex_zero', map_one]
  have hQ : Bd fun x => (act (.lie X) Φ).1 x * φ.1 x + (1 : ℂ) * (Φ.1 x * (act (.lie X) φ).1 x) := by
    refine ⟨h1.cont.add (continuous_const.mul h2.cont), fun γ g => ?_, fun C hC => ?_⟩
    · exact congrArg₂ (fun p q => p + (1 : ℂ) * q) (h1.left γ g) (h2.left γ g)
    · obtain ⟨B₁, hB₁⟩ := h1.bdd C hC
      obtain ⟨B₂, hB₂⟩ := h2.bdd C hC
      refine ⟨B₁ + B₂, fun h k hk => ?_⟩
      have a := hB₁ h k hk
      have b := hB₂ h k hk
      rw [one_mul]
      exact (norm_add_le _ _).trans (add_le_add a b)
  have hd : ∀ y s, HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X u)) * φ.1 (y * infGL E 2 (ex X u)))
      ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s)) * φ.1 (y * infGL E 2 (ex X s)) +
        (1 : ℂ) * (Φ.1 (y * infGL E 2 (ex X s)) * (act (.lie X) φ).1 (y * infGL E 2 (ex X s)))) s := by
    intro y s
    rw [one_mul]
    exact (der_curve Φ X y s).mul (der_curve φ X y s)
  have hD := outer_der N h0 hQ hg g0 hd
  have hc : (fun s => II N fun x => Φ.1 (x * infGL E 2 (ex X s)) * φ.1 (x * infGL E 2 (ex X s))) =
      fun _ => II N fun x => Φ.1 x * φ.1 x :=
    funext fun s => (iiLaws E N _ h0).2 hP (infGL E 2 (ex X s))
  rw [hc] at hD
  have hz := hD.unique (hasDerivAt_const (0 : ℝ) _)
  rw [(iiLaws E N _ h1).1 _ h2 1, one_mul] at hz
  exact hz
