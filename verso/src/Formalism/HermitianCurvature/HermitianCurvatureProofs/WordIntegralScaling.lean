import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordIntegralScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons i l ih`. Establish `hi : Integrable (φ i) μ` using `h i (by simp)`. Take `⟨hl1, hl2⟩` from `ih (fun j hj => h j (by simp [hj]))`.

Establish `hLi : Integrable (fun p => L i (φ i p)) μ` using `(L i).integrable_comp hi`. Simplify using `only [List.map_cons, List.sum_cons]`. Use `⟨hLi.add hl1, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_add hLi hl1, hl2, ContinuousLinearMap.integral_comp_comm _ hi]`.
-/
theorem int_list {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (L : ι → E →L[ℂ] E) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    Integrable (fun p => (l.map fun i => L i (φ i p)).sum) μ ∧
      ∫ p, (l.map fun i => L i (φ i p)).sum ∂μ = (l.map fun i => L i (∫ p, φ i p ∂μ)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : Integrable (φ i) μ := h i (by simp)
    obtain ⟨hl1, hl2⟩ := ih (fun j hj => h j (by simp [hj]))
    have hLi : Integrable (fun p => L i (φ i p)) μ := (L i).integrable_comp hi
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hLi.add hl1, ?_⟩
    rw [integral_add hLi hl1, hl2, ContinuousLinearMap.integral_comp_comm _ hi]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons i l ih`. Rewrite using `[List.map_cons, List.sum_cons, smul_add, ih, List.map_cons, List.sum_cons, map_smul]`.
-/
theorem smul_list {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (l : List ι) (L : ι → E →L[ℂ] E)
    (x : ι → E) : c • (l.map fun i => L i (x i)).sum = (l.map fun i => L i (c • x i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, smul_add, ih, List.map_cons, List.sum_cons, map_smul]

variable {k r : ℕ}

/- English proof (translation)
Simplify using `[B4.lr, B4.nrm, List.map_map, Function.comp_def]`.
-/
theorem lr_nrm (v : List (Mat k r)) :
    (B4.lr [] v).map B4.nrm = B4.lr [] (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) := by
  simp [B4.lr, B4.nrm, List.map_map, Function.comp_def]

/- English proof (translation)
Establish `h` using `B4.W_nrm (B4.lr [] v) f`. Rewrite `h` using `[lr_nrm, ← B4.dLR_eq, ← B4.dLR_eq]`. Conclude with `h`.
-/
theorem rw_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (Mat k r)) (f : Mat k r → E) :
    Rw v f = B4.pn (B4.lr [] v) • Rw (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) f := by
  have h := B4.W_nrm (B4.lr [] v) f
  rw [lr_nrm, ← B4.dLR_eq, ← B4.dLR_eq] at h
  exact h

end Formalism.FourierDecayAlt.P.WordIntegralScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `hW hR k r Wp Wq _ _ _ _ _ _ D A m F Θ ho hT hF hC g hg`. Establish `hCk : CkOn (m : ℕ∞) (GV k r) F` using `hF.choose_spec.1`. Establish `hgG : g ∈ GV k r` using `hg.1`. Establish `key : ∀ T ∈ Θ, Integrable (fun p => xiP D p • Rw T.word (rho D p F) g) D.μSS ∧ Rw T.word (JF D F) g = ∫ p, xiP D p • Rw T.word (rho D p F) g ∂D.μSS`. Introduce `T hT'`.

Establish `hvl : T.word.length ≤ m` using `(B5.len_le_order Θ hT').trans ho`. Use `set v' := T.word.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X with hv'`. Establish `hv'u : ∀ X ∈ v', unitLie k r X`. Introduce `X hX`. Take `⟨Y, hY, rfl⟩` from `List.mem_map.1 hX`.

Conclude with `B4.nrm_unit (x := (false, Y)) (T.word_lie Y hY)`. Establish `hv'l : v'.length ≤ m` using `by rw [hv', List.length_map]; exact hvl`. Take `⟨hI, hE⟩` from `(hW k r Wp Wq D A m F hT hF).2 [] v' (by simp) hv'u (by simpa using hv'l) g hg`. Simplify using `only [List.map_nil] at hI hE`. Establish `hae : (fun p => xiP D p • rho D p (dLR [] (v'.map (AdR p)) F) g) =ᵐ[D.μSS] fun p => xiP D p • Rw v' (rho D p F) g` using `by filter_upwards [B5.ae_inSS D] with p hp`.

Use `hR k r Wp Wq D m F p hp hCk [] v' (by simp) (fun X hX => (hv'u X hX).1) (by simpa using hv'l) g hgG` as an intermediate fact. Simplify using `only [List.map_nil] at this`. Rewrite using `[← this]`. Both sides reduce to the same expression. Establish `hI' : Integrable (fun p => xiP D p • Rw v' (rho D p F) g) D.μSS` using `hI.congr hae`.

Establish `hfun : (fun p => xiP D p • Rw T.word (rho D p F) g) = fun p => (B4.pn (B4.lr [] T.word) : ℝ) • (xiP D p • Rw v' (rho D p F) g)`. Use function extensionality and compare the values at `p`. Rewrite using `[WordIntegralScaling.rw_scale T.word (rho D p F), Pi.smul_apply, smul_comm]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfun]`.

Conclude with `hI'.smul (B4.pn (B4.lr [] T.word))`. Rewrite using `[WordIntegralScaling.rw_scale T.word (JF D F), Pi.smul_apply, hfun, integral_smul]`. Use `congr 1`. Rewrite using `[← integral_congr_ae hae]`. Conclude with `hE`.

Establish `hCo : CkOn (opOrder Θ : ℕ∞) (GV k r) F` using `B5.ckOn_mono (by exact_mod_cast ho) hCk`. Establish `hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS` using `by show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [B5.ae_inSS D] with p hp`. Rewrite using `[hC p hp F hCo g hg]`.

Rewrite using `[hRHS]`. Unfold `opApply`. Simplify using `only [WordIntegralScaling.smul_list]`. Take `⟨_, hsum⟩` from `WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g) (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1`. Rewrite using `[hsum]`.

Use `congr 1`. Use `List.map_congr_left fun T hT' => ?_` and prove the remaining obligations. Rewrite using `[(key T hT').2]`.
-/
theorem theta_bessel_commute_of_parts : Formalism.FourierDecayAlt.JF.JThetaOfParts := by
  intro hW hR k r Wp Wq _ _ _ _ _ _ D A m F Θ ho hT hF hC g hg
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hgG : g ∈ GV k r := hg.1
  have key : ∀ T ∈ Θ, Integrable (fun p => xiP D p • Rw T.word (rho D p F) g) D.μSS ∧
      Rw T.word (JF D F) g = ∫ p, xiP D p • Rw T.word (rho D p F) g ∂D.μSS := by
    intro T hT'
    have hvl : T.word.length ≤ m := (B5.len_le_order Θ hT').trans ho
    set v' := T.word.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X with hv'
    have hv'u : ∀ X ∈ v', unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact B4.nrm_unit (x := (false, Y)) (T.word_lie Y hY)
    have hv'l : v'.length ≤ m := by rw [hv', List.length_map]; exact hvl
    obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] v' (by simp) hv'u (by simpa using hv'l) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP D p • rho D p (dLR [] (v'.map (AdR p)) F) g) =ᵐ[D.μSS]
        fun p => xiP D p • Rw v' (rho D p F) g := by
      filter_upwards [B5.ae_inSS D] with p hp
      have := hR k r Wp Wq D m F p hp hCk [] v' (by simp) (fun X hX => (hv'u X hX).1) (by simpa using hv'l) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    have hI' : Integrable (fun p => xiP D p • Rw v' (rho D p F) g) D.μSS := hI.congr hae
    have hfun : (fun p => xiP D p • Rw T.word (rho D p F) g) =
        fun p => (B4.pn (B4.lr [] T.word) : ℝ) • (xiP D p • Rw v' (rho D p F) g) := by
      funext p
      rw [WordIntegralScaling.rw_scale T.word (rho D p F), Pi.smul_apply, smul_comm]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact hI'.smul (B4.pn (B4.lr [] T.word))
    · rw [WordIntegralScaling.rw_scale T.word (JF D F), Pi.smul_apply, hfun, integral_smul]
      congr 1
      rw [← integral_congr_ae hae]
      exact hE
  have hCo : CkOn (opOrder Θ : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast ho) hCk
  have hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS := by
    show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hC p hp F hCo g hg]
  rw [hRHS]
  unfold opApply
  simp only [WordIntegralScaling.smul_list]
  obtain ⟨_, hsum⟩ := WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g)
    (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1
  rw [hsum]
  congr 1
  refine List.map_congr_left fun T hT' => ?_
  rw [(key T hT').2]

end Formalism.FourierDecayAlt.P
