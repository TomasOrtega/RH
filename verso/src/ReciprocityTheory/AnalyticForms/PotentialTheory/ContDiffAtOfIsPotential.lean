import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def HoloSmoothStatement : Prop :=
  ∀ {e e' : ℕ} (F : (Fin e → ℂ) → (Fin e' → ℂ)) (U : Set (Fin e → ℂ)), IsOpen U →
    AnalyticOnNhd ℂ F U → ContDiffOn ℝ ∞ F U

def SmoothOnAlgStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U V : Set X) (f g : X → ℝ)
    (c : ℝ), A.SmoothOn U f → A.SmoothOn V g → V ⊆ U →
      A.SmoothOn V (fun x => f x + g x) ∧ A.SmoothOn U (fun x => c * f x)

/- English proof (translation)
Introduce `e X _ A U V f g c hf hg hVU`. Use `⟨fun j => ?_, fun j => ?_⟩` and prove the remaining obligations. Conclude with `((hf j).mono fun y hy => ⟨hy.1, hVU hy.2⟩).add (hg j)`. Conclude with `contDiffOn_const.mul (hf j)`.
-/
theorem smoothOnAlg : SmoothOnAlgStatement := by
  intro e X _ A U V f g c hf hg hVU
  refine ⟨fun j => ?_, fun j => ?_⟩
  · exact ((hf j).mono fun y hy => ⟨hy.1, hVU hy.2⟩).add (hg j)
  · exact contDiffOn_const.mul (hf j)

section SlopeTestRemainingChoices

variable {e : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem add_U (P Q : LocPot X) (x : X) : (P + Q).U x = P.U x ∩ Q.U x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem add_φ (P Q : LocPot X) (x : X) : (P + Q).φ x = fun y => P.φ x y + Q.φ x y := rfl

/- English proof (translation)
The claim follows from `(hP.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy)`.
-/
theorem contDiffAt_of_isPotential (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) y :=
  (hP.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy)

/- English proof (translation)
Introduce `j w hw` and use `((h₁ j w ⟨hw.1, hw.2.1⟩).add (h₂ j w ⟨hw.1, hw.2.2⟩))`.
-/
theorem holoOn_add (A : FinHolAtlas e X) {W₁ W₂ : Set X} {G₁ G₂ : X → ℂ}
    (h₁ : A.HoloOn W₁ G₁) (h₂ : A.HoloOn W₂ G₂) :
    A.HoloOn (W₁ ∩ W₂) (fun z => G₁ z + G₂ z) := fun j w hw =>
  ((h₁ j w ⟨hw.1, hw.2.1⟩).add (h₂ j w ⟨hw.1, hw.2.2⟩))

/- English proof (translation)
Introduce `j w hw` and use `analyticAt_const.mul (h j w hw)`.
-/
theorem holoOn_mul (A : FinHolAtlas e X) {W : Set X} {G : X → ℂ} (h : A.HoloOn W G) (c : ℂ) :
    A.HoloOn W (fun z => c * G z) := fun j w hw => analyticAt_const.mul (h j w hw)

/- English proof (translation)
Establish `hQφ : ∀ x, Q.φ x = fun y => c * P.φ x y` using `fun x => funext (hφ x)`. Use `⟨fun x => ?_, fun x x' y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hQφ x, hU]`. Conclude with `fun j => contDiffOn_const.mul (hP.1 x j)`. Rewrite `hy` using `[hU]`.

Take `⟨W, hW, hyW, G, hG, hGe⟩` from `hP.2 x x' y hy`. Use `⟨W, hW, hyW, fun z => (c : ℂ) * G z, holoOn_mul A hG c, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[hU]`. Rewrite using `[hφ, hφ, ← mul_sub, hGe z hz, Complex.re_ofReal_mul]`.
-/
theorem isPotential_mul (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (c : ℝ)
    (Q : LocPot X) (hU : Q.U = P.U) (hφ : ∀ x y, Q.φ x y = c * P.φ x y) : IsPotential A Q := by
  have hQφ : ∀ x, Q.φ x = fun y => c * P.φ x y := fun x => funext (hφ x)
  refine ⟨fun x => ?_, fun x x' y hy => ?_⟩
  · rw [hQφ x, hU]
    exact fun j => contDiffOn_const.mul (hP.1 x j)
  · rw [hU] at hy
    obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hP.2 x x' y hy
    refine ⟨W, hW, hyW, fun z => (c : ℂ) * G z, holoOn_mul A hG c, fun z hz => ?_⟩
    rw [hU] at hz
    rw [hφ, hφ, ← mul_sub, hGe z hz, Complex.re_ofReal_mul]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `e X _ A P Q hP hQ`. Use `⟨fun x => ?_, fun x x' y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[add_U, add_φ]`. Conclude with `fun j => ((hP.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩).add ((hQ.1 x j).mono fun y hy => ⟨hy.1, hy.2.2⟩)`. Rewrite `hy` using `[add_U, add_U]`.

Take `⟨⟨hPx, hQx⟩, hPx', hQx'⟩` from `hy`. Take `⟨W₁, hW₁, hyW₁, G₁, hG₁, hGe₁⟩` from `hP.2 x x' y ⟨hPx, hPx'⟩`. Take `⟨W₂, hW₂, hyW₂, G₂, hG₂, hGe₂⟩` from `hQ.2 x x' y ⟨hQx, hQx'⟩`. Use `⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hyW₁, hyW₂⟩, fun z => G₁ z + G₂ z, holoOn_add A hG₁ hG₂, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[add_U, add_U]`.

Take `⟨⟨⟨hz₁, hz₂⟩, hzP, hzQ⟩, hzP', hzQ'⟩` from `hz`. Establish `e₁` using `hGe₁ z ⟨⟨hz₁, hzP⟩, hzP'⟩`. Establish `e₂` using `hGe₂ z ⟨⟨hz₂, hzQ⟩, hzQ'⟩`. Simplify using `only [add_φ, Complex.add_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isPotentialAdd : IsPotentialAddStatement := by
  intro e X _ A P Q hP hQ
  refine ⟨fun x => ?_, fun x x' y hy => ?_⟩
  · rw [add_U, add_φ]
    exact fun j => ((hP.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩).add
      ((hQ.1 x j).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  · rw [add_U, add_U] at hy
    obtain ⟨⟨hPx, hQx⟩, hPx', hQx'⟩ := hy
    obtain ⟨W₁, hW₁, hyW₁, G₁, hG₁, hGe₁⟩ := hP.2 x x' y ⟨hPx, hPx'⟩
    obtain ⟨W₂, hW₂, hyW₂, G₂, hG₂, hGe₂⟩ := hQ.2 x x' y ⟨hQx, hQx'⟩
    refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hyW₁, hyW₂⟩, fun z => G₁ z + G₂ z, holoOn_add A hG₁ hG₂,
      fun z hz => ?_⟩
    rw [add_U, add_U] at hz
    obtain ⟨⟨⟨hz₁, hz₂⟩, hzP, hzQ⟩, hzP', hzQ'⟩ := hz
    have e₁ := hGe₁ z ⟨⟨hz₁, hzP⟩, hzP'⟩
    have e₂ := hGe₂ z ⟨⟨hz₂, hzQ⟩, hzQ'⟩
    simp only [add_φ, Complex.add_re]
    linarith

/- English proof (translation)
Introduce `e X _ A m P hP`. Conclude with `isPotential_mul A P hP (m : ℝ) (P.zsmul m) rfl (fun _ _ => rfl)`.
-/
theorem isPotentialZsmul : IsPotentialZsmulStatement := by
  intro e X _ A m P hP
  exact isPotential_mul A P hP (m : ℝ) (P.zsmul m) rfl (fun _ _ => rfl)

/- English proof (translation)
Introduce `e X _ A c P hP`. Conclude with `isPotential_mul A P hP c (P.rsmul c) rfl (fun _ _ => rfl)`.
-/
theorem isPotentialRsmul : IsPotentialRsmulStatement := by
  intro e X _ A c P hP
  exact isPotential_mul A P hP c (P.rsmul c) rfl (fun _ _ => rfl)

/- English proof (translation)
Establish `hO : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source))` using `(B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hh)`. Use `filter_upwards [hO.mem_nhds ⟨hw, hk⟩] with w' hw'`. Conclude with `(A.chart k).left_inv hw'.2`.
-/
private theorem eventually_chart_symm_chart_comp_eq {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (h : Y → X) (hh : Continuous h)
    (j : Fin B.n) (k : Fin A.n) {w : Fin e' → ℂ} (hw : w ∈ (B.chart j).target)
    (hk : h ((B.chart j).symm w) ∈ (A.chart k).source) :
    ∀ᶠ w' in 𝓝 w, (A.chart k).symm (A.chart k (h ((B.chart j).symm w'))) = h ((B.chart j).symm w') := by
  have hO : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hh)
  filter_upwards [hO.mem_nhds ⟨hw, hk⟩] with w' hw'
  exact (A.chart k).left_inv hw'.2

/- English proof (translation)
Introduce `e e' X Y _ _ A B h hh P hP`. Use `⟨fun y j w hw => ?_, fun y y' z hz => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `A.cover (h ((B.chart j).symm w))`. Establish `hin : A.chart k (h ((B.chart j).symm w)) ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U (h y)`. Use `⟨(A.chart k).map_source hk, ?_⟩` and prove the remaining obligations.

Use `show (A.chart k).symm (A.chart k (h ((B.chart j).symm w))) ∈ P.U (h y)`. Rewrite using `[(A.chart k).left_inv hk]`. Conclude with `hw.2`. Establish `hf` using `contDiffAt_of_isPotential A P hP (h y) k hin`. Establish `hg : ContDiffAt ℝ ∞ (A.chart k ∘ h ∘ (B.chart j).symm) w` using `(AnalyticAt.contDiffAt (n := ∞) (hh.2 j k w ⟨hw.1, hk⟩)).restrict_scalars ℝ`.

Use `(ContDiffAt.congr_of_eventuallyEq (hf.comp w hg) ?_).contDiffWithinAt` and prove the remaining obligations. Use `filter_upwards [eventually_chart_symm_chart_comp_eq A B h hh.1 j k hw.1 hk] with w' hw'`. Use `show P.φ (h y) (h ((B.chart j).symm w')) = P.φ (h y) ((A.chart k).symm (A.chart k (h ((B.chart j).symm w'))))`. Rewrite using `[hw']`. Establish `hz' : h z ∈ P.U (h y) ∩ P.U (h y')` using `hz`.

Take `⟨W, hW, hzW, G, hG, hGe⟩` from `hP.2 (h y) (h y') (h z) hz'`. Use `⟨h ⁻¹' W, hW.preimage hh.1, hzW, G ∘ h, fun j w hw => ?_, fun z' hz' => hGe (h z') hz'⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `A.cover (h ((B.chart j).symm w))`. Establish `hin : A.chart k (h ((B.chart j).symm w)) ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' W`. Use `⟨(A.chart k).map_source hk, ?_⟩` and prove the remaining obligations.

Use `show (A.chart k).symm (A.chart k (h ((B.chart j).symm w))) ∈ W`. Rewrite using `[(A.chart k).left_inv hk]`. Conclude with `hw.2`. Establish `hc : AnalyticAt ℂ ((G ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (B.chart j).symm)) w` using `AnalyticAt.comp (hG k _ hin) (hh.2 j k w ⟨hw.1, hk⟩)`. Use `hc.congr ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_chart_symm_chart_comp_eq A B h hh.1 j k hw.1 hk] with w' hw'`. Use `show G ((A.chart k).symm (A.chart k (h ((B.chart j).symm w')))) = G (h ((B.chart j).symm w'))`. Rewrite using `[hw']`.
-/
theorem isPotentialPullback : IsPotentialPullbackStatement := by
  intro e e' X Y _ _ A B h hh P hP
  refine ⟨fun y j w hw => ?_, fun y y' z hz => ?_⟩
  · obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm w))
    have hin : A.chart k (h ((B.chart j).symm w)) ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U (h y) := by
      refine ⟨(A.chart k).map_source hk, ?_⟩
      show (A.chart k).symm (A.chart k (h ((B.chart j).symm w))) ∈ P.U (h y)
      rw [(A.chart k).left_inv hk]
      exact hw.2
    have hf := contDiffAt_of_isPotential A P hP (h y) k hin
    have hg : ContDiffAt ℝ ∞ (A.chart k ∘ h ∘ (B.chart j).symm) w :=
      (AnalyticAt.contDiffAt (n := ∞) (hh.2 j k w ⟨hw.1, hk⟩)).restrict_scalars ℝ
    refine (ContDiffAt.congr_of_eventuallyEq (hf.comp w hg) ?_).contDiffWithinAt
    filter_upwards [eventually_chart_symm_chart_comp_eq A B h hh.1 j k hw.1 hk] with w' hw'
    show P.φ (h y) (h ((B.chart j).symm w')) =
      P.φ (h y) ((A.chart k).symm (A.chart k (h ((B.chart j).symm w'))))
    rw [hw']
  · have hz' : h z ∈ P.U (h y) ∩ P.U (h y') := hz
    obtain ⟨W, hW, hzW, G, hG, hGe⟩ := hP.2 (h y) (h y') (h z) hz'
    refine ⟨h ⁻¹' W, hW.preimage hh.1, hzW, G ∘ h, fun j w hw => ?_, fun z' hz' => hGe (h z') hz'⟩
    obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm w))
    have hin : A.chart k (h ((B.chart j).symm w)) ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' W := by
      refine ⟨(A.chart k).map_source hk, ?_⟩
      show (A.chart k).symm (A.chart k (h ((B.chart j).symm w))) ∈ W
      rw [(A.chart k).left_inv hk]
      exact hw.2
    have hc : AnalyticAt ℂ ((G ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (B.chart j).symm)) w :=
      AnalyticAt.comp (hG k _ hin) (hh.2 j k w ⟨hw.1, hk⟩)
    refine hc.congr ?_
    filter_upwards [eventually_chart_symm_chart_comp_eq A B h hh.1 j k hw.1 hk] with w' hw'
    show G ((A.chart k).symm (A.chart k (h ((B.chart j).symm w')))) = G (h ((B.chart j).symm w'))
    rw [hw']

/- English proof (translation)
Use `filter_upwards [((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy] with z hz`. Conclude with `contDiffAt_of_isPotential A P hP x j hz`.
-/
private theorem eventually_contDiffAt_potential_chart_symm {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (x : X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) z := by
  filter_upwards [((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy] with z hz
  exact contDiffAt_of_isPotential A P hP x j hz

/- English proof (translation)
The claim follows from `hF.differentiableAt (by simp)`.
-/
private theorem differentiableAt_of_contDiffAt_infty {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ContDiffAt ℝ ∞ F y) : DifferentiableAt ℝ F y :=
  hF.differentiableAt (by simp)

/- English proof (translation)
The claim follows from `(hF.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)`.
-/
private theorem differentiableAt_fderiv_of_contDiffAt_infty {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ContDiffAt ℝ ∞ F y) : DifferentiableAt ℝ (fderiv ℝ F) y :=
  (hF.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)

/- English proof (translation)
Establish `hev : fderiv ℝ (fun z => F z + G z) =ᶠ[𝓝 y] fun z => fderiv ℝ F z + fderiv ℝ G z` using `by filter_upwards [hF, hG] with z hFz hGz`. Conclude with `fderiv_add (differentiableAt_of_contDiffAt_infty hFz) (differentiableAt_of_contDiffAt_infty hGz)`. Rewrite using `[hev.fderiv_eq]`. Conclude with `fderiv_add (differentiableAt_fderiv_of_contDiffAt_infty hF.self_of_nhds) (differentiableAt_fderiv_of_contDiffAt_infty hG.self_of_nhds)`.
-/
private theorem fderiv_fderiv_add' {n : ℕ} {F G : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ F z) (hG : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ G z) :
    fderiv ℝ (fderiv ℝ (fun z => F z + G z)) y = fderiv ℝ (fderiv ℝ F) y + fderiv ℝ (fderiv ℝ G) y := by
  have hev : fderiv ℝ (fun z => F z + G z) =ᶠ[𝓝 y] fun z => fderiv ℝ F z + fderiv ℝ G z := by
    filter_upwards [hF, hG] with z hFz hGz
    exact fderiv_add (differentiableAt_of_contDiffAt_infty hFz) (differentiableAt_of_contDiffAt_infty hGz)
  rw [hev.fderiv_eq]
  exact fderiv_add (differentiableAt_fderiv_of_contDiffAt_infty hF.self_of_nhds)
    (differentiableAt_fderiv_of_contDiffAt_infty hG.self_of_nhds)

/- English proof (translation)
Introduce `e X _ A P Q hP hQ hpP hpQ x j y hy w`. Establish `hy' : y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ P.U x ∩ Q.U x` using `hy`. Establish `hyP : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x` using `⟨hy'.1, hy'.2.1⟩`. Establish `hyQ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x` using `⟨hy'.1, hy'.2.2⟩`. Establish `hp` using `hpP x j y hyP w`.

Establish `hq` using `hpQ x j y hyQ w`. Establish `hrw : (P + Q).φ x ∘ (A.chart j).symm = fun z => (P.φ x ∘ (A.chart j).symm) z + (Q.φ x ∘ (A.chart j).symm) z` using `rfl`. Rewrite using `[hrw]`. Unfold `ReciprocityTheory.AnForm.levi at hp hq ⊢`. Rewrite using `[fderiv_fderiv_add' (eventually_contDiffAt_potential_chart_symm A P hP x j hyP) (eventually_contDiffAt_potential_chart_symm A Q hQ x j hyQ)]`.

Simplify using `only [ContinuousLinearMap.add_apply]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isPshAdd : IsPshAddStatement := by
  intro e X _ A P Q hP hQ hpP hpQ x j y hy w
  have hy' : y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ P.U x ∩ Q.U x := hy
  have hyP : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x := ⟨hy'.1, hy'.2.1⟩
  have hyQ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x := ⟨hy'.1, hy'.2.2⟩
  have hp := hpP x j y hyP w
  have hq := hpQ x j y hyQ w
  have hrw : (P + Q).φ x ∘ (A.chart j).symm =
      fun z => (P.φ x ∘ (A.chart j).symm) z + (Q.φ x ∘ (A.chart j).symm) z := rfl
  rw [hrw]
  unfold ReciprocityTheory.AnForm.levi at hp hq ⊢
  rw [fderiv_fderiv_add' (eventually_contDiffAt_potential_chart_symm A P hP x j hyP)
    (eventually_contDiffAt_potential_chart_symm A Q hQ x j hyQ)]
  simp only [ContinuousLinearMap.add_apply]
  linarith

/- English proof (translation)
Establish `hev : fderiv ℝ (fun z => c * F z) =ᶠ[𝓝 y] fun z => c • fderiv ℝ F z` using `by filter_upwards [hF] with z hFz`. Conclude with `fderiv_const_mul (differentiableAt_of_contDiffAt_infty hFz) c`. Rewrite using `[hev.fderiv_eq]`. Conclude with `fderiv_const_smul (differentiableAt_fderiv_of_contDiffAt_infty hF.self_of_nhds) c`.
-/
private theorem fderiv_fderiv_const_mul {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ F z) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => c * F z)) y = c • fderiv ℝ (fderiv ℝ F) y := by
  have hev : fderiv ℝ (fun z => c * F z) =ᶠ[𝓝 y] fun z => c • fderiv ℝ F z := by
    filter_upwards [hF] with z hFz
    exact fderiv_const_mul (differentiableAt_of_contDiffAt_infty hFz) c
  rw [hev.fderiv_eq]
  exact fderiv_const_smul (differentiableAt_fderiv_of_contDiffAt_infty hF.self_of_nhds) c

/- English proof (translation)
Introduce `e X _ A c P hc hP hpP x j y hy w`. Establish `hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x` using `hy`. Establish `hp` using `hpP x j y hy' w`. Establish `hrw : (P.rsmul c).φ x ∘ (A.chart j).symm = fun z => c * (P.φ x ∘ (A.chart j).symm) z` using `rfl`. Rewrite using `[hrw]`.

Unfold `ReciprocityTheory.AnForm.levi at hp ⊢`. Rewrite using `[fderiv_fderiv_const_mul (eventually_contDiffAt_potential_chart_symm A P hP x j hy') c]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[show ∀ a b : ℝ, (c * a + c * b) / 4 = c * ((a + b) / 4) from fun a b => by ring]`. Conclude with `mul_nonneg hc hp`.
-/
theorem isPshRsmul : IsPshRsmulStatement := by
  intro e X _ A c P hc hP hpP x j y hy w
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x := hy
  have hp := hpP x j y hy' w
  have hrw : (P.rsmul c).φ x ∘ (A.chart j).symm = fun z => c * (P.φ x ∘ (A.chart j).symm) z := rfl
  rw [hrw]
  unfold ReciprocityTheory.AnForm.levi at hp ⊢
  rw [fderiv_fderiv_const_mul (eventually_contDiffAt_potential_chart_symm A P hP x j hy') c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [show ∀ a b : ℝ, (c * a + c * b) / 4 = c * ((a + b) / 4) from fun a b => by ring]
  exact mul_nonneg hc hp

end

end ReciprocityTheory.AnForm.M
