import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollB

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology Set

noncomputable section

variable {D : ℕ}

section PolyMax

variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}

/- English proof (translation)
The claim follows from `(hφ.mono h).bddAbove_of_isCompact (isCompact_closedBall z t)`.
-/
lemma polyMax_bdd (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (h : closedBall z t ⊆ U) :
    BddAbove (φ '' closedBall z t) :=
  (hφ.mono h).bddAbove_of_isCompact (isCompact_closedBall z t)

/- English proof (translation)
The claim follows from `le_csSup (polyMax_bdd hφ h) (mem_image_of_mem φ hx)`.
-/
lemma le_polyMax (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (h : closedBall z t ⊆ U) {x}
    (hx : x ∈ closedBall z t) : φ x ≤ polyMax φ z t :=
  le_csSup (polyMax_bdd hφ h) (mem_image_of_mem φ hx)

/- English proof (translation)
The claim follows from `csSup_le ((nonempty_closedBall.2 ht).image φ) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)`.
-/
lemma polyMax_le' {t c : ℝ} (ht : 0 ≤ t) (h : ∀ x ∈ closedBall z t, φ x ≤ c) :
    polyMax φ z t ≤ c :=
  csSup_le ((nonempty_closedBall.2 ht).image φ) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

/- English proof (translation)
Take `⟨a, ha, hmax⟩` from `(hφ.mono h).exists_isMaxOn (nonempty_closedBall.2 ht) (isCompact_closedBall z t)`. Conclude with `⟨a, ha, le_antisymm (le_polyMax hφ h ha) (polyMax_le' ht fun x hx => isMaxOn_iff.1 hmax x hx)⟩`.
-/
lemma polyMax_attained (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (ht : 0 ≤ t)
    (h : closedBall z t ⊆ U) : ∃ x ∈ closedBall z t, φ x = polyMax φ z t := by
  obtain ⟨a, ha, hmax⟩ := (hφ.mono h).exists_isMaxOn (nonempty_closedBall.2 ht)
    (isCompact_closedBall z t)
  exact ⟨a, ha, le_antisymm (le_polyMax hφ h ha)
    (polyMax_le' ht fun x hx => isMaxOn_iff.1 hmax x hx)⟩

/- English proof (translation)
The claim follows from `csSup_le_csSup (polyMax_bdd hφ h) ((nonempty_closedBall.2 hs).image φ) (image_mono (closedBall_subset_closedBall hst))`.
-/
lemma polyMax_mono' (hφ : UpperSemicontinuousOn φ U) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : closedBall z t ⊆ U) : polyMax φ z s ≤ polyMax φ z t :=
  csSup_le_csSup (polyMax_bdd hφ h) ((nonempty_closedBall.2 hs).image φ)
    (image_mono (closedBall_subset_closedBall hst))

/- English proof (translation)
Simplify using `[polyMax, closedBall_zero]`.
-/
lemma polyMax_zero' : polyMax φ z 0 = φ z := by
  simp [polyMax, closedBall_zero]

/- English proof (translation)
Use `set V : Set (Fin D → ℂ) := {x | x ∈ U ∧ φ x < polyMax φ z t + ε} with hVdef`. Establish `hV : IsOpen V`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `x ⟨hxU, hx⟩`. Establish `h1` using `hφ x hxU _ hx`.

Rewrite `h1` using `[nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)]`. Use `filter_upwards [h1, hU.mem_nhds hxU] with y hy hyU using ⟨hyU, hy⟩`. Establish `hsub : closedBall z t ⊆ V` using `fun x hx => ⟨h hx, lt_of_le_of_lt (le_polyMax hφ h hx) (by linarith)⟩`. Take `⟨δ, hδ, hδV⟩` from `(isCompact_closedBall z t).exists_cthickening_subset_open hV hsub`. Rewrite `hδV` using `[cthickening_closedBall hδ.le ht, add_comm δ t]`.

Establish `hVU : closedBall z (t + δ) ⊆ U` using `fun x hx => (hδV hx).1`. Use `⟨δ, hδ, hVU, fun t' ht' ht'le => ?_⟩` and prove the remaining obligations. Establish `hsub' : closedBall z t' ⊆ closedBall z (t + δ)` using `closedBall_subset_closedBall ht'le`. Take `⟨x, hx, hxe⟩` from `polyMax_attained hφ ht' (hsub'.trans hVU)`. Rewrite using `[← hxe]`.

Conclude with `(hδV (hsub' hx)).2`.
-/
lemma polyMax_usc (hU : IsOpen U) (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (ht : 0 ≤ t)
    (h : closedBall z t ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, closedBall z (t + δ) ⊆ U ∧
      ∀ t', 0 ≤ t' → t' ≤ t + δ → polyMax φ z t' < polyMax φ z t + ε := by
  set V : Set (Fin D → ℂ) := {x | x ∈ U ∧ φ x < polyMax φ z t + ε} with hVdef
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxU, hx⟩
    have h1 := hφ x hxU _ hx
    rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at h1
    filter_upwards [h1, hU.mem_nhds hxU] with y hy hyU using ⟨hyU, hy⟩
  have hsub : closedBall z t ⊆ V := fun x hx =>
    ⟨h hx, lt_of_le_of_lt (le_polyMax hφ h hx) (by linarith)⟩
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_closedBall z t).exists_cthickening_subset_open hV hsub
  rw [cthickening_closedBall hδ.le ht, add_comm δ t] at hδV
  have hVU : closedBall z (t + δ) ⊆ U := fun x hx => (hδV hx).1
  refine ⟨δ, hδ, hVU, fun t' ht' ht'le => ?_⟩
  have hsub' : closedBall z t' ⊆ closedBall z (t + δ) := closedBall_subset_closedBall ht'le
  obtain ⟨x, hx, hxe⟩ := polyMax_attained hφ ht' (hsub'.trans hVU)
  rw [← hxe]
  exact (hδV (hsub' hx)).2

/- English proof (translation)
Introduce `s hs y hy`. Establish `hexp : Real.exp s ≤ R` using `(Real.exp_le_exp.2 hs).trans_eq (Real.exp_log hR0)`. Establish `hsR : closedBall z (Real.exp s) ⊆ U` using `(closedBall_subset_closedBall hexp).trans hR`. Take `⟨δ, hδ, -, hδ'⟩` from `polyMax_usc hU hφ (Real.exp_pos s).le hsR (sub_pos.2 hy)`. Establish `hev : ∀ᶠ s' in 𝓝 s, Real.exp s' < Real.exp s + δ` using `(Real.continuous_exp.tendsto s) (Iio_mem_nhds (by linarith))`.

Apply `Filter.Eventually.filter_mono nhdsWithin_le_nhds` to reduce the goal to its premises. Use `filter_upwards [hev] with s' hs'`. Use `hδ' _ (Real.exp_pos s').le hs'.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma polyMax_exp_usc (hU : IsOpen U) (hφ : UpperSemicontinuousOn φ U) {R : ℝ} (hR0 : 0 < R)
    (hR : closedBall z R ⊆ U) :
    UpperSemicontinuousOn (fun s => polyMax φ z (Real.exp s)) (Iic (Real.log R)) := by
  intro s hs y hy
  have hexp : Real.exp s ≤ R := (Real.exp_le_exp.2 hs).trans_eq (Real.exp_log hR0)
  have hsR : closedBall z (Real.exp s) ⊆ U := (closedBall_subset_closedBall hexp).trans hR
  obtain ⟨δ, hδ, -, hδ'⟩ := polyMax_usc hU hφ (Real.exp_pos s).le hsR (sub_pos.2 hy)
  have hev : ∀ᶠ s' in 𝓝 s, Real.exp s' < Real.exp s + δ :=
    (Real.continuous_exp.tendsto s) (Iio_mem_nhds (by linarith))
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [hev] with s' hs'
  have := hδ' _ (Real.exp_pos s').le hs'.le
  linarith

end PolyMax

/- English proof (translation)
Establish `key : ∀ x ∈ s, ∀ y ∈ s, x < y → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a * x + b * y) ≤ a * f x + b * f y`. Introduce `x hx y hy hxy a b ha hb hab`. Establish `hyx : 0 < y - x` using `sub_pos.2 hxy`. Use `set β := (f y - f x) / (y - x) with hβdef`. Establish `hβ : β * (y - x) = f y - f x` using `div_mul_cancel₀ _ hyx.ne'`.

Establish `ha' : a = 1 - b` using `by linarith`. Establish `e1 : a * x + b * y - x = b * (y - x)` using `by rw [ha']; ring`. Establish `e2 : y - (a * x + b * y) = a * (y - x)` using `by rw [ha']; ring`. Establish `hp : a * x + b * y ∈ Icc x y` using `⟨by nlinarith [mul_nonneg hb hyx.le], by nlinarith [mul_nonneg ha hyx.le]⟩`. Use `h x hx y hy hxy (f x - β * x) β (by linarith) (by linarith [hβ]) _ hp` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Use `⟨hs, fun x hx y hy a b ha hb hab => ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Break down `lt_trichotomy x y with hxy | rfl | hxy` into its components or cases. Conclude with `key x hx y hy hxy a b ha hb hab`.

Rewrite using `[← add_mul, hab, one_mul, ← add_mul, hab, one_mul]`. Use `key y hy x hx hxy b a hb ha (by linarith)` as an intermediate fact. Rewrite `this` using `[add_comm (b * y)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma chord_to_convex {f : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (h : ∀ x ∈ s, ∀ y ∈ s, x < y → ∀ α β : ℝ, f x ≤ α + β * x → f y ≤ α + β * y →
      ∀ p ∈ Icc x y, f p ≤ α + β * p) : ConvexOn ℝ s f := by
  have key : ∀ x ∈ s, ∀ y ∈ s, x < y → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a * x + b * y) ≤ a * f x + b * f y := by
    intro x hx y hy hxy a b ha hb hab
    have hyx : 0 < y - x := sub_pos.2 hxy
    set β := (f y - f x) / (y - x) with hβdef
    have hβ : β * (y - x) = f y - f x := div_mul_cancel₀ _ hyx.ne'
    have ha' : a = 1 - b := by linarith
    have e1 : a * x + b * y - x = b * (y - x) := by rw [ha']; ring
    have e2 : y - (a * x + b * y) = a * (y - x) := by rw [ha']; ring
    have hp : a * x + b * y ∈ Icc x y :=
      ⟨by nlinarith [mul_nonneg hb hyx.le], by nlinarith [mul_nonneg ha hyx.le]⟩
    have := h x hx y hy hxy (f x - β * x) β (by linarith) (by linarith [hβ]) _ hp
    calc f (a * x + b * y) ≤ f x - β * x + β * (a * x + b * y) := this
      _ = a * f x + b * f y := by rw [ha']; linear_combination b * hβ
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exact key x hx y hy hxy a b ha hb hab
  · rw [← add_mul, hab, one_mul, ← add_mul, hab, one_mul]
  · have := key y hy x hx hxy b a hb ha (by linarith)
    rw [add_comm (b * y)] at this
    linarith

/- English proof (translation)
Repeatedly rewrite using `[← smul_eq_mul]`. Conclude with `Real.circleAverage_fun_smul`.
-/
lemma ca_const_mul (c : ℝ) (f : ℂ → ℝ) :
    Real.circleAverage (fun ζ => c * f ζ) 0 1 = c * Real.circleAverage f 0 1 := by
  simp_rw [← smul_eq_mul]
  exact Real.circleAverage_fun_smul

/- English proof (translation)
Establish `h1` using `Complex.reCLM.circleAverage_comp_comm (circleIntegrable_id (0 : ℂ) 1)`. Establish `h2 : Real.circleAverage (fun ζ : ℂ => ζ) 0 1 = 0`. Use `(differentiable_id (𝕜 := ℂ) (E := ℂ)).diffContOnCl (s := ball (0 : ℂ) |1|)` as an intermediate fact. Conclude with `this.circleAverage`. Simplify using `only [Function.comp_def, Complex.reCLM_apply, h2, Complex.zero_re] at h1`.

Conclude with `h1`.
-/
lemma ca_re : Real.circleAverage (fun ζ : ℂ => ζ.re) 0 1 = 0 := by
  have h1 := Complex.reCLM.circleAverage_comp_comm (circleIntegrable_id (0 : ℂ) 1)
  have h2 : Real.circleAverage (fun ζ : ℂ => ζ) 0 1 = 0 := by
    have := (differentiable_id (𝕜 := ℂ) (E := ℂ)).diffContOnCl (s := ball (0 : ℂ) |1|)
    exact this.circleAverage
  simp only [Function.comp_def, Complex.reCLM_apply, h2, Complex.zero_re] at h1
  exact h1

section Chord

variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}

/- English proof (translation)
Use `set f : ℝ → ℝ := fun s => polyMax φ z (Real.exp s) with hf`. Use `set H : ℝ → ℝ := fun s => f s + δ * Real.exp s ^ 2 - α - β * s - δ * Real.exp b ^ 2 with hH`. Establish `hbR : Real.exp b ≤ R` using `(Real.exp_le_exp.2 hb).trans_eq (Real.exp_log hR0)`. Establish `hfu : UpperSemicontinuousOn f (Icc a b)` using `(polyMax_exp_usc hU hφ.1 hR0 hR).mono (fun x hx => hx.2.trans hb)`. Establish `hHu : UpperSemicontinuousOn H (Icc a b)`.

Establish `hc : Continuous fun s : ℝ => δ * Real.exp s ^ 2 - α - β * s - δ * Real.exp b ^ 2` using `by fun_prop`. Establish `hHeq : H = fun x => f x + (δ * Real.exp x ^ 2 - α - β * x - δ * Real.exp b ^ 2)`. Use function extensionality and compare the values at `x`. Use `show f x + δ * Real.exp x ^ 2 - α - β * x - δ * Real.exp b ^ 2 = _`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hHeq]`. Conclude with `hfu.add (hc.upperSemicontinuous.upperSemicontinuousOn _)`. Take `⟨s0, hs0, hmax⟩` from `hHu.exists_isMaxOn ⟨a, left_mem_Icc.2 hab.le⟩ isCompact_Icc`. Establish `hHs` using `isMaxOn_iff.1 hmax s hs`. It suffices to establish `hneg : H s0 ≤ 0 by`.

Establish `: H s ≤ 0` using `hHs.trans hneg`. Simplify using `only [hH, hf] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hpos`. Use `push Not at hpos`.

Establish `hea : Real.exp a ^ 2 ≤ Real.exp b ^ 2`. Use `Real.exp_le_exp.2 hab.le` as an intermediate fact. Use `Real.exp_pos a` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `ha0 : a < s0`.

Break down `eq_or_lt_of_le hs0.1 with h | h` into its components or cases. Rewrite `hpos` using `[← h]`. Simplify using `only [hH, hf] at hpos`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `h`.

Establish `hs0b : s0 < b`. Break down `eq_or_lt_of_le hs0.2 with h | h` into its components or cases. Rewrite `hpos` using `[h]`. Simplify using `only [hH, hf] at hpos`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `h`. Use `set r0 := Real.exp s0 with hr0`. Establish `hr0pos : 0 < r0` using `Real.exp_pos _`. Establish `h1 : Real.exp a < r0` using `Real.exp_lt_exp.2 ha0`. Establish `h2 : r0 < Real.exp b` using `Real.exp_lt_exp.2 hs0b`.

Use `set ρ := min (r0 - Real.exp a) (Real.exp b - r0) with hρ`. Establish `hρpos : 0 < ρ` using `lt_min (by linarith) (by linarith)`. Establish `hρ1 : ρ ≤ r0 - Real.exp a` using `min_le_left _ _`. Establish `hρ2 : ρ ≤ Real.exp b - r0` using `min_le_right _ _`. Establish `hea0 : 0 < Real.exp a` using `Real.exp_pos a`.

Establish `hr0U : closedBall z r0 ⊆ U` using `(closedBall_subset_closedBall (by linarith)).trans hR`. Take `⟨x0, hx0, hx0e⟩` from `polyMax_attained hφ.1 hr0pos.le hr0U`. Use `set u0 : Fin D → ℂ := ((r0 : ℂ)⁻¹) • (x0 - z) with hu0def`. Establish `hr0c : (r0 : ℂ) ≠ 0` using `by exact_mod_cast hr0pos.ne'`. Establish `hu0 : ‖u0‖ ≤ 1`.

Rewrite `hx0` using `[mem_closedBall, dist_eq_norm]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[u0, norm_smul, abs_of_pos hr0pos]`. Use `_ ≤ r0⁻¹ * r0 := by gcongr`. Use `_ = 1 := inv_mul_cancel₀ hr0pos.ne'`.

Establish `hx0eq : x0 = z + (r0 : ℂ) • u0`. Rewrite using `[hu0def, smul_smul, mul_inv_cancel₀ hr0c, one_smul, add_sub_cancel]`. Use `clear_value u0`. Use `set P : ℂ → ℂ := fun ζ => (r0 : ℂ) + (ρ : ℂ) * ζ with hP`. Establish `hPle : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ‖P ζ‖ ≤ r0 + ρ`.

Introduce `ζ hζ`. Combine the equalities or inequalities in the displayed calculation. Establish `hPge : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → r0 - ρ ≤ ‖P ζ‖`. Introduce `ζ hζ`. Use `norm_sub_le (P ζ) ((ρ : ℂ) * ζ)` as an intermediate fact.

Establish `e : P ζ - (ρ : ℂ) * ζ = r0` using `by simp [P]`. Rewrite `this` using `[e]`. Establish `: ‖(r0 : ℂ)‖ = r0` using `by simp [abs_of_pos hr0pos]`. Establish `: ‖(ρ : ℂ) * ζ‖ = ρ * ‖ζ‖` using `by simp [abs_of_pos hρpos]`. Use polynomial arithmetic with `[norm_nonneg ζ]`.

Establish `hPpos : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → 0 < ‖P ζ‖` using `fun ζ hζ => by linarith [hPge ζ hζ]`. Use `set w : Fin D → ℂ := (ρ : ℂ) • u0 with hw`. Establish `hpt : ∀ ζ : ℂ, x0 + ζ • w = z + P ζ • u0`. Introduce `ζ`. Rewrite using `[hx0eq, hw, smul_smul, add_assoc, ← add_smul]`.

Use `congr 2`. Simplify using `only [P]`. Expand and normalize the polynomial expressions, which then agree. Establish `hin : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → x0 + ζ • w ∈ closedBall z ‖P ζ‖`. Introduce `ζ hζ`.

Rewrite using `[hpt, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]`. Use polynomial arithmetic with `[norm_nonneg (P ζ)]`. Establish `hballU : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → closedBall z ‖P ζ‖ ⊆ U` using `fun ζ hζ => (closedBall_subset_closedBall (by linarith [hPle ζ hζ])).trans hR`. Take `⟨hint, hmean⟩` from `hφ.2 x0 w (fun ζ hζ => hballU ζ hζ (hin ζ hζ))`. Use `set K := H s0 + α + δ * Real.exp b ^ 2 with hK`.

Use `set g : ℂ → ℝ := fun ζ => K - δ * ‖P ζ‖ ^ 2 + β * Real.log ‖P ζ‖ with hg`. Establish `hbound : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → φ (x0 + ζ • w) ≤ g ζ`. Introduce `ζ hζ`. Establish `hpos` using `hPpos ζ hζ`. Establish `hX : Real.log ‖P ζ‖ ∈ Icc a b`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Real.le_log_iff_exp_le hpos]`. Combine the linear relations using `[hPge ζ hζ]`. Rewrite using `[Real.log_le_iff_le_exp hpos]`. Combine the linear relations using `[hPle ζ hζ]`.

Establish `hHX` using `isMaxOn_iff.1 hmax _ hX`. Simplify using `only [hH, hf, Real.exp_log hpos] at hHX`. Use `le_polyMax hφ.1 (hballU ζ hζ) (hin ζ hζ)` as an intermediate fact. Simplify using `only [hg, hK]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsph : ∀ ζ ∈ sphere (0 : ℂ) |1|, ‖ζ‖ = 1` using `by intro ζ hζ; simpa using hζ`. Establish `hcb : ∀ ζ ∈ closedBall (0 : ℂ) |1|, ‖ζ‖ ≤ 1` using `by intro ζ hζ; simpa using hζ`. Establish `hPd : Differentiable ℂ P` using `by rw [hP]; fun_prop`. Establish `hPcont : Continuous P` using `hPd.continuous`. Establish `hlogc : ContinuousOn (fun ζ => Real.log ‖P ζ‖) (sphere (0 : ℂ) |1|)` using `(hPcont.norm.continuousOn).log (fun ζ hζ => (hPpos ζ (hsph ζ hζ).le).ne')`.

Establish `hsqc : Continuous (fun ζ => ‖P ζ‖ ^ 2)` using `hPcont.norm.pow 2`. Establish `hA2 : Real.circleAverage (fun ζ => Real.log ‖P ζ‖) 0 1 = s0`. Establish `han : AnalyticOnNhd ℂ P (closedBall 0 |1|)` using `fun x _ => hPd.analyticAt x`. Rewrite using `[AnalyticOnNhd.circleAverage_log_norm_of_ne_zero han (fun u hu => norm_ne_zero_iff.1 (hPpos u (hcb u hu)).ne')]`. Establish `: P 0 = (r0 : ℂ)` using `by simp [hP]`.

Rewrite using `[this, Complex.norm_real, Real.norm_of_nonneg hr0pos.le, hr0, Real.log_exp]`. Establish `hA1 : Real.circleAverage (fun ζ => ‖P ζ‖ ^ 2) 0 1 = r0 ^ 2 + ρ ^ 2`. Establish `heq : Set.EqOn (fun ζ => ‖P ζ‖ ^ 2) (fun ζ => (r0 ^ 2 + ρ ^ 2) + (2 * r0 * ρ) * ζ.re) (sphere (0 : ℂ) |1|)`. Introduce `ζ hζ`. Establish `hn` using `hsph ζ hζ`.

Establish `h1 : ζ.re * ζ.re + ζ.im * ζ.im = 1`. Rewrite using `[← Complex.normSq_apply, ← Complex.sq_norm, hn]`. Evaluate the numerical expressions. Simplify using `only [hP]`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`.

Simplify using `only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]`. Take the linear combination `ρ ^ 2 * h1`. Rewrite using `[Real.circleAverage_congr_sphere heq, Real.circleAverage_fun_add (circleIntegrable_const _ _ _) ((by fun_prop : Continuous (fun ζ : ℂ => 2 * r0 * ρ * ζ.re)).continuousOn.circleIntegrable'), Real.circleAverage_const, ca_const_mul, ca_re]`. Expand and normalize the polynomial expressions, which then agree. Establish `hgint : CircleIntegrable g 0 1`.

Apply `ContinuousOn.circleIntegrable'` to reduce the goal to its premises. Conclude with `(continuousOn_const.sub (continuousOn_const.mul hsqc.continuousOn)).add (continuousOn_const.mul hlogc)`. Establish `hCAg : Real.circleAverage g 0 1 = K - δ * (r0 ^ 2 + ρ ^ 2) + β * s0`. Establish `i1 : CircleIntegrable (fun ζ => K - δ * ‖P ζ‖ ^ 2) 0 1` using `(continuous_const.sub (continuous_const.mul hsqc)).continuousOn.circleIntegrable'`. Establish `i2 : CircleIntegrable (fun ζ => β * Real.log ‖P ζ‖) 0 1` using `(continuousOn_const.mul hlogc).circleIntegrable'`.

Establish `i3 : CircleIntegrable (fun ζ => δ * ‖P ζ‖ ^ 2) 0 1` using `(continuous_const.mul hsqc).continuousOn.circleIntegrable'`. Rewrite using `[hg, Real.circleAverage_fun_add i1 i2, Real.circleAverage_fun_sub (circleIntegrable_const _ _ _) i3, Real.circleAverage_const, ca_const_mul, ca_const_mul, hA1, hA2]`. Establish `hφx0 : φ x0 = H s0 - δ * r0 ^ 2 + α + β * s0 + δ * Real.exp b ^ 2`. Rewrite using `[hx0e]`. Use `show polyMax φ z r0 = (polyMax φ z r0 + δ * r0 ^ 2 - α - β * s0 - δ * Real.exp b ^ 2) - δ * r0 ^ 2 + α + β * s0 + δ * Real.exp b ^ 2`.

Expand and normalize the polynomial expressions, which then agree. Establish `hle` using `hmean.trans (Real.circleAverage_mono hint hgint (fun ζ hζ => hbound ζ (hsph ζ hζ).le))`. Rewrite `hle` using `[hCAg, hφx0]`. Combine the linear relations using `[hK, mul_pos hδ (pow_pos hρpos 2)]`.
-/
lemma polydiscMax_exp_chord_bound (hU : IsOpen U) (hφ : IsPsh U φ) {R : ℝ} (hR0 : 0 < R)
    (hR : closedBall z R ⊆ U) {a b α β : ℝ} (hab : a < b) (hb : b ≤ Real.log R)
    (ha' : polyMax φ z (Real.exp a) ≤ α + β * a) (hb' : polyMax φ z (Real.exp b) ≤ α + β * b)
    {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ∈ Icc a b) :
    polyMax φ z (Real.exp s) + δ * Real.exp s ^ 2 ≤ α + β * s + δ * Real.exp b ^ 2 := by
  set f : ℝ → ℝ := fun s => polyMax φ z (Real.exp s) with hf
  set H : ℝ → ℝ := fun s => f s + δ * Real.exp s ^ 2 - α - β * s - δ * Real.exp b ^ 2 with hH
  have hbR : Real.exp b ≤ R := (Real.exp_le_exp.2 hb).trans_eq (Real.exp_log hR0)
  have hfu : UpperSemicontinuousOn f (Icc a b) :=
    (polyMax_exp_usc hU hφ.1 hR0 hR).mono (fun x hx => hx.2.trans hb)
  have hHu : UpperSemicontinuousOn H (Icc a b) := by
    have hc : Continuous fun s : ℝ => δ * Real.exp s ^ 2 - α - β * s - δ * Real.exp b ^ 2 := by
      fun_prop
    have hHeq : H = fun x => f x + (δ * Real.exp x ^ 2 - α - β * x - δ * Real.exp b ^ 2) := by
      funext x
      show f x + δ * Real.exp x ^ 2 - α - β * x - δ * Real.exp b ^ 2 = _
      ring
    rw [hHeq]
    exact hfu.add (hc.upperSemicontinuous.upperSemicontinuousOn _)
  obtain ⟨s0, hs0, hmax⟩ := hHu.exists_isMaxOn ⟨a, left_mem_Icc.2 hab.le⟩ isCompact_Icc
  have hHs := isMaxOn_iff.1 hmax s hs
  suffices hneg : H s0 ≤ 0 by
    have : H s ≤ 0 := hHs.trans hneg
    simp only [hH, hf] at this
    linarith
  by_contra hpos
  push Not at hpos
  have hea : Real.exp a ^ 2 ≤ Real.exp b ^ 2 := by
    have := Real.exp_le_exp.2 hab.le
    have := Real.exp_pos a
    nlinarith
  have ha0 : a < s0 := by
    rcases eq_or_lt_of_le hs0.1 with h | h
    · rw [← h] at hpos
      simp only [hH, hf] at hpos
      nlinarith
    · exact h
  have hs0b : s0 < b := by
    rcases eq_or_lt_of_le hs0.2 with h | h
    · rw [h] at hpos
      simp only [hH, hf] at hpos
      nlinarith
    · exact h
  set r0 := Real.exp s0 with hr0
  have hr0pos : 0 < r0 := Real.exp_pos _
  have h1 : Real.exp a < r0 := Real.exp_lt_exp.2 ha0
  have h2 : r0 < Real.exp b := Real.exp_lt_exp.2 hs0b
  set ρ := min (r0 - Real.exp a) (Real.exp b - r0) with hρ
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρ1 : ρ ≤ r0 - Real.exp a := min_le_left _ _
  have hρ2 : ρ ≤ Real.exp b - r0 := min_le_right _ _
  have hea0 : 0 < Real.exp a := Real.exp_pos a
  have hr0U : closedBall z r0 ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hR
  obtain ⟨x0, hx0, hx0e⟩ := polyMax_attained hφ.1 hr0pos.le hr0U
  set u0 : Fin D → ℂ := ((r0 : ℂ)⁻¹) • (x0 - z) with hu0def
  have hr0c : (r0 : ℂ) ≠ 0 := by exact_mod_cast hr0pos.ne'
  have hu0 : ‖u0‖ ≤ 1 := by
    rw [mem_closedBall, dist_eq_norm] at hx0
    calc ‖u0‖ = r0⁻¹ * ‖x0 - z‖ := by
          simp [u0, norm_smul, abs_of_pos hr0pos]
      _ ≤ r0⁻¹ * r0 := by gcongr
      _ = 1 := inv_mul_cancel₀ hr0pos.ne'
  have hx0eq : x0 = z + (r0 : ℂ) • u0 := by
    rw [hu0def, smul_smul, mul_inv_cancel₀ hr0c, one_smul, add_sub_cancel]
  clear_value u0
  set P : ℂ → ℂ := fun ζ => (r0 : ℂ) + (ρ : ℂ) * ζ with hP
  have hPle : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ‖P ζ‖ ≤ r0 + ρ := by
    intro ζ hζ
    calc ‖P ζ‖ ≤ ‖(r0 : ℂ)‖ + ‖(ρ : ℂ) * ζ‖ := norm_add_le _ _
      _ = r0 + ρ * ‖ζ‖ := by simp [abs_of_pos hr0pos, abs_of_pos hρpos]
      _ ≤ r0 + ρ := by nlinarith [norm_nonneg ζ]
  have hPge : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → r0 - ρ ≤ ‖P ζ‖ := by
    intro ζ hζ
    have := norm_sub_le (P ζ) ((ρ : ℂ) * ζ)
    have e : P ζ - (ρ : ℂ) * ζ = r0 := by simp [P]
    rw [e] at this
    have : ‖(r0 : ℂ)‖ = r0 := by simp [abs_of_pos hr0pos]
    have : ‖(ρ : ℂ) * ζ‖ = ρ * ‖ζ‖ := by simp [abs_of_pos hρpos]
    nlinarith [norm_nonneg ζ]
  have hPpos : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → 0 < ‖P ζ‖ := fun ζ hζ => by linarith [hPge ζ hζ]
  set w : Fin D → ℂ := (ρ : ℂ) • u0 with hw
  have hpt : ∀ ζ : ℂ, x0 + ζ • w = z + P ζ • u0 := by
    intro ζ
    rw [hx0eq, hw, smul_smul, add_assoc, ← add_smul]
    congr 2
    simp only [P]
    ring
  have hin : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → x0 + ζ • w ∈ closedBall z ‖P ζ‖ := by
    intro ζ hζ
    rw [hpt, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg (P ζ)]
  have hballU : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → closedBall z ‖P ζ‖ ⊆ U := fun ζ hζ =>
    (closedBall_subset_closedBall (by linarith [hPle ζ hζ])).trans hR
  obtain ⟨hint, hmean⟩ := hφ.2 x0 w (fun ζ hζ => hballU ζ hζ (hin ζ hζ))

  set K := H s0 + α + δ * Real.exp b ^ 2 with hK
  set g : ℂ → ℝ := fun ζ => K - δ * ‖P ζ‖ ^ 2 + β * Real.log ‖P ζ‖ with hg
  have hbound : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → φ (x0 + ζ • w) ≤ g ζ := by
    intro ζ hζ
    have hpos := hPpos ζ hζ
    have hX : Real.log ‖P ζ‖ ∈ Icc a b := by
      constructor
      · rw [Real.le_log_iff_exp_le hpos]; linarith [hPge ζ hζ]
      · rw [Real.log_le_iff_le_exp hpos]; linarith [hPle ζ hζ]
    have hHX := isMaxOn_iff.1 hmax _ hX
    simp only [hH, hf, Real.exp_log hpos] at hHX
    have := le_polyMax hφ.1 (hballU ζ hζ) (hin ζ hζ)
    simp only [hg, hK]
    linarith
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) |1|, ‖ζ‖ = 1 := by intro ζ hζ; simpa using hζ
  have hcb : ∀ ζ ∈ closedBall (0 : ℂ) |1|, ‖ζ‖ ≤ 1 := by intro ζ hζ; simpa using hζ
  have hPd : Differentiable ℂ P := by rw [hP]; fun_prop
  have hPcont : Continuous P := hPd.continuous
  have hlogc : ContinuousOn (fun ζ => Real.log ‖P ζ‖) (sphere (0 : ℂ) |1|) :=
    (hPcont.norm.continuousOn).log (fun ζ hζ => (hPpos ζ (hsph ζ hζ).le).ne')
  have hsqc : Continuous (fun ζ => ‖P ζ‖ ^ 2) := hPcont.norm.pow 2
  have hA2 : Real.circleAverage (fun ζ => Real.log ‖P ζ‖) 0 1 = s0 := by
    have han : AnalyticOnNhd ℂ P (closedBall 0 |1|) := fun x _ => hPd.analyticAt x
    rw [AnalyticOnNhd.circleAverage_log_norm_of_ne_zero han
      (fun u hu => norm_ne_zero_iff.1 (hPpos u (hcb u hu)).ne')]
    have : P 0 = (r0 : ℂ) := by simp [hP]
    rw [this, Complex.norm_real, Real.norm_of_nonneg hr0pos.le, hr0, Real.log_exp]
  have hA1 : Real.circleAverage (fun ζ => ‖P ζ‖ ^ 2) 0 1 = r0 ^ 2 + ρ ^ 2 := by
    have heq : Set.EqOn (fun ζ => ‖P ζ‖ ^ 2) (fun ζ => (r0 ^ 2 + ρ ^ 2) + (2 * r0 * ρ) * ζ.re)
        (sphere (0 : ℂ) |1|) := by
      intro ζ hζ
      have hn := hsph ζ hζ
      have h1 : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
        rw [← Complex.normSq_apply, ← Complex.sq_norm, hn]; norm_num
      simp only [hP]
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      linear_combination ρ ^ 2 * h1
    rw [Real.circleAverage_congr_sphere heq, Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
      ((by fun_prop : Continuous (fun ζ : ℂ => 2 * r0 * ρ * ζ.re)).continuousOn.circleIntegrable'),
      Real.circleAverage_const, ca_const_mul, ca_re]
    ring
  have hgint : CircleIntegrable g 0 1 := by
    apply ContinuousOn.circleIntegrable'
    exact (continuousOn_const.sub (continuousOn_const.mul hsqc.continuousOn)).add
      (continuousOn_const.mul hlogc)
  have hCAg : Real.circleAverage g 0 1 = K - δ * (r0 ^ 2 + ρ ^ 2) + β * s0 := by
    have i1 : CircleIntegrable (fun ζ => K - δ * ‖P ζ‖ ^ 2) 0 1 :=
      (continuous_const.sub (continuous_const.mul hsqc)).continuousOn.circleIntegrable'
    have i2 : CircleIntegrable (fun ζ => β * Real.log ‖P ζ‖) 0 1 :=
      (continuousOn_const.mul hlogc).circleIntegrable'
    have i3 : CircleIntegrable (fun ζ => δ * ‖P ζ‖ ^ 2) 0 1 :=
      (continuous_const.mul hsqc).continuousOn.circleIntegrable'
    rw [hg, Real.circleAverage_fun_add i1 i2, Real.circleAverage_fun_sub
      (circleIntegrable_const _ _ _) i3,
      Real.circleAverage_const, ca_const_mul, ca_const_mul, hA1, hA2]
  have hφx0 : φ x0 = H s0 - δ * r0 ^ 2 + α + β * s0 + δ * Real.exp b ^ 2 := by
    rw [hx0e]
    show polyMax φ z r0 = (polyMax φ z r0 + δ * r0 ^ 2 - α - β * s0 - δ * Real.exp b ^ 2)
      - δ * r0 ^ 2 + α + β * s0 + δ * Real.exp b ^ 2
    ring
  have hle := hmean.trans
    (Real.circleAverage_mono hint hgint (fun ζ hζ => hbound ζ (hsph ζ hζ).le))
  rw [hCAg, hφx0] at hle
  linarith [hK, mul_pos hδ (pow_pos hρpos 2)]

end Chord

/- English proof (translation)
Introduce `D U φ z R hU hφ hR0 hR`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `chord_to_convex (convex_Iic _) fun x hx y hy hxy α β hx' hy' p hp => ?_` and prove the remaining obligations. Use `le_of_forall_pos_le_add fun e he => ?_` and prove the remaining obligations. Establish `hB : 0 < Real.exp y ^ 2 + 1` using `by positivity`.

Establish `key` using `polydiscMax_exp_chord_bound hU hφ hR0 hR hxy hy hx' hy' (div_pos he hB) hp`. Establish `h2 : e / (Real.exp y ^ 2 + 1) * Real.exp y ^ 2 ≤ e`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ hB]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : 0 ≤ e / (Real.exp y ^ 2 + 1) * Real.exp p ^ 2` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `fun s hs t ht hst => polyMax_mono' hφ.1 hs.1.le hst ((closedBall_subset_closedBall ht.2).trans hR)`. Conclude with `fun t ht0 htR => polyMax_attained hφ.1 ht0 ((closedBall_subset_closedBall htR).trans hR)`. Establish `h0U : closedBall z 0 ⊆ U` using `(closedBall_subset_closedBall hR0.le).trans hR`. Use `tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with t ht htR`. Establish `hsub : closedBall z t ⊆ U` using `(closedBall_subset_closedBall (le_of_lt htR)).trans hR`. Use `le_polyMax hφ.1 hsub (mem_closedBall_self (le_of_lt ht))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨δ, hδ, -, hδ'⟩` from `polyMax_usc hU hφ.1 le_rfl h0U (sub_pos.2 ha)`.

Rewrite `hδ'` using `[polyMax_zero']`. Use `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with t ht htδ`. Use `hδ' t (le_of_lt ht) (by simp only [zero_add]; exact le_of_lt htδ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem polyMaxLogConvex_thm : PolyMaxLogConvexStatement := by
  intro D U φ z R hU hφ hR0 hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine chord_to_convex (convex_Iic _) fun x hx y hy hxy α β hx' hy' p hp => ?_
    refine le_of_forall_pos_le_add fun e he => ?_
    have hB : 0 < Real.exp y ^ 2 + 1 := by positivity
    have key := polydiscMax_exp_chord_bound hU hφ hR0 hR hxy hy hx' hy' (div_pos he hB) hp
    have h2 : e / (Real.exp y ^ 2 + 1) * Real.exp y ^ 2 ≤ e := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hB]; nlinarith
    have h3 : 0 ≤ e / (Real.exp y ^ 2 + 1) * Real.exp p ^ 2 := by positivity
    linarith
  · exact fun s hs t ht hst =>
      polyMax_mono' hφ.1 hs.1.le hst ((closedBall_subset_closedBall ht.2).trans hR)
  · exact fun t ht0 htR => polyMax_attained hφ.1 ht0 ((closedBall_subset_closedBall htR).trans hR)
  · have h0U : closedBall z 0 ⊆ U := (closedBall_subset_closedBall hR0.le).trans hR
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with t ht htR
      have hsub : closedBall z t ⊆ U :=
        (closedBall_subset_closedBall (le_of_lt htR)).trans hR
      have := le_polyMax hφ.1 hsub (mem_closedBall_self (le_of_lt ht))
      linarith
    · obtain ⟨δ, hδ, -, hδ'⟩ := polyMax_usc hU hφ.1 le_rfl h0U (sub_pos.2 ha)
      rw [polyMax_zero'] at hδ'
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with t ht htδ
      have := hδ' t (le_of_lt ht) (by simp only [zero_add]; exact le_of_lt htδ)
      linarith

/- English proof (translation)
Introduce `D ρ U φ hU hφ`. Use `⟨fun ε hε => mollify_main ρ hU hφ hε, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, hrU⟩` from `Metric.isOpen_iff.1 hU z hz`. Establish `hR0 : 0 < r / 2` using `by positivity`. Establish `hRU : closedBall z (r / 2) ⊆ U` using `(closedBall_subset_ball (by linarith)).trans hrU`.

Establish `hlim` using `(polyMaxLogConvex_thm D U φ z (r / 2) hU hφ hR0 hRU).2.2.2`. Establish `hsh : ∀ ε, 0 < ε → ε < r / 2 → z ∈ shrink U ε` using `fun ε _ hεR => (closedBall_subset_closedBall hεR.le).trans hRU`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with ε hε hεR`. Conclude with `((mollify_main ρ hU hφ hε).2.2.2 z (hsh ε hε hεR)).1`.

Use `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with ε hε hεR`. Conclude with `((mollify_main ρ hU hφ hε).2.2.2 z (hsh ε hε hεR)).2`.
-/
theorem mollify_thm : MollifyStatement := by
  intro D ρ U φ hU hφ
  refine ⟨fun ε hε => mollify_main ρ hU hφ hε, fun z hz => ?_⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hz
  have hR0 : 0 < r / 2 := by positivity
  have hRU : closedBall z (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hlim := (polyMaxLogConvex_thm D U φ z (r / 2) hU hφ hR0 hRU).2.2.2
  have hsh : ∀ ε, 0 < ε → ε < r / 2 → z ∈ shrink U ε := fun ε _ hεR =>
    (closedBall_subset_closedBall hεR.le).trans hRU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with ε hε hεR
    exact ((mollify_main ρ hU hφ hε).2.2.2 z (hsh ε hε hεR)).1
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with ε hε hεR
    exact ((mollify_main ρ hU hφ hε).2.2.2 z (hsh ε hε hεR)).2

/- English proof (translation)
The claim follows from `mollificationSecondOrder_holds`.
-/
theorem mollification_second_order : MollificationSecondOrder :=
  mollificationSecondOrder_holds

end

end ReciprocityTheory.AnForm.A
