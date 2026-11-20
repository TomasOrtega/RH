import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Hyp (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) : Prop :=
  IsOrth X x0 ∧ PropDisc X ∧ IsMetricW X la W ∧ WLower X la W ∧
    4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧
    IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z

def supR (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (ρ : ℝ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
    (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)

def LocStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ x ∈ X.dom, ∃ ε > 0, ∃ u : X.Γ → ℝ, Summable u ∧
      ∀ γ : X.Γ, ∀ y ∈ Metric.ball x ε, ‖P (lact γ.1 y)‖ ≤ u γ

def BallStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ ≤ ENNReal.ofReal C * supR X la W ρ x

def FFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)

/- English proof (translation)
Unfold `lact mat`. Use `differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem differentiable_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Differentiable ℂ (lact (Ψ := Ψ) γ) := by
  unfold lact mat
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Unfold `poin`. Establish `hχ : ∀ γ : X.Γ, ‖X.χ la γ.1‖ = 1` using `fun γ => by`. Take `⟨n, hn, h⟩` from `X.χ_fin la`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h γ.1 γ.2, norm_one])`. Establish `hn : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ = ‖P (lact γ.1 x)‖` using `fun γ => by`.

Rewrite using `[norm_mul, norm_inv, hχ γ, inv_one, one_mul]`. Distinguish the cases in `hs : Summable fun γ : X.Γ => ‖P (lact γ.1 x)‖`. Combine the equalities or inequalities in the displayed calculation. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Use `(norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hn))` and prove the remaining obligations.

Conclude with `hs.congr fun γ => (hn γ).symm`. Use `_ = ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ := by`. Rewrite using `[ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]`. Simplify using `only [ofReal_norm_eq_enorm]`. Establish `htop : ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ = ⊤`.

Assume the negation of the conclusion as `h`. Apply `hs` to reduce the goal to its premises. Establish `h2 : Summable fun γ : X.Γ => ‖P (lact γ.1 x)‖₊`. Rewrite using `[← ENNReal.tsum_coe_ne_top_iff_summable]`. Simplify `h` using `only [enorm_eq_nnnorm]`.

Conclude with `NNReal.summable_coe.2 h2`. Rewrite using `[htop]`. Conclude with `le_top`.
-/
theorem enorm_poin_le (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    ENNReal.ofReal ‖poin X la P x‖ ≤ ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ := by
  unfold poin
  have hχ : ∀ γ : X.Γ, ‖X.χ la γ.1‖ = 1 := fun γ => by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1
      (by rw [← norm_pow, h γ.1 γ.2, norm_one])
  have hn : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ = ‖P (lact γ.1 x)‖ := fun γ => by
    rw [norm_mul, norm_inv, hχ γ, inv_one, one_mul]
  by_cases hs : Summable fun γ : X.Γ => ‖P (lact γ.1 x)‖
  · calc ENNReal.ofReal ‖∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖
        ≤ ENNReal.ofReal (∑' γ : X.Γ, ‖P (lact γ.1 x)‖) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hn))
          exact hs.congr fun γ => (hn γ).symm
      _ = ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
          simp only [ofReal_norm_eq_enorm]
  · have htop : ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ = ⊤ := by
      by_contra h
      apply hs
      have h2 : Summable fun γ : X.Γ => ‖P (lact γ.1 x)‖₊ := by
        rw [← ENNReal.tsum_coe_ne_top_iff_summable]
        simpa only [enorm_eq_nnnorm] using h
      exact NNReal.summable_coe.2 h2
    rw [htop]
    exact le_top

/- English proof (translation)
Unfold `supR`. Use `iSup₂_le fun z _ => iSup_le fun hz => ENNReal.rpow_le_rpow ?_ (by norm_num)` and prove the remaining obligations. Establish `he : 0 < Real.exp (-phla X la (cpt X x z))` using `Real.exp_pos _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_div_of_pos (by positivity)]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem supR_le (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) {c : ℝ} (hc : 0 < c)
    (hW : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x) (ρ : ℝ) (x : Frame X.Ψ r) :
    supR X la W ρ x ≤ ENNReal.ofReal (1 / c) ^ (1 / 2 : ℝ) := by
  unfold supR
  refine iSup₂_le fun z _ => iSup_le fun hz => ENNReal.rpow_le_rpow ?_ (by norm_num)
  have he : 0 < Real.exp (-phla X la (cpt X x z)) := Real.exp_pos _
  calc ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)
      ≤ ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) /
          ENNReal.ofReal (c * Real.exp (-phla X la (cpt X x z))) := ENNReal.div_le_div_left (hW _ hz) _
    _ = ENNReal.ofReal (1 / c) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem norm_sgn' (p0 a : ℕ) : ‖((sgn p0 a : ℝ) : ℂ)‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Unfold `IsOrth at hx`. Unfold `dmin lminor`. Rewrite using `[hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]`. Conclude with `Finset.prod_eq_one fun a _ => norm_sgn' _ _`.
-/
theorem norm_dmin_orth' (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ)
    (i : Fin (r + 1)) : ‖dmin X.Gm x τ i‖ = 1 := by
  unfold IsOrth at hx
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  exact Finset.prod_eq_one fun a _ => norm_sgn' _ _

/- English proof (translation)
Unfold `Data.pnorm`. Simplify using `[norm_div, norm_dmin_orth' X hx]`.
-/
theorem pnorm_orth' (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  simp [norm_div, norm_dmin_orth' X hx]

/- English proof (translation)
Introduce `r X x0 hx0 hPD la W bb hW hWl hbb F P hFd hA hP hPF`. Establish `H : Hyp X x0 la W bb F P` using `⟨hx0, hPD, hW, hWl, hbb, hFd, hA, hP, hPF⟩`. Take `⟨c, hc, hcW⟩` from `hWl`. Establish `hterm : ∀ (γ : X.Γ) y, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖`. Introduce `γ y`.

Rewrite using `[norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]`. Take `⟨C1, hC1⟩` from `hB r X x0 la W bb F P H 1 one_pos le_rfl`. Establish `horth : ∀ y ∈ X.dom, IsOrth X y → ‖poin X la P y‖ ≤ max C1 0 * (1 / c) ^ (1 / 2 : ℝ)`. Introduce `y hy hyo`. Establish `h1` using `(enorm_poin_le X la P y).trans ((hC1 y hy hyo).trans (mul_le_mul_of_nonneg_left (supR_le X la W hc hcW 1 y) (zero_le)))`.

Establish `h2 : ENNReal.ofReal C1 * ENNReal.ofReal (1 / c) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (max C1 0 * (1 / c) ^ (1 / 2 : ℝ))`. Rewrite using `[ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ENNReal.ofReal_mul (le_max_right _ _)]`. Use `gcongr`. Conclude with `le_max_left _ _`. Conclude with `(ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans h2)`.

Use `⟨?_, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hF r X x0 la W bb F P H, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨ε, hε, u, hu, hub⟩` from `hL r X x0 la W bb F P H x hx`. Conclude with `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun γ => (hterm γ x).le.trans (hub γ x (Metric.mem_ball_self hε))) hu`. Unfold `poin`.

Use `differentiableOn_tsum_loc (isOpenDom X) _ (fun γ => ?_) (fun x hx => ?_)` and prove the remaining obligations. Conclude with `(differentiableOn_const _).mul (hP.1.comp (differentiable_lact γ.1).differentiableOn fun y hy => lactDom X γ.2 hy)`. Take `⟨ε, hε, u, hu, hub⟩` from `hL r X x0 la W bb F P H x hx`. Conclude with `⟨ε, hε, u, hu, fun γ y hy => (hterm γ y).le.trans (hub γ y hy)⟩`. Introduce `x hx b hb`.

Conclude with `poin_rmul X la P hP.2 hx hb`. Introduce `γ hγ x _`. Conclude with `poin_lact X la P hγ x`. Use `⟨max C1 0 * (1 / c) ^ (1 / 2 : ℝ), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hb` using `FrameDegreeData.bOf_mem X hx`.

Establish `ho : IsOrth X (rmul x (FrameDegreeData.bOf X x))` using `FrameDegreeData.ortho_bOf X hx`. Establish `hxb : rmul x (FrameDegreeData.bOf X x) ∈ X.dom` using `rmulDom X hb hx`. Rewrite using `[← FrameDegreeData.pnorm_rmul X la _ (fun y hy b hb => poin_rmul X la P hP.2 hy hb) x hx _ hb, pnorm_orth' X la _ ho]`. Conclude with `horth _ hxb ho`. Introduce `ρ hρ hρ1`.

Take `⟨C, hC⟩` from `hB r X x0 la W bb F P H ρ hρ hρ1`. Conclude with `⟨C, fun x hx hxo => (enorm_poin_le X la P x).trans (hC x hx hxo)⟩`. Introduce `la' g hg x hx`. Conclude with `poin_mul X la la' P g hg x hx`.
-/
theorem poin_of (hL : LocStatement (E := E)) (hB : BallStatement (E := E)) (hF : FFStatement (E := E)) :
    PoinStatement (E := E) := by
  intro r X x0 hx0 hPD la W bb hW hWl hbb F P hFd hA hP hPF
  have H : Hyp X x0 la W bb F P := ⟨hx0, hPD, hW, hWl, hbb, hFd, hA, hP, hPF⟩
  obtain ⟨c, hc, hcW⟩ := hWl
  have hterm : ∀ (γ : X.Γ) y, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖ := by
    intro γ y; rw [norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]
  obtain ⟨C1, hC1⟩ := hB r X x0 la W bb F P H 1 one_pos le_rfl
  have horth : ∀ y ∈ X.dom, IsOrth X y → ‖poin X la P y‖ ≤ max C1 0 * (1 / c) ^ (1 / 2 : ℝ) := by
    intro y hy hyo
    have h1 := (enorm_poin_le X la P y).trans ((hC1 y hy hyo).trans
      (mul_le_mul_of_nonneg_left (supR_le X la W hc hcW 1 y) (zero_le)))
    have h2 : ENNReal.ofReal C1 * ENNReal.ofReal (1 / c) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (max C1 0 * (1 / c) ^ (1 / 2 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ENNReal.ofReal_mul (le_max_right _ _)]
      gcongr
      exact le_max_left _ _
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans h2)
  refine ⟨?_, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hF r X x0 la W bb F P H, ?_, ?_⟩
  · intro x hx
    obtain ⟨ε, hε, u, hu, hub⟩ := hL r X x0 la W bb F P H x hx
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun γ => (hterm γ x).le.trans (hub γ x (Metric.mem_ball_self hε))) hu
  · unfold poin
    refine differentiableOn_tsum_loc (isOpenDom X) _ (fun γ => ?_) (fun x hx => ?_)
    · exact (differentiableOn_const _).mul
        (hP.1.comp (differentiable_lact γ.1).differentiableOn fun y hy => lactDom X γ.2 hy)
    · obtain ⟨ε, hε, u, hu, hub⟩ := hL r X x0 la W bb F P H x hx
      exact ⟨ε, hε, u, hu, fun γ y hy => (hterm γ y).le.trans (hub γ y hy)⟩
  · intro x hx b hb
    exact poin_rmul X la P hP.2 hx hb
  · intro γ hγ x _
    exact poin_lact X la P hγ x
  · refine ⟨max C1 0 * (1 / c) ^ (1 / 2 : ℝ), fun x hx => ?_⟩
    have hb := FrameDegreeData.bOf_mem X hx
    have ho : IsOrth X (rmul x (FrameDegreeData.bOf X x)) := FrameDegreeData.ortho_bOf X hx
    have hxb : rmul x (FrameDegreeData.bOf X x) ∈ X.dom := rmulDom X hb hx
    rw [← FrameDegreeData.pnorm_rmul X la _ (fun y hy b hb => poin_rmul X la P hP.2 hy hb) x hx _ hb,
      pnorm_orth' X la _ ho]
    exact horth _ hxb ho
  · intro ρ hρ hρ1
    obtain ⟨C, hC⟩ := hB r X x0 la W bb F P H ρ hρ hρ1
    exact ⟨C, fun x hx hxo => (enorm_poin_le X la P x).trans (hC x hx hxo)⟩
  · intro la' g hg x hx
    exact poin_mul X la la' P g hg x hx

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
