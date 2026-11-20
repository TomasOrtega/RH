import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAngleFormReEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsC1DensityForLinePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartwiseC1DensityOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDbarQuotientFormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CurveDens

open GlobalTheory.Twist (resM)

/- English proof (translation)
Unfold `leviForm ddbar`. Use `del_congr ?_` and prove the remaining obligations. Use `filter_upwards [h.eventuallyEq_nhds] with x hx`. Conclude with `dbar_congr (hx.mono fun w hw => by simp only [hw])`.
-/
theorem leviForm_congr_germ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {u u' : E → ℝ} {z : E} (h : u =ᶠ[𝓝 z] u') :
    leviForm u z = leviForm u' z := by
  unfold leviForm ddbar
  refine del_congr ?_
  filter_upwards [h.eventuallyEq_nhds] with x hx
  exact dbar_congr (hx.mono fun w hw => by simp only [hw])

/- English proof (translation)
Establish `e : N / (A * B) = v` using `by rw [hN]; field_simp`. Rewrite using `[e, hx, hy, hN, hc, hc']`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem green_algebra (π A B v bc bc' ch ch' lA lB x y N : ℝ) (n : ℕ) (hπ : π ≠ 0) (hA : 0 < A)
    (hB : 0 < B) (hN : N = v * A * B) (hx : x = (A * B - N) * (π * bc))
    (hy : y = (B * A - N) * (π * bc')) (hc : ch = -lA / π) (hc' : ch' = -lB / π) :
    v ^ (n + 1) * (ch - ch') + (n + 1) * v ^ n * (1 - v) * (bc - bc') =
      -(1 / π) * ((n + 1) * (N / (A * B)) ^ n * ((y - x) / (A * B)) +
        (N / (A * B)) ^ (n + 1) * (lA - lB)) := by
  have e : N / (A * B) = v := by rw [hN]; field_simp
  rw [e, hx, hy, hN, hc, hc']
  field_simp
  ring

/- English proof (translation)
Set `c₀ : VB.Chart L 1` to `⟨U, fun _ => t, ht⟩`. Establish `h₀` using `g.form_frame c₀ hy 0 0`. Establish `h₁` using `(g.posDef c₀ y hy).diag_pos (i := 0)`. Establish `h₂ : g.form t t y = g.G c₀ y 0 0` using `h₀`. Rewrite using `[h₂]`.

Conclude with `(Complex.pos_iff.1 h₁).1`.
-/
theorem form_frame_re_pos {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : X.Modules} (g : Met p σ L 1) {U : X.Opens} {t : Γ(L, U)}
    (ht : IsFrame (fun _ : Fin 1 => t)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    0 < (g.form t t y).re := by
  let c₀ : VB.Chart L 1 := ⟨U, fun _ => t, ht⟩
  have h₀ := g.form_frame c₀ hy 0 0
  have h₁ := (g.posDef c₀ y hy).diag_pos (i := 0)
  have h₂ : g.form t t y = g.G c₀ y 0 0 := h₀
  rw [h₂]
  exact (Complex.pos_iff.1 h₁).1

/- English proof (translation)
Take `⟨U₁, e₁, hx₁, he₁⟩` from `hL (y.1 (IsLocalRing.closedPoint ℂ))`. Take `⟨U₂, e₂, hx₂, he₂⟩` from `hL' (y.1 (IsLocalRing.closedPoint ℂ))`. Establish `hU : y ∈ ptsIn p σ (U₁ ⊓ U₂)` using `mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hx₁, mem_ptsIn.2 hx₂⟩`. Take `⟨U, hUdef⟩ : ∃ U, U = U₁ ⊓ U₂` from `⟨_, rfl⟩`. Rewrite `hU` using `[← hUdef]`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : Γ(L, U), IsFrame (fun _ : Fin 1 => t) := by`. Substitute `hUdef` using the available equality. Use `⟨resM L inf_le_left (e₁ 0), ?_⟩` and prove the remaining obligations. Establish `e : (fun _ : Fin 1 => resM L (inf_le_left : U₁ ⊓ U₂ ≤ U₁) (e₁ 0)) = fun i => resM L inf_le_left (e₁ i)`. Use function extensionality and compare the values at `i`.

Rewrite using `[Subsingleton.elim i 0]`. Rewrite using `[e]`. Conclude with `he₁.res inf_le_left`. Choose the witnesses or unpack the hypotheses as in `⟨t', ht'⟩ : ∃ t' : Γ(L', U), IsFrame (fun _ : Fin 1 => t') := by`. Substitute `hUdef` using the available equality.

Use `⟨resM L' inf_le_right (e₂ 0), ?_⟩` and prove the remaining obligations. Establish `e : (fun _ : Fin 1 => resM L' (inf_le_right : U₁ ⊓ U₂ ≤ U₂) (e₂ 0)) = fun i => resM L' inf_le_right (e₂ i)`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Rewrite using `[e]`.

Conclude with `he₂.res inf_le_right`. Establish `e₀ : c.e.symm (c.e y) = y` using `c.e.left_inv hy`. Establish `ho` using `ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)`. Establish `hm` using `ChartGlue.mem_over c.e hy hU`. Establish `hn` using `ho.mem_nhds hm`.

Establish `hG : MContDiffAt ∞ (fun x => h.gram ![l.app U t, l'.app U t'] (c.e.symm x)) (c.e y)` using `(H.gram ![l.app U t, l'.app U t'] hU).mContDiffAt c hy`. Establish `dq : ContDiffAt ℝ 2 (fun x => h.form (l'.app U t') (l.app U t) (c.e.symm x)) (c.e y)` using `(hG 1 0).of_le (by norm_cast)`. Establish `da₀ : ContDiffAt ℝ 2 (fun x => h.form (l.app U t) (l.app U t) (c.e.symm x)) (c.e y)` using `(hG 0 0).of_le (by norm_cast)`. Establish `da₁ : ContDiffAt ℝ 2 (fun x => h.form (l'.app U t') (l'.app U t') (c.e.symm x)) (c.e y)` using `(hG 1 1).of_le (by norm_cast)`. Establish `da : ContDiffAt ℝ 2 (fun x => (h.form (l.app U t) (l.app U t) (c.e.symm x)).re) (c.e y)` using `Complex.reCLM.contDiff.contDiffAt.comp _ da₀`.

Establish `da' : ContDiffAt ℝ 2 (fun x => (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re) (c.e y)` using `Complex.reCLM.contDiff.contDiffAt.comp _ da₁`. Establish `pa : 0 < (h.form (l.app U t) (l.app U t) y).re`. Use `form_frame_re_pos (h.restrict hl hL) ht hU` as an intermediate fact. Rewrite `this` using `[h.form_restrict hl hL _ _ hU]`. Then use the resulting hypothesis. Establish `pa' : 0 < (h.form (l'.app U t') (l'.app U t') y).re`.

Use `form_frame_re_pos (h.restrict hl' hL') ht' hU` as an intermediate fact. Rewrite `this` using `[h.form_restrict hl' hL' _ _ hU]`. Then use the resulting hypothesis. Establish `hdb : dbar (fun x => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c (c.e.symm x)) (c.e y) (EuclideanSpace.single 0 1) = (((-(1 / Real.pi) : ℝ)) : ℂ) * dbar (angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re) (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re …`. Establish `e₁` using `dbar_const_smul (((-(1 / Real.pi) : ℝ)) : ℂ) ((hm₁ c y hy).differentiableAt (by norm_num))`. Establish `e₂` using `dbar_congr (z := c.e y) (f := fun v => m₀ c (c.e.symm v)) (g := angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re) (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re) (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single …`.

Use `hm₃ U t t' ht ht' c (c.e.symm x) (c.e.map_target hx.1) hx.2` as an intermediate fact. Rewrite using `[c.e.right_inv hx.1] at this)` and apply the resulting hypothesis. Simplify using `only [smul_eq_mul] at e₁`. Rewrite using `[e₁, e₂]`. Both sides reduce to the same expression.

Establish `hcalc` using `GlobalTheory.T.dbar_angleForm_re_eq _ n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re) (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re) (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y) da da' dq (by simpa onl …`. Establish `hX` using `GlobalTheory.T.norm_dbar_quotient_form_bound k X p σ (ShortComplex.mk l m w) h hS hL hQ H U t (l'.app U t') ht c y hy hU`. Establish `hY` using `GlobalTheory.T.norm_dbar_quotient_form_bound k X p σ (ShortComplex.mk l' m' w') h hS' hL' hQ' H U t' (l.app U t) ht' c y hy hU`. Establish `hY' : ‖del (fun x => h.form (l'.app U t') (l.app U t) (c.e.symm x)) (c.e y) (EuclideanSpace.single 0 1) - h.form (l'.app U t') (l.app U t) y * del (fun x => (Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re : ℂ)) (c.e y) (EuclideanSpace.single 0 1)‖ ^ 2 = ((h.form (l …`. Establish `e₁ : (fun x => h.form (l.app U t) (l'.app U t') (c.e.symm x)) = fun x => (starRingEnd ℂ) (h.form (l'.app U t') (l.app U t) (c.e.symm x))`.

Use function extensionality and compare the values at `x`. Rewrite using `[h.conj_form]`. Establish `e₂ : h.form (l.app U t) (l'.app U t') y = (starRingEnd ℂ) (h.form (l'.app U t') (l.app U t) y)` using `by rw [h.conj_form]`. Establish `hY2 : ‖dbar (fun x => h.form (l.app U t) (l'.app U t') (c.e.symm x)) (c.e y) (EuclideanSpace.single 0 1) - h.form (l.app U t) (l'.app U t') y * dbar (fun x => (Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re : ℂ)) (c.e y) (EuclideanSpace.single 0 1)‖ ^ 2 = ((h.form …` using `hY`. Rewrite `hY2` using `[e₁, e₂, dbar_conj, dbar_ofReal, ← map_mul, ← map_sub, Complex.norm_conj, Complex.norm_conj]`.

Conclude with `hY2`. Establish `c₁` using `(chernDens_curve k X p σ).2 L (h.restrict hl hL) (H.restrict hl hL) U t ht c y hy hU`. Establish `c₂` using `(chernDens_curve k X p σ).2 L' (h.restrict hl' hL') (H.restrict hl' hL') U t' ht' c y hy hU`. Establish `l₁ : leviForm (fun x => Real.log ((h.restrict hl hL).form t t (c.e.symm x)).re) (c.e y) = leviForm (fun x => Real.log (h.form (l.app U t) (l.app U t) (c.e.symm x)).re) (c.e y)` using `leviForm_congr_germ (by filter_upwards [hn] with x hx`. Rewrite using `[h.form_restrict hl hL _ _ hx.2])`.

Establish `l₂ : leviForm (fun x => Real.log ((h.restrict hl' hL').form t' t' (c.e.symm x)).re) (c.e y) = leviForm (fun x => Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re) (c.e y)` using `leviForm_congr_germ (by filter_upwards [hn] with x hx`. Rewrite using `[h.form_restrict hl' hL' _ _ hx.2])`. Rewrite `c₁` using `[l₁]`. Rewrite `c₂` using `[l₂]`. Simplify using `only [e₀] at hcalc`.

Rewrite using `[hdb, Complex.re_ofReal_mul, hcalc]`. Conclude with `green_algebra Real.pi _ _ (v y) _ _ _ _ _ _ _ _ _ n Real.pi_ne_zero pa pa' (hv U t t' y hU) hX hY' c₁ c₂`.
-/
theorem green_density {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {V L Q L' Q' : X.Modules} {l : L ⟶ V} {m : V ⟶ Q} {w : l ≫ m = 0} {l' : L' ⟶ V} {m' : V ⟶ Q'}
    {w' : l' ≫ m' = 0} (hS : (ShortComplex.mk l m w).ShortExact)
    (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1)
    (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l')
    (h : Met p σ V (1 + 1)) (H : h.IsCInf) {v : CxPts p σ → ℝ} (hv : IsCosSq h l l' v) (n : ℕ)
    {m₀ : AlgChart p σ 1 → CxPts p σ → ℂ}
    (hm₁ : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source,
      ContDiffAt ℝ 1 (fun v => m₀ c (c.e.symm v)) (c.e y))
    (hm₃ : ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), IsFrame (fun _ : Fin 1 => t) →
      IsFrame (fun _ : Fin 1 => t') → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U →
      m₀ c y = angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
        (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
        (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y))
    (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    v y ^ (n + 1) * (c.chernDens (h.restrict hl hL).detWeight y -
        c.chernDens (h.restrict hl' hL').detWeight y) +
      (n + 1) * v y ^ n * (1 - v y) * (Met.bcDens (S := ShortComplex.mk l m w) h hS hL hQ c y -
        Met.bcDens (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y) =
    (dbar (fun x => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c (c.e.symm x)) (c.e y)
      (EuclideanSpace.single 0 1)).re := by
  obtain ⟨U₁, e₁, hx₁, he₁⟩ := hL (y.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨U₂, e₂, hx₂, he₂⟩ := hL' (y.1 (IsLocalRing.closedPoint ℂ))
  have hU : y ∈ ptsIn p σ (U₁ ⊓ U₂) := mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hx₁, mem_ptsIn.2 hx₂⟩
  obtain ⟨U, hUdef⟩ : ∃ U, U = U₁ ⊓ U₂ := ⟨_, rfl⟩
  rw [← hUdef] at hU
  obtain ⟨t, ht⟩ : ∃ t : Γ(L, U), IsFrame (fun _ : Fin 1 => t) := by
    subst hUdef
    refine ⟨resM L inf_le_left (e₁ 0), ?_⟩
    have e : (fun _ : Fin 1 => resM L (inf_le_left : U₁ ⊓ U₂ ≤ U₁) (e₁ 0)) =
        fun i => resM L inf_le_left (e₁ i) := by
      funext i; rw [Subsingleton.elim i 0]
    rw [e]
    exact he₁.res inf_le_left
  obtain ⟨t', ht'⟩ : ∃ t' : Γ(L', U), IsFrame (fun _ : Fin 1 => t') := by
    subst hUdef
    refine ⟨resM L' inf_le_right (e₂ 0), ?_⟩
    have e : (fun _ : Fin 1 => resM L' (inf_le_right : U₁ ⊓ U₂ ≤ U₂) (e₂ 0)) =
        fun i => resM L' inf_le_right (e₂ i) := by
      funext i; rw [Subsingleton.elim i 0]
    rw [e]
    exact he₂.res inf_le_right
  have e₀ : c.e.symm (c.e y) = y := c.e.left_inv hy
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
  have hm := ChartGlue.mem_over c.e hy hU
  have hn := ho.mem_nhds hm

  have hG : MContDiffAt ∞ (fun x => h.gram ![l.app U t, l'.app U t'] (c.e.symm x)) (c.e y) :=
    (H.gram ![l.app U t, l'.app U t'] hU).mContDiffAt c hy
  have dq : ContDiffAt ℝ 2 (fun x => h.form (l'.app U t') (l.app U t) (c.e.symm x)) (c.e y) :=
    (hG 1 0).of_le (by norm_cast)
  have da₀ : ContDiffAt ℝ 2 (fun x => h.form (l.app U t) (l.app U t) (c.e.symm x)) (c.e y) :=
    (hG 0 0).of_le (by norm_cast)
  have da₁ : ContDiffAt ℝ 2 (fun x => h.form (l'.app U t') (l'.app U t') (c.e.symm x)) (c.e y) :=
    (hG 1 1).of_le (by norm_cast)
  have da : ContDiffAt ℝ 2 (fun x => (h.form (l.app U t) (l.app U t) (c.e.symm x)).re) (c.e y) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ da₀
  have da' : ContDiffAt ℝ 2 (fun x => (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re) (c.e y) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ da₁

  have pa : 0 < (h.form (l.app U t) (l.app U t) y).re := by
    have := form_frame_re_pos (h.restrict hl hL) ht hU
    rwa [h.form_restrict hl hL _ _ hU] at this
  have pa' : 0 < (h.form (l'.app U t') (l'.app U t') y).re := by
    have := form_frame_re_pos (h.restrict hl' hL') ht' hU
    rwa [h.form_restrict hl' hL' _ _ hU] at this

  have hdb : dbar (fun x => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c (c.e.symm x)) (c.e y)
      (EuclideanSpace.single 0 1) = (((-(1 / Real.pi) : ℝ)) : ℂ) *
        dbar (angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
          (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
          (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1))
          (c.e y) (EuclideanSpace.single 0 1) := by
    have e₁ := dbar_const_smul (((-(1 / Real.pi) : ℝ)) : ℂ)
      ((hm₁ c y hy).differentiableAt (by norm_num))
    have e₂ := dbar_congr (z := c.e y) (f := fun v => m₀ c (c.e.symm v))
      (g := angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
          (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
          (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1))
      (by
        filter_upwards [hn] with x hx
        have := hm₃ U t t' ht ht' c (c.e.symm x) (c.e.map_target hx.1) hx.2
        rwa [c.e.right_inv hx.1] at this)
    simp only [smul_eq_mul] at e₁
    rw [e₁, e₂]
    rfl
  have hcalc := GlobalTheory.T.dbar_angleForm_re_eq _ n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
    (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
    (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y)
    da da' dq (by simpa only [e₀] using pa) (by simpa only [e₀] using pa')

  have hX := GlobalTheory.T.norm_dbar_quotient_form_bound k X p σ (ShortComplex.mk l m w) h hS hL hQ H U t (l'.app U t') ht c y hy hU
  have hY := GlobalTheory.T.norm_dbar_quotient_form_bound k X p σ (ShortComplex.mk l' m' w') h hS' hL' hQ' H U t' (l.app U t) ht' c y hy hU
  have hY' : ‖del (fun x => h.form (l'.app U t') (l.app U t) (c.e.symm x)) (c.e y)
        (EuclideanSpace.single 0 1) - h.form (l'.app U t') (l.app U t) y *
        del (fun x => (Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re : ℂ)) (c.e y)
        (EuclideanSpace.single 0 1)‖ ^ 2 =
      ((h.form (l'.app U t') (l'.app U t') y).re * (h.form (l.app U t) (l.app U t) y).re -
        ‖h.form (l'.app U t') (l.app U t) y‖ ^ 2) * (Real.pi * h.bcDens hS' hL' hQ' c y) := by
    have e₁ : (fun x => h.form (l.app U t) (l'.app U t') (c.e.symm x)) =
        fun x => (starRingEnd ℂ) (h.form (l'.app U t') (l.app U t) (c.e.symm x)) := by
      funext x; rw [h.conj_form]
    have e₂ : h.form (l.app U t) (l'.app U t') y =
        (starRingEnd ℂ) (h.form (l'.app U t') (l.app U t) y) := by rw [h.conj_form]
    have hY2 : ‖dbar (fun x => h.form (l.app U t) (l'.app U t') (c.e.symm x)) (c.e y)
          (EuclideanSpace.single 0 1) - h.form (l.app U t) (l'.app U t') y *
          dbar (fun x => (Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re : ℂ)) (c.e y)
          (EuclideanSpace.single 0 1)‖ ^ 2 =
        ((h.form (l'.app U t') (l'.app U t') y).re * (h.form (l.app U t) (l.app U t) y).re -
          ‖h.form (l.app U t) (l'.app U t') y‖ ^ 2) * (Real.pi * h.bcDens hS' hL' hQ' c y) := hY
    rw [e₁, e₂, dbar_conj, dbar_ofReal, ← map_mul, ← map_sub, Complex.norm_conj,
      Complex.norm_conj] at hY2
    exact hY2
  have c₁ := (chernDens_curve k X p σ).2 L (h.restrict hl hL) (H.restrict hl hL) U t ht c y hy hU
  have c₂ := (chernDens_curve k X p σ).2 L' (h.restrict hl' hL') (H.restrict hl' hL') U t' ht' c y hy hU
  have l₁ : leviForm (fun x => Real.log ((h.restrict hl hL).form t t (c.e.symm x)).re) (c.e y) =
      leviForm (fun x => Real.log (h.form (l.app U t) (l.app U t) (c.e.symm x)).re) (c.e y) :=
    leviForm_congr_germ (by
      filter_upwards [hn] with x hx
      rw [h.form_restrict hl hL _ _ hx.2])
  have l₂ : leviForm (fun x => Real.log ((h.restrict hl' hL').form t' t' (c.e.symm x)).re) (c.e y) =
      leviForm (fun x => Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re) (c.e y) :=
    leviForm_congr_germ (by
      filter_upwards [hn] with x hx
      rw [h.form_restrict hl' hL' _ _ hx.2])
  rw [l₁] at c₁
  rw [l₂] at c₂
  simp only [e₀] at hcalc
  rw [hdb, Complex.re_ofReal_mul, hcalc]
  exact green_algebra Real.pi _ _ (v y) _ _ _ _ _ _ _ _ _ n Real.pi_ne_zero pa pa'
    (hv U t t' y hU) hX hY' c₁ c₂

/- English proof (translation)
Introduce `k _ X p σ _ _ _ hAn V L Q L' Q' l m w l' m' w' hS hS' hL hQ hL' hQ' hl hl' h H v hv n`. Take `⟨m₀, hm₁, hm₂, hm₃⟩` from `GlobalTheory.T.exists_C1_density_for_line_pair k X p σ V L L' (1 + 1) h l l' H hl hl' hL hL' n`. Establish `st` using `GlobalTheory.T.chartwise_C1_density_of_compatible k X p σ hAn (fun c y => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c y) (fun c y hy => contDiffAt_const.mul (hm₁ c y hy)) (fun c c' y hy hy' => by rw [hm₂ c c' y hy hy']; ring)`. Rewrite using `[← st]`. Conclude with `total_congr fun c y hy => green_density hS hS' hL hQ hL' hQ' hl hl' h H hv n hm₁ hm₃ c hy`.
-/
theorem green_cosSq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0) (hS : (ShortComplex.mk l m w).ShortExact) (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l') (h : Met p σ V (1 + 1)), h.IsCInf → ∀ v : CxPts p σ → ℝ, IsCosSq h l l' v → ∀ n : ℕ, total (fun (c : AlgChart p σ 1) y => v y ^ (n + 1) * (c.chernDens (h.restrict hl hL).detWeight y - c.chernDens (h.restrict hl' hL').detWeight y) + (n + 1) * v y ^ n * (1 - v y) * (Met.bcDens (S := ShortComplex.mk l m w) h hS hL hQ c y - Met.bcDens (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y)) = 0 := by
  intro k _ X p σ _ _ _ hAn V L Q L' Q' l m w l' m' w' hS hS' hL hQ hL' hQ' hl hl' h H v hv n
  obtain ⟨m₀, hm₁, hm₂, hm₃⟩ := GlobalTheory.T.exists_C1_density_for_line_pair k X p σ V L L' (1 + 1) h l l' H hl hl' hL hL' n
  have st := GlobalTheory.T.chartwise_C1_density_of_compatible k X p σ hAn (fun c y => (((-(1 / Real.pi) : ℝ)) : ℂ) * m₀ c y)
    (fun c y hy => contDiffAt_const.mul (hm₁ c y hy))
    (fun c c' y hy hy' => by rw [hm₂ c c' y hy hy']; ring)
  rw [← st]
  exact total_congr fun c y hy =>
    green_density hS hS' hL hQ hL' hQ' hl hl' h H hv n hm₁ hm₃ c hy

end GlobalTheory.CurveDens
