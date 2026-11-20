import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcIntegrationByPartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralOfContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLogPlusConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCompositionFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoFlagsSineSquaredIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineLimitStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm.PLStep

section General

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [evalF, fld, map_mul, Pi.mul_apply, Subalgebra.coe_mul]`.
-/
theorem evalF_mul {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  funext x
  simp only [evalF, fld, map_mul, Pi.mul_apply, Subalgebra.coe_mul]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [evalF, fld, map_neg, Pi.neg_apply, NegMemClass.coe_neg]`.
-/
theorem evalF_neg {ι : Type} (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ) :
    evalF A w (-P) = -evalF A w P := by
  funext x
  simp only [evalF, fld, map_neg, Pi.neg_apply, NegMemClass.coe_neg]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Conclude with `((Subalgebra.mem_center_iff.1 (aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ))).2) (ψ x)).symm`.
-/
theorem evalF_comm {ι : Type} (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ) (ψ : A.Fld) :
    evalF A w P * ψ = ψ * evalF A w P := by
  funext x
  exact ((Subalgebra.mem_center_iff.1 (aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ))).2) (ψ x)).symm

/- English proof (translation)
Simplify using `only [wInt, integral_div]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wInt_div_two [MeasurableSpace M] (g : M → ℝ) (α : A.Fld) :
    wInt A (fun y => g y / 2) α = wInt A g α / 2 := by
  simp only [wInt, integral_div]; ring

/- English proof (translation)
Establish `key : ∀ ε : ℤˣ, Tendsto (fun t => ∫ y, G t y ∂A.part α ε) l (𝓝 (∫ y, g y ∂A.part α ε))` using `fun ε => tendsto_integral_filter_of_dominated_convergence b (hm.mono fun t ht => ht ε) (hbd.mono fun t ht => ht ε) (hb ε) (hl ε)`. Simplify using `only [wInt]`. Conclude with `(key 1).sub (key (-1))`.
-/
theorem wInt_tendsto [MeasurableSpace M] (α : A.Fld) {G : ℝ → M → ℝ} {g b : M → ℝ} {l : Filter ℝ}
    [l.IsCountablyGenerated]
    (hm : ∀ᶠ t in l, ∀ ε : ℤˣ, AEStronglyMeasurable (G t) (A.part α ε))
    (hb : ∀ ε : ℤˣ, Integrable b (A.part α ε))
    (hbd : ∀ᶠ t in l, ∀ ε : ℤˣ, ∀ᵐ y ∂A.part α ε, ‖G t y‖ ≤ b y)
    (hl : ∀ ε : ℤˣ, ∀ᵐ y ∂A.part α ε, Tendsto (fun t => G t y) l (𝓝 (g y))) :
    Tendsto (fun t => wInt A (G t) α) l (𝓝 (wInt A g α)) := by
  have key : ∀ ε : ℤˣ, Tendsto (fun t => ∫ y, G t y ∂A.part α ε) l (𝓝 (∫ y, g y ∂A.part α ε)) := fun ε =>
    tendsto_integral_filter_of_dominated_convergence b (hm.mono fun t ht => ht ε)
      (hbd.mono fun t ht => ht ε) (hb ε) (hl ε)
  simp only [wInt]
  exact (key 1).sub (key (-1))

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `hz` using `(hpos z.pt).ne'`. Simplify using `only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, HolAtlas.fn, ← Algebra.smul_def]`. Simplify using `only [sub_mul, add_mul, smul_mul_assoc, smul_add, smul_sub, mul_add]`. Apply the tactic sequence `match_scalars <;> push_cast <;> field_simp <;> ring`.
-/
theorem alg_step (f : M → ℝ) (t : ℝ) (D α ψ : A.Fld) (hpos : ∀ y, 0 < f y + t) :
    (A.fn (fun y => 1 / (f y + t)) * D - A.fn (fun y => 1 / (f y + t) ^ 2) * (A.fn f * (D + A.fn f * α))) * ψ =
      A.fn (fun y => t / (f y + t) ^ 2) * (D + A.fn f * α) * ψ - A.fn (fun y => f y / (f y + t)) * (α * ψ) := by
  funext z
  have hz := (hpos z.pt).ne'
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, HolAtlas.fn, ← Algebra.smul_def]
  simp only [sub_mul, add_mul, smul_mul_assoc, smul_add, smul_sub, mul_add]
  match_scalars <;> push_cast <;> field_simp <;> ring

end General

/- English proof (translation)
Introduce `k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv K`. Use `haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver`. Use `haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver`. Use `haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver`. Use `haveI : BorelSpace (Sp ℂ ⟶ Y) := ⟨rfl⟩`.

Establish `hcalc` using `GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ (d + 1) (hY.atlas σ)`. Establish `hbasic` using `GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ`. Establish `hlin` using `GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous (CxPts p σ) (d + 1) (hY.atlas σ)`. Establish `hfib` using `(GlobalTheory.T.flag_bundle_chern_integral_pull_fourth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv).1`. Establish `hom` using `GlobalTheory.T.flag_bundle_hermitian_line_curvature k B Y q p d hB hY π w E h H flB fl hfl A σ`.

Take `⟨hv01, hvc, hvs⟩` from `GlobalTheory.T.flag_bundle_hermitian_line_integral k B Y q p d hB hY π w E h H flB fl hfl A σ v hv`. Establish `hloc` using `GlobalTheory.T.flag_bundle_hermitian_line_degree k B Y q p d hB hY π w E h H flB fl hfl A σ v hv`. Establish `hnull` using `GlobalTheory.T.flag_bundle_hermitian_line_height k B Y q p d hB hY π w E h H flB fl hfl A σ v hv`. Establish `hconc` using `GlobalTheory.T.flag_bundle_hermitian_line_limit k B Y q p d hB hY π w E h H flB fl hfl A σ v hv K`. Use `set At := hY.atlas σ with hAt`.

Use `set x : Fin 5 → At.Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hx`. Use `set ω := (fld At (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) with hω`. Use `set Z := evalF At x K with hZ`. Use `set α := evalF At x (X 4 - X 0) with hα`. Use `set f : CxPts p σ → ℝ := fun y => 1 - v y with hf`.

Establish `hxF : ∀ i, At.IsForm (fld At (x i))` using `fun i => (hbasic.1 _ (fam5 π w H flB fl A i)).1.1`. Establish `hxd : ∀ i, At.del (fld At (x i)) = 0` using `fun i => (hbasic.1 _ (fam5 π w H flB fl A i)).2.1`. Establish `hxdb : ∀ i, At.dbar (fld At (x i)) = 0` using `fun i => (hbasic.1 _ (fam5 π w H flB fl A i)).2.2.1`. Establish `hev` using `fun P => hcalc.2.2.2.1 (Fin 5) x P hxF`. Establish `hZF : At.IsForm Z` using `(hev K).1`.

Establish `hZd : At.del Z = 0` using `(hev K).2.1 hxd`. Establish `hZdb : At.dbar Z = 0` using `(hev K).2.2 hxdb`. Establish `hαF : At.IsForm α` using `(hev _).1`. Establish `hωF : At.IsForm ω` using `hom.1`. Establish `hops` using `fun (c : ℂ) (a b : At.Fld) (ha : At.IsForm a) (hb : At.IsForm b) => hcalc.2.1 c a b ha hb`.

Establish `hdbωF : At.IsForm (At.dbar ω)` using `(hops 0 ω ω hωF hωF).2.2.2.2.1`. Establish `hψF : At.IsForm (Z * ω)` using `(hops 0 Z ω hZF hωF).2.1`. Establish `hddcψ : At.ddc (Z * ω) = Z * At.ddc ω`. Establish `l1` using `(hcalc.2.2.1 (fun y => aeval (fun i => x i y) (K.map (algebraMap ℝ ℂ))) ω hZF hωF).2`. Establish `l2` using `(hcalc.2.2.1 (fun y => aeval (fun i => x i y) (K.map (algebraMap ℝ ℂ))) (At.dbar ω) hZF hdbωF).1`.

Express the relevant statement in the definitionally equal form `At.dbar (Z * ω) = At.dbar Z * ω + Z * At.dbar ω at l1`. Express the relevant statement in the definitionally equal form `At.del (Z * At.dbar ω) = At.del Z * At.dbar ω + Z * At.del (At.dbar ω) at l2`. Rewrite `l1` using `[hZdb, zero_mul, zero_add]`. Rewrite `l2` using `[hZd, zero_mul, zero_add]`. Use `show GlobalTheory.HermFrame.kappa • At.del (At.dbar (Z * ω)) = Z * (GlobalTheory.HermFrame.kappa • At.del (At.dbar ω))`.

Rewrite using `[l1, l2, mul_smul_comm]`. Establish `hf01 : ∀ y, 0 ≤ f y ∧ f y ≤ 1` using `fun y => ⟨by simp only [hf]; linarith [(hv01 y).2], by simp only [hf]; linarith [(hv01 y).1]⟩`. Establish `hfc : Continuous f` using `continuous_const.sub hvc`. Establish `hfs : At.SmoothOn Set.univ (fun y => (f y : ℂ))` using `fun i => ((contDiffOn_const (c := (1 : ℂ))).sub (hvs i)).congr fun z _ => by simp only [hf, Function.comp_apply]; push_cast; ring`. Establish `hfF : At.IsForm (At.fn f)` using `At.isForm_fn hfs`.

Use `set D := At.ddc (At.fn f) with hD`. Establish `hDF : At.IsForm D`. Establish `db` using `(hops 0 _ _ hfF hfF).2.2.2.2.1`. Establish `dd` using `(hops 0 _ _ db db).2.2.2.1`. Conclude with `(hops GlobalTheory.HermFrame.kappa _ _ dd dd).2.2.1`.

Establish `hρF : At.IsForm (D + At.fn f * α)` using `(hops 0 _ _ hDF (hops 0 _ _ hfF hαF).2.1).1`. Establish `hddcF : At.IsForm (At.ddc (Z * ω))`. Establish `db` using `(hops 0 _ _ hψF hψF).2.2.2.2.1`. Establish `dd` using `(hops 0 _ _ db db).2.2.2.1`. Conclude with `(hops GlobalTheory.HermFrame.kappa _ _ dd dd).2.2.1`.

Establish `hαψF : At.IsForm (α * (Z * ω))` using `(hops 0 _ _ hαF hψF).2.1`. Establish `F2 : ∀ t : ℝ, 0 < t → wInt At (fun y => Real.log (f y + t)) (At.ddc (Z * ω)) = At.integral (At.fn (fun y => t / (f y + t) ^ 2) * (D + At.fn f * α) * (Z * ω)) - wInt At (fun y => f y / (f y + t)) (α * (Z * ω))`. Introduce `t ht`. Establish `hpos : ∀ y, 0 < f y + t` using `fun y => by linarith [(hf01 y).1]`. Take `⟨c1, s1, -⟩` from `GlobalTheory.T.smooth_composition_form _ _ At f (Set.Ioi (-t)) (fun s => Real.log (s + t)) hfc hfs isOpen_Ioi (fun y => by simp only [Set.mem_Ioi]; linarith [hpos y]) (Real.contDiffOn_log.comp (contDiff_id.add contDiff_const).contDiffOn fun s hs => by`.

Simplify using `only [Set.mem_Ioi] at hs`. Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff, id]`. Use the proof step `linarith)`. Take `⟨-, -, g2F⟩` from `GlobalTheory.T.smooth_composition_form _ _ At f (Set.Ioi (-t)) (fun s => t / (s + t) ^ 2) hfc hfs isOpen_Ioi (fun y => by simp only [Set.mem_Ioi]; linarith [hpos y]) (contDiffOn_const.div ((contDiff_id.add contDiff_const).pow 2).contDiffOn fun s hs => by`. Simplify using `only [Set.mem_Ioi] at hs; show (s + t) ^ 2 ≠ 0; exact pow_ne_zero _ (by linarith : (0:ℝ) < s + t).ne')`.

Take `⟨c3, -, g3F⟩` from `GlobalTheory.T.smooth_composition_form _ _ At f (Set.Ioi (-t)) (fun s => s / (s + t)) hfc hfs isOpen_Ioi (fun y => by simp only [Set.mem_Ioi]; linarith [hpos y]) (contDiff_id.contDiffOn.div (contDiff_id.add contDiff_const).contDiffOn fun s hs => by`. Simplify using `only [Set.mem_Ioi] at hs`. Use the proof step `linarith)`. Rewrite using `[← GlobalTheory.T.weighted_integral_of_continuous _ _ At _ c1 _ hddcF, GlobalTheory.T.ddc_integration_by_parts _ _ At _ s1 _ hψF, GlobalTheory.T.ddc_log_plus_constant _ _ At f hfs (fun y => (hf01 y).1) t ht, hloc, alg_step At f t D α (Z * ω) hpos, GlobalTheory.T.integral_sub_of_i …`. Establish `hnullae : ∀ β : At.Fld, At.IsForm β → ∀ ε : ℤˣ, ∀ᵐ y ∂At.part β ε, 0 < f y`.

Introduce `β hβ ε`. Use `ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull β hβ ε))` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, hf, not_lt] at hy ⊢`. Conclude with `le_antisymm (hv01 y).2 (by linarith)`. Establish `hfin` using `hlin.1`.

Establish `F3 : Tendsto (fun t => wInt At (fun y => Real.log (f y + t)) (At.ddc (Z * ω))) (𝓝[>] 0) (𝓝 (wInt At (fun y => Real.log (f y)) (At.ddc (Z * ω))))`. Use `wInt_tendsto At _ (b := fun y => 2 * |Real.log (f y) / 2| + 1) ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with t ht ε`. Conclude with `((hfc.add continuous_const).log fun y => (by linarith [(hf01 y).1, Set.mem_Ioi.1 ht] : 0 < f y + t).ne').aestronglyMeasurable`. Introduce `ε haveI := hfin _ hddcF ε`.

Conclude with `(((hfib _ hddcF ε).abs.const_mul 2).add (integrable_const 1))`. Use `filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht ε filter_upwards [hnullae _ hddcF ε] with y hy`. Establish `h1` using `(hf01 y).2`. Establish `hlog1 : Real.log (f y + t) ≤ 1`. Use `Real.log_le_sub_one_of_pos (show 0 < f y + t by linarith [ht.1])` as an intermediate fact.

Combine the linear relations using `[ht.2]`. Establish `hlog2 : Real.log (f y) ≤ Real.log (f y + t)` using `Real.log_le_log hy (by linarith [ht.1])`. Establish `hlog3 : Real.log (f y) ≤ 0` using `Real.log_nonpos hy.le h1`. Establish `e : 2 * |Real.log (f y) / 2| = -Real.log (f y)`. Rewrite using `[abs_div, abs_two, abs_of_nonpos hlog3]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Real.norm_eq_abs, abs_le, e]`. Apply the tactic sequence `constructor <;> linarith`. Introduce `ε filter_upwards [hnullae _ hddcF ε] with y hy`. Establish `: Tendsto (fun t => f y + t) (𝓝[>] 0) (𝓝 (f y + 0))` using `((continuous_const.add continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds`.

Rewrite `this` using `[add_zero]`. Conclude with `this.log hy.ne'`. Establish `F4 : Tendsto (fun t => wInt At (fun y => f y / (f y + t)) (α * (Z * ω))) (𝓝[>] 0) (𝓝 (At.integral (α * (Z * ω))))`. Rewrite using `[← wInt_one]`. Use `wInt_tendsto At _ (b := fun _ => 1) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with t ht ε`. Conclude with `(hfc.div (hfc.add continuous_const) fun y => (by linarith [(hf01 y).1, Set.mem_Ioi.1 ht] : 0 < f y + t).ne').aestronglyMeasurable`. Introduce `ε haveI := hfin _ hαψF ε`. Conclude with `integrable_const 1`. Use `filter_upwards [self_mem_nhdsWithin] with t ht ε`.

Use `Filter.Eventually.of_forall fun y => ?_` and prove the remaining obligations. Establish `h0` using `(hf01 y).1`. Establish `ht'` using `Set.mem_Ioi.1 ht`. Rewrite using `[Real.norm_eq_abs, abs_le]`. Prove the components needed by the constructor for the conclusion.

Establish `: 0 ≤ f y / (f y + t)` using `div_nonneg h0 (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(div_le_one (by linarith)).2 (by linarith)`. Introduce `ε filter_upwards [hnullae _ hαψF ε] with y hy`. Establish `: Tendsto (fun t => f y + t) (𝓝[>] 0) (𝓝 (f y + 0))` using `((continuous_const.add continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds`.

Rewrite `this` using `[add_zero]`. Establish `h2` using `(tendsto_const_nhds (x := f y)).div this hy.ne'`. Rewrite `h2` using `[div_self hy.ne']`. Then use the resulting hypothesis. Establish `F5 : Tendsto (fun t => wInt At (fun y => Real.log (f y + t)) (At.ddc (Z * ω))) (𝓝[>] 0) (𝓝 (0 - At.integral (α * (Z * ω))))`. Use `(hconc.sub F4).congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with t ht`. Conclude with `(F2 t ht).symm`. Establish `hcoreEq : wInt At (fun y => Real.log (1 - v y)) (At.ddc (Z * ω)) = -At.integral (α * (Z * ω))` using `(tendsto_nhds_unique F3 F5).trans (zero_sub _)`. Establish `e1 : evalF At x ((X 0 - X 3) * ((X 4 - X 0) * K)) = ((-1 : ℝ) : ℂ) • At.ddc (Z * ω)`. Rewrite using `[hddcψ, hom.2, hZ, ← evalF_mul]`.

Establish `: (X 0 - X 3) * ((X 4 - X 0) * K) = -(K * ((X 4 - X 0) * (X 3 - X 0)))` using `by ring`. Rewrite using `[this, evalF_neg]`. Simplify using the standard rewrite rules. Establish `e2` using `wInt_div_two At (fun y => Real.log (1 - v y)) (At.ddc (Z * ω))`. Use `beta_reduce at e2`.

Establish `hcalcB` using `GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ d (hB.atlas σ)`. Establish `hbasicB` using `GlobalTheory.T.firstChern_form_properties k B q d hB σ`. Establish `hoY : At.IsForm (fld At (omF hY σ (h.pull π w) fl))` using `(hbasic.2.1 _ (h.pull π w) (H.pull π w) fl fl).1.1`. Establish `hoB : (hB.atlas σ).IsForm (fld (hB.atlas σ) (omF hB σ h flB))` using `(hbasicB.2.1 E h H flB flB).1.1`. Establish `hpB : At.IsForm (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)))` using `((hcalcB.2.2.2.2 (CxPts p σ) (d + 1) At _ (hbasicB.2.2 Y p (d + 1) hY π w).1).2 0 (fld (hB.atlas σ) (omF hB σ h flB)) (fld (hB.atlas σ) (omF hB σ h flB)) |>.2.2.2 hoB).1`.

Establish `hPF : At.IsForm (evalF At x ((X 4 - X 0) * K))` using `(hev _).1`. Establish `eR : At.integral (fld At (omF hY σ (h.pull π w) fl) * evalF At x ((X 4 - X 0) * K)) - At.integral (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) * evalF At x ((X 4 - X 0) * K)) = At.integral (α * (Z * ω))`. Rewrite using `[← GlobalTheory.T.integral_sub_of_isForm' At _ _ (hops 0 _ _ hoY hPF).2.1 (hops 0 _ _ hpB hPF).2.1, ← sub_mul, ← hω, ← evalF_comm, evalF_mul, ← hα, ← hZ, mul_assoc]`. Rewrite using `[eR, e1, hlin.2.2.1 _ _ _ hddcF, e2, hcoreEq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pl_step : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ,
      wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 0 - X 3) * ((X 4 - X 0) * K))) =
        1 / 2 * ((hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * K)) - (hY.atlas σ).integral (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * K))) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv K
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  haveI : BorelSpace (Sp ℂ ⟶ Y) := ⟨rfl⟩
  have hcalc := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ (d + 1) (hY.atlas σ)
  have hbasic := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  have hlin := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous (CxPts p σ) (d + 1) (hY.atlas σ)
  have hfib := (GlobalTheory.T.flag_bundle_chern_integral_pull_fourth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv).1
  have hom := GlobalTheory.T.flag_bundle_hermitian_line_curvature k B Y q p d hB hY π w E h H flB fl hfl A σ
  obtain ⟨hv01, hvc, hvs⟩ := GlobalTheory.T.flag_bundle_hermitian_line_integral k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hloc := GlobalTheory.T.flag_bundle_hermitian_line_degree k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hnull := GlobalTheory.T.flag_bundle_hermitian_line_height k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hconc := GlobalTheory.T.flag_bundle_hermitian_line_limit k B Y q p d hB hY π w E h H flB fl hfl A σ v hv K
  set At := hY.atlas σ with hAt
  set x : Fin 5 → At.Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hx
  set ω := (fld At (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) with hω
  set Z := evalF At x K with hZ
  set α := evalF At x (X 4 - X 0) with hα
  set f : CxPts p σ → ℝ := fun y => 1 - v y with hf
  have hxF : ∀ i, At.IsForm (fld At (x i)) := fun i => (hbasic.1 _ (fam5 π w H flB fl A i)).1.1
  have hxd : ∀ i, At.del (fld At (x i)) = 0 := fun i => (hbasic.1 _ (fam5 π w H flB fl A i)).2.1
  have hxdb : ∀ i, At.dbar (fld At (x i)) = 0 := fun i => (hbasic.1 _ (fam5 π w H flB fl A i)).2.2.1
  have hev := fun P => hcalc.2.2.2.1 (Fin 5) x P hxF
  have hZF : At.IsForm Z := (hev K).1
  have hZd : At.del Z = 0 := (hev K).2.1 hxd
  have hZdb : At.dbar Z = 0 := (hev K).2.2 hxdb
  have hαF : At.IsForm α := (hev _).1
  have hωF : At.IsForm ω := hom.1
  have hops := fun (c : ℂ) (a b : At.Fld) (ha : At.IsForm a) (hb : At.IsForm b) => hcalc.2.1 c a b ha hb
  have hdbωF : At.IsForm (At.dbar ω) := (hops 0 ω ω hωF hωF).2.2.2.2.1
  have hψF : At.IsForm (Z * ω) := (hops 0 Z ω hZF hωF).2.1
  have hddcψ : At.ddc (Z * ω) = Z * At.ddc ω := by
    have l1 := (hcalc.2.2.1 (fun y => aeval (fun i => x i y) (K.map (algebraMap ℝ ℂ))) ω hZF hωF).2
    have l2 := (hcalc.2.2.1 (fun y => aeval (fun i => x i y) (K.map (algebraMap ℝ ℂ))) (At.dbar ω) hZF hdbωF).1
    change At.dbar (Z * ω) = At.dbar Z * ω + Z * At.dbar ω at l1
    change At.del (Z * At.dbar ω) = At.del Z * At.dbar ω + Z * At.del (At.dbar ω) at l2
    rw [hZdb, zero_mul, zero_add] at l1
    rw [hZd, zero_mul, zero_add] at l2
    show GlobalTheory.HermFrame.kappa • At.del (At.dbar (Z * ω)) = Z * (GlobalTheory.HermFrame.kappa • At.del (At.dbar ω))
    rw [l1, l2, mul_smul_comm]
  have hf01 : ∀ y, 0 ≤ f y ∧ f y ≤ 1 := fun y => ⟨by simp only [hf]; linarith [(hv01 y).2], by simp only [hf]; linarith [(hv01 y).1]⟩
  have hfc : Continuous f := continuous_const.sub hvc
  have hfs : At.SmoothOn Set.univ (fun y => (f y : ℂ)) := fun i =>
    ((contDiffOn_const (c := (1 : ℂ))).sub (hvs i)).congr fun z _ => by simp only [hf, Function.comp_apply]; push_cast; ring
  have hfF : At.IsForm (At.fn f) := At.isForm_fn hfs
  set D := At.ddc (At.fn f) with hD
  have hDF : At.IsForm D := by
    have db := (hops 0 _ _ hfF hfF).2.2.2.2.1
    have dd := (hops 0 _ _ db db).2.2.2.1
    exact (hops GlobalTheory.HermFrame.kappa _ _ dd dd).2.2.1
  have hρF : At.IsForm (D + At.fn f * α) := (hops 0 _ _ hDF (hops 0 _ _ hfF hαF).2.1).1
  have hddcF : At.IsForm (At.ddc (Z * ω)) := by
    have db := (hops 0 _ _ hψF hψF).2.2.2.2.1
    have dd := (hops 0 _ _ db db).2.2.2.1
    exact (hops GlobalTheory.HermFrame.kappa _ _ dd dd).2.2.1
  have hαψF : At.IsForm (α * (Z * ω)) := (hops 0 _ _ hαF hψF).2.1

  have F2 : ∀ t : ℝ, 0 < t → wInt At (fun y => Real.log (f y + t)) (At.ddc (Z * ω)) =
      At.integral (At.fn (fun y => t / (f y + t) ^ 2) * (D + At.fn f * α) * (Z * ω)) -
        wInt At (fun y => f y / (f y + t)) (α * (Z * ω)) := by
    intro t ht
    have hpos : ∀ y, 0 < f y + t := fun y => by linarith [(hf01 y).1]
    obtain ⟨c1, s1, -⟩ := GlobalTheory.T.smooth_composition_form _ _ At f (Set.Ioi (-t)) (fun s => Real.log (s + t)) hfc hfs isOpen_Ioi
      (fun y => by simp only [Set.mem_Ioi]; linarith [hpos y])
      (Real.contDiffOn_log.comp (contDiff_id.add contDiff_const).contDiffOn fun s hs => by
        simp only [Set.mem_Ioi] at hs; simp only [Set.mem_compl_iff, Set.mem_singleton_iff, id]; linarith)
    obtain ⟨-, -, g2F⟩ := GlobalTheory.T.smooth_composition_form _ _ At f (Set.Ioi (-t)) (fun s => t / (s + t) ^ 2) hfc hfs isOpen_Ioi
      (fun y => by simp only [Set.mem_Ioi]; linarith [hpos y])
      (contDiffOn_const.div ((contDiff_id.add contDiff_const).pow 2).contDiffOn fun s hs => by
        simp only [Set.mem_Ioi] at hs; show (s + t) ^ 2 ≠ 0; exact pow_ne_zero _ (by linarith : (0:ℝ) < s + t).ne')
    obtain ⟨c3, -, g3F⟩ := GlobalTheory.T.smooth_composition_form _ _ At f (Set.Ioi (-t)) (fun s => s / (s + t)) hfc hfs isOpen_Ioi
      (fun y => by simp only [Set.mem_Ioi]; linarith [hpos y])
      (contDiff_id.contDiffOn.div (contDiff_id.add contDiff_const).contDiffOn fun s hs => by
        simp only [Set.mem_Ioi] at hs; linarith)
    rw [← GlobalTheory.T.weighted_integral_of_continuous _ _ At _ c1 _ hddcF, GlobalTheory.T.ddc_integration_by_parts _ _ At _ s1 _ hψF,
      GlobalTheory.T.ddc_log_plus_constant _ _ At f hfs (fun y => (hf01 y).1) t ht, hloc, alg_step At f t D α (Z * ω) hpos,
      GlobalTheory.T.integral_sub_of_isForm' At _ _ ((hops 0 _ _ (hops 0 _ _ g2F hρF).2.1 hψF).2.1) ((hops 0 _ _ g3F hαψF).2.1),
      GlobalTheory.T.weighted_integral_of_continuous _ _ At _ c3 _ hαψF]
  have hnullae : ∀ β : At.Fld, At.IsForm β → ∀ ε : ℤˣ, ∀ᵐ y ∂At.part β ε, 0 < f y := by
    intro β hβ ε
    refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull β hβ ε))
    simp only [Set.mem_setOf_eq, hf, not_lt] at hy ⊢
    exact le_antisymm (hv01 y).2 (by linarith)
  have hfin := hlin.1
  have F3 : Tendsto (fun t => wInt At (fun y => Real.log (f y + t)) (At.ddc (Z * ω))) (𝓝[>] 0)
      (𝓝 (wInt At (fun y => Real.log (f y)) (At.ddc (Z * ω)))) := by
    refine wInt_tendsto At _ (b := fun y => 2 * |Real.log (f y) / 2| + 1) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht ε
      exact ((hfc.add continuous_const).log fun y =>
        (by linarith [(hf01 y).1, Set.mem_Ioi.1 ht] : 0 < f y + t).ne').aestronglyMeasurable
    · intro ε
      haveI := hfin _ hddcF ε
      exact (((hfib _ hddcF ε).abs.const_mul 2).add (integrable_const 1))
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht ε
      filter_upwards [hnullae _ hddcF ε] with y hy
      have h1 := (hf01 y).2
      have hlog1 : Real.log (f y + t) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show 0 < f y + t by linarith [ht.1])
        linarith [ht.2]
      have hlog2 : Real.log (f y) ≤ Real.log (f y + t) := Real.log_le_log hy (by linarith [ht.1])
      have hlog3 : Real.log (f y) ≤ 0 := Real.log_nonpos hy.le h1
      have e : 2 * |Real.log (f y) / 2| = -Real.log (f y) := by
        rw [abs_div, abs_two, abs_of_nonpos hlog3]; ring
      rw [Real.norm_eq_abs, abs_le, e]
      constructor <;> linarith
    · intro ε
      filter_upwards [hnullae _ hddcF ε] with y hy
      have : Tendsto (fun t => f y + t) (𝓝[>] 0) (𝓝 (f y + 0)) :=
        ((continuous_const.add continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
      rw [add_zero] at this
      exact this.log hy.ne'
  have F4 : Tendsto (fun t => wInt At (fun y => f y / (f y + t)) (α * (Z * ω))) (𝓝[>] 0)
      (𝓝 (At.integral (α * (Z * ω)))) := by
    rw [← wInt_one]
    refine wInt_tendsto At _ (b := fun _ => 1) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht ε
      exact (hfc.div (hfc.add continuous_const) fun y =>
        (by linarith [(hf01 y).1, Set.mem_Ioi.1 ht] : 0 < f y + t).ne').aestronglyMeasurable
    · intro ε
      haveI := hfin _ hαψF ε
      exact integrable_const 1
    · filter_upwards [self_mem_nhdsWithin] with t ht ε
      refine Filter.Eventually.of_forall fun y => ?_
      have h0 := (hf01 y).1
      have ht' := Set.mem_Ioi.1 ht
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have : 0 ≤ f y / (f y + t) := div_nonneg h0 (by linarith)
        linarith
      · exact (div_le_one (by linarith)).2 (by linarith)
    · intro ε
      filter_upwards [hnullae _ hαψF ε] with y hy
      have : Tendsto (fun t => f y + t) (𝓝[>] 0) (𝓝 (f y + 0)) :=
        ((continuous_const.add continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
      rw [add_zero] at this
      have h2 := (tendsto_const_nhds (x := f y)).div this hy.ne'
      rwa [div_self hy.ne'] at h2
  have F5 : Tendsto (fun t => wInt At (fun y => Real.log (f y + t)) (At.ddc (Z * ω))) (𝓝[>] 0)
      (𝓝 (0 - At.integral (α * (Z * ω)))) := by
    refine (hconc.sub F4).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (F2 t ht).symm
  have hcoreEq : wInt At (fun y => Real.log (1 - v y)) (At.ddc (Z * ω)) = -At.integral (α * (Z * ω)) :=
    (tendsto_nhds_unique F3 F5).trans (zero_sub _)
  have e1 : evalF At x ((X 0 - X 3) * ((X 4 - X 0) * K)) = ((-1 : ℝ) : ℂ) • At.ddc (Z * ω) := by
    rw [hddcψ, hom.2, hZ, ← evalF_mul]
    have : (X 0 - X 3) * ((X 4 - X 0) * K) = -(K * ((X 4 - X 0) * (X 3 - X 0))) := by ring
    rw [this, evalF_neg]
    simp
  have e2 := wInt_div_two At (fun y => Real.log (1 - v y)) (At.ddc (Z * ω))
  beta_reduce at e2
  have hcalcB := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ d (hB.atlas σ)
  have hbasicB := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  have hoY : At.IsForm (fld At (omF hY σ (h.pull π w) fl)) := (hbasic.2.1 _ (h.pull π w) (H.pull π w) fl fl).1.1
  have hoB : (hB.atlas σ).IsForm (fld (hB.atlas σ) (omF hB σ h flB)) := (hbasicB.2.1 E h H flB flB).1.1
  have hpB : At.IsForm (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) :=
    ((hcalcB.2.2.2.2 (CxPts p σ) (d + 1) At _ (hbasicB.2.2 Y p (d + 1) hY π w).1).2 0 (fld (hB.atlas σ) (omF hB σ h flB)) (fld (hB.atlas σ) (omF hB σ h flB)) |>.2.2.2 hoB).1
  have hPF : At.IsForm (evalF At x ((X 4 - X 0) * K)) := (hev _).1
  have eR : At.integral (fld At (omF hY σ (h.pull π w) fl) * evalF At x ((X 4 - X 0) * K)) -
      At.integral (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) * evalF At x ((X 4 - X 0) * K)) =
      At.integral (α * (Z * ω)) := by
    rw [← GlobalTheory.T.integral_sub_of_isForm' At _ _ (hops 0 _ _ hoY hPF).2.1 (hops 0 _ _ hpB hPF).2.1, ← sub_mul, ← hω,
      ← evalF_comm, evalF_mul, ← hα, ← hZ, mul_assoc]
  rw [eR, e1, hlin.2.2.1 _ _ _ hddcF, e2, hcoreEq]
  ring

end GlobalTheory.LineForm.PLStep
