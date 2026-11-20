import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DivisionOrderOne
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemSpanCuspReadingsIffComponents

namespace GlobalTheory.Shares.VanDiv

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

/- English proof (translation)
Establish `h1` using `(IW.phla_cpt_cdAt X x0 hz F).of_le HE.two_le_inf`. Establish `h3` using `(IW.phla_cpt_cdAt X x0 hz L).of_le HE.two_le_inf`. Establish `e : (fun w => ((phla X (F + k • L) (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[nhds z] fun w => ((phla X F (cpt X x0 w) + (k : ℝ) * phla X L (cpt X x0 w) : ℝ) : ℂ)` using `by filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with w hw`. Rewrite using `[OW.phla_add_nsmul X hw]`. Unfold `leviO leviM`.

Rewrite using `[Y.fc_leviV_congr _ _ _ _ e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h3), Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3]`. Simplify using `only [Complex.add_re, Complex.re_ofReal_mul]`.
-/
theorem leviO_phla_add_nsmul (x0 : Frame X.Ψ r) (F L : Wt X.Ψ r) (k : ℕ) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (phla X (F + k • L)) z ξ = leviO X x0 (phla X F) z ξ + k * leviO X x0 (phla X L) z ξ := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz F).of_le HE.two_le_inf
  have h3 := (IW.phla_cpt_cdAt X x0 hz L).of_le HE.two_le_inf
  have e : (fun w => ((phla X (F + k • L) (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[nhds z]
      fun w => ((phla X F (cpt X x0 w) + (k : ℝ) * phla X L (cpt X x0 w) : ℝ) : ℂ) := by
    filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with w hw
    rw [OW.phla_add_nsmul X hw]
  unfold leviO leviM
  rw [Y.fc_leviV_congr _ _ _ _ e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h3),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3]
  simp only [Complex.add_re, Complex.re_ofReal_mul]

/- English proof (translation)
Rewrite using `[OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.phla_add_nsmul X hx, neg_add, Real.exp_add, ← mul_neg, Real.exp_nat_mul, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pnorm_mul_pow_sq (F L : Wt X.Ψ r) (m : ℕ) (g w : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm (F + m • L) (fun x => g x * w x ^ m) x ^ 2 = X.pnorm F g x ^ 2 * (X.pnorm L w x ^ 2) ^ m := by
  rw [OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.phla_add_nsmul X hx, neg_add,
    Real.exp_add, ← mul_neg, Real.exp_nat_mul, map_mul, map_pow]
  ring

/- English proof (translation)
Take `⟨-, ⟨bb, m, hbb, hbm, hmar⟩, hL, -, hcusp⟩` from `hm`. Establish `e : ∀ a : ℕ, Xa.Fp + k • Xa.L + a • Xa.L = Xa.Fp + (k + a) • Xa.L` using `fun a => by`. Rewrite using `[add_nsmul, add_assoc]`. Take `⟨C, hC⟩` from `hg.2`. Establish `hC2 : ∀ x ∈ X.dom, X.pnorm (Xa.Fp + k • Xa.L) g x ^ 2 ≤ C ^ 2` using `fun x hx => pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hC x hx) 2`.

Take `⟨B, hB⟩` from `Fl.weightForm_vanishes.1.1.2`. Take `⟨K, hK⟩` from `Fl.denom_le_family`. Take `⟨h, hh, hs⟩` from `GlobalTheory.DivFreeWeight.division_order_one E r X Xa Fl (Xa.Fp + k • Xa.L) ⟨bb, m, hbb, hbm, fun x0 ho z hz ξ => by`. Establish `h1` using `hmar x0 ho z hz ξ`. Establish `h2` using `mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (hL x0 ho z hz ξ)`.

Rewrite using `[leviO_phla_add_nsmul x0 _ _ k hz]`. Use the proof step `linarith⟩`. Use the proof step `(by rw [e]; exact hcusp _) (by rw [e]; exact hfin)`. Use the proof step `(fun x => g x * Fl.w0 x ^ (nd X + 1))`. Use the proof step `⟨GlobalTheory.Up.DivCorePf.isSec_mul hg.1 (GlobalTheory.Up.DivCorePf.isSec_pow Fl.weightForm_vanishes.1.1.1 _), √(C ^ 2 * (B ^ 2) ^ (nd X + 1)), fun x hx => by`.

Use `Real.le_sqrt_of_sq_le ?_` and prove the remaining obligations. Rewrite using `[pnorm_mul_pow_sq _ _ _ _ _ hx]`. Conclude with `mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hB x hx) 2) _) (by positivity) (by positivity)⟩`. Use the proof step `⟨C ^ 2 * |K| ^ (nd X + 1), fun x hx => by`. Rewrite using `[pnorm_mul_pow_sq _ _ _ _ _ hx, mul_assoc, ← mul_pow]`.

Use `mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _) ((hK x hx).trans ?_) _) (by positivity) (by positivity)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)⟩`. Use the proof step `(fun j => by simp [hv j])`. Conclude with `⟨h, fun i => hcusp _ _ (e _ ▸ hh i), hs⟩`.
-/
theorem model_division (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa) (k : ℕ)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + (k + (nd X + 1)) • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    (g : Frame X.Ψ r → ℂ) (hg : X.IsBddSec (Xa.Fp + k • Xa.L) g) (hv : ∀ j, g (Fl.xs j) = 0) :
    ∃ h : Fin (nd X) → Frame X.Ψ r → ℂ, (∀ i, h i ∈ X.SS (Xa.Fp + (k + nd X) • Xa.L)) ∧
      ∀ x ∈ X.dom, g x * Fl.w0 x ^ (nd X + 1) = ∑ i, Fl.s i x * h i x := by
  obtain ⟨-, ⟨bb, m, hbb, hbm, hmar⟩, hL, -, hcusp⟩ := hm
  have e : ∀ a : ℕ, Xa.Fp + k • Xa.L + a • Xa.L = Xa.Fp + (k + a) • Xa.L := fun a => by
    rw [add_nsmul, add_assoc]
  obtain ⟨C, hC⟩ := hg.2
  have hC2 : ∀ x ∈ X.dom, X.pnorm (Xa.Fp + k • Xa.L) g x ^ 2 ≤ C ^ 2 := fun x hx =>
    pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hC x hx) 2
  obtain ⟨B, hB⟩ := Fl.weightForm_vanishes.1.1.2
  obtain ⟨K, hK⟩ := Fl.denom_le_family
  obtain ⟨h, hh, hs⟩ := GlobalTheory.DivFreeWeight.division_order_one E r X Xa Fl (Xa.Fp + k • Xa.L)
    ⟨bb, m, hbb, hbm, fun x0 ho z hz ξ => by
      have h1 := hmar x0 ho z hz ξ
      have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (hL x0 ho z hz ξ)
      rw [leviO_phla_add_nsmul x0 _ _ k hz]
      linarith⟩
    (by rw [e]; exact hcusp _) (by rw [e]; exact hfin)
    (fun x => g x * Fl.w0 x ^ (nd X + 1))
    ⟨GlobalTheory.Up.DivCorePf.isSec_mul hg.1 (GlobalTheory.Up.DivCorePf.isSec_pow Fl.weightForm_vanishes.1.1.1 _),
      √(C ^ 2 * (B ^ 2) ^ (nd X + 1)), fun x hx => by
        refine Real.le_sqrt_of_sq_le ?_
        rw [pnorm_mul_pow_sq _ _ _ _ _ hx]
        exact mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _)
          (pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hB x hx) 2) _) (by positivity) (by positivity)⟩
    ⟨C ^ 2 * |K| ^ (nd X + 1), fun x hx => by
      rw [pnorm_mul_pow_sq _ _ _ _ _ hx, mul_assoc, ← mul_pow]
      refine mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _) ((hK x hx).trans ?_) _)
        (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)⟩
    (fun j => by simp [hv j])
  exact ⟨h, fun i => hcusp _ _ (e _ ▸ hh i), hs⟩

end Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

/- English proof (translation)
Take `⟨K, b, hb⟩` from `Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j u)`. Use `⟨K, b, Submodule.span_le.2 ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨F, -, rfl⟩`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun B.KO).1 (hb ▸ Submodule.mem_top : F ∈ _)`. Simplify using `only [map_sum, map_smul, R.ev_smul]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem sp_le_span {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) : ∃ (K : ℕ) (b : Fin K → B.Cusp j u),
      R.sp u Set.univ ≤ Submodule.span ℂ (Set.range fun i => R.ev (X.inc u (b i))) := by
  obtain ⟨K, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j u)
  refine ⟨K, b, Submodule.span_le.2 ?_⟩
  rintro _ ⟨F, -, rfl⟩
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B.KO).1 (hb ▸ Submodule.mem_top : F ∈ _)
  simp only [map_sum, map_smul, R.ev_smul]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce `D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hen honto k g hg hv`. Establish `hwt : ∀ (a : ℕ) c, laR T j (addL wF wL a) c = (A.Xa c).Fp + a • (A.Xa c).L` using `fun a c => by`. Rewrite using `[(GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj c).2.2.1, A.hF, A.hL]`. Take `⟨f, hf, hgf⟩` from `(GlobalTheory.Shares.span_readings_components D T h j hj n R e hR (addL wF wL k)).1 g hg`. Establish `hfin : ∀ (a : ℕ) (c : (T.U j T.σ₀).Comp), ∃ (K : ℕ) (b : Fin K → Frame ((T.U j T.σ₀).X c).Ψ D.R.r → ℂ), ∀ f ∈ ((T.U j T.σ₀).X c).SS ((A.Xa c).Fp + a • (A.Xa c).L), ∃ cc : Fin K → ℂ, ∀ x ∈ ((T.U j T.σ₀).X c).dom, f x = ∑ i, cc i * b i x`.

Introduce `a c`. Take `⟨K, b, hb⟩` from `sp_le_span R (addL wF wL a)`. Use `⟨K, fun i => rdR h j (b i) c, fun p hp => ?_⟩` and prove the remaining obligations. Establish `h1` using `(GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto a) (Function.update (fun _ => 0) c p) (fun c' => by`. Distinguish the cases in `hc : c' = c`.

Substitute `hc` using the available equality. Rewrite using `[Function.update_self, hwt]`. Conclude with `hp`. Rewrite using `[Function.update_of_ne hc]`. Conclude with `(siegelSpaceAlgebra_holds _ _ _ 0 0).2.2.1.1.1)`.

Take `⟨cc, hcc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 (hb h1)`. Use `⟨cc, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h2` using `congrFun hcc (e.symm ⟨c, ⟨x, hx⟩⟩)`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2] at h2`. Rewrite `h2` using `[Equiv.apply_symm_apply]`.

Simplify using `using h2.symm`. Establish `hdiv` using `fun c => model_division (A.Xa c) (Fl.Fl c) (A.mar c) k (hfin _ c) (f c) (hwt k c ▸ (hf c).1.1) (fun i => by`. Establish `h1` using `hv (en.symm ⟨c, i⟩)`. Rewrite `h1` using `[hgf, hen, Equiv.apply_symm_apply]`. Conclude with `h1)`.

Use `choose H hH hsum using hdiv`. Use `⟨WeightFamilies.dimY D j, ?_⟩` and prove the remaining obligations. Establish `hs : ∀ i y, R.s w t i y = ∑ a, t (i, a) * rdR h j (w a) (e y).1 (e y).2.1` using `fun i y => by`. Simplify using `only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]`. Establish `hmem : ∀ i : Fin (WeightFamilies.dimY D j), (fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1) ∈ R.sp (addL wF wL (k + WeightFamilies.dimY D j)) Set.univ` using `fun i => (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto _) (fun c => H c (Fin.cast (A.dim c).symm i)) (fun c => by`.

Rewrite using `[hwt]`. Establish `h1` using `hH c (Fin.cast (A.dim c).symm i)`. Rewrite using `[show k + nd ((T.U j T.σ₀).X c) = k + WeightFamilies.dimY D j by rw [A.dim c]] at h1)` and apply the resulting hypothesis. Establish `heq : R.s w t 0 ^ (WeightFamilies.dimY D j + 1) * g = ∑ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) * fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1`. Establish `hmon : ∀ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) = R.s w t i.succ` using `fun i => by`.

Unfold `Rdg.mon`. Rewrite using `[Finset.prod_eq_single i (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `y`. Simplify using `only [hmon, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hs]`.

Establish `h1` using `hsum _ _ (e y).2.2`. Rewrite `h1` using `[show nd ((T.U j T.σ₀).X (e y).1) + 1 = WeightFamilies.dimY D j + 1 by rw [A.dim]]`. Rewrite using `[← Fl.h0, hgf, mul_comm, h1]`. Use `Fintype.sum_equiv (finCongr (A.dim (e y).1)) _ _ fun a => ?_` and prove the remaining obligations. Rewrite using `[Fl.hs]`.

Both sides reduce to the same expression. Rewrite using `[heq]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨Pi.single i 1, _, by simp, hmem i, rfl⟩`.
-/
theorem vanishing_division : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ k : ℕ, ∀ g ∈ R.sp (addL wF wL k) Set.univ, (∀ q, g (xs q) = 0) → ∃ m : ℕ, R.s w t 0 ^ (m + 1) * g ∈ R.deep w t (addL wF wL (k + m)) 1 := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hen honto k g hg hv
  classical
  have hwt : ∀ (a : ℕ) c, laR T j (addL wF wL a) c = (A.Xa c).Fp + a • (A.Xa c).L := fun a c => by
    rw [(GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj c).2.2.1, A.hF, A.hL]
  obtain ⟨f, hf, hgf⟩ := (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR (addL wF wL k)).1 g hg
  have hfin : ∀ (a : ℕ) (c : (T.U j T.σ₀).Comp), ∃ (K : ℕ) (b : Fin K → Frame ((T.U j T.σ₀).X c).Ψ D.R.r → ℂ),
      ∀ f ∈ ((T.U j T.σ₀).X c).SS ((A.Xa c).Fp + a • (A.Xa c).L),
      ∃ cc : Fin K → ℂ, ∀ x ∈ ((T.U j T.σ₀).X c).dom, f x = ∑ i, cc i * b i x := by
    intro a c
    obtain ⟨K, b, hb⟩ := sp_le_span R (addL wF wL a)
    refine ⟨K, fun i => rdR h j (b i) c, fun p hp => ?_⟩
    have h1 := (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto a)
      (Function.update (fun _ => 0) c p) (fun c' => by
        by_cases hc : c' = c
        · subst hc
          rw [Function.update_self, hwt]
          exact hp
        · rw [Function.update_of_ne hc]
          exact (siegelSpaceAlgebra_holds _ _ _ 0 0).2.2.1.1.1)
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hb h1)
    refine ⟨cc, fun x hx => ?_⟩
    have h2 := congrFun hcc (e.symm ⟨c, ⟨x, hx⟩⟩)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2] at h2
    rw [Equiv.apply_symm_apply] at h2
    simpa using h2.symm
  have hdiv := fun c => model_division (A.Xa c) (Fl.Fl c) (A.mar c) k (hfin _ c) (f c)
    (hwt k c ▸ (hf c).1.1) (fun i => by
      have h1 := hv (en.symm ⟨c, i⟩)
      rw [hgf, hen, Equiv.apply_symm_apply] at h1
      exact h1)
  choose H hH hsum using hdiv
  refine ⟨WeightFamilies.dimY D j, ?_⟩
  have hs : ∀ i y, R.s w t i y = ∑ a, t (i, a) * rdR h j (w a) (e y).1 (e y).2.1 := fun i y => by
    simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  have hmem : ∀ i : Fin (WeightFamilies.dimY D j),
      (fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1) ∈ R.sp (addL wF wL (k + WeightFamilies.dimY D j)) Set.univ :=
    fun i => (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto _) (fun c => H c (Fin.cast (A.dim c).symm i))
      (fun c => by
        rw [hwt]
        have h1 := hH c (Fin.cast (A.dim c).symm i)
        rwa [show k + nd ((T.U j T.σ₀).X c) = k + WeightFamilies.dimY D j by rw [A.dim c]] at h1)
  have heq : R.s w t 0 ^ (WeightFamilies.dimY D j + 1) * g =
      ∑ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) * fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1 := by
    have hmon : ∀ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) = R.s w t i.succ := fun i => by
      unfold Rdg.mon
      rw [Finset.prod_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
      simp
    funext y
    simp only [hmon, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hs]
    have h1 := hsum _ _ (e y).2.2
    rw [show nd ((T.U j T.σ₀).X (e y).1) + 1 = WeightFamilies.dimY D j + 1 by rw [A.dim]] at h1
    rw [← Fl.h0, hgf, mul_comm, h1]
    refine Fintype.sum_equiv (finCongr (A.dim (e y).1)) _ _ fun a => ?_
    rw [Fl.hs]
    rfl
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨Pi.single i 1, _, by simp, hmem i, rfl⟩

end GlobalTheory.Shares.VanDiv
