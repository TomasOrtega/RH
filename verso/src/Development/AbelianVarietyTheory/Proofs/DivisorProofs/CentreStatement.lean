import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExtensionOfPhaseFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantLineChernFormFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPotentialPositiveOnComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Filter Topology ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.CentFlat

/- English proof (translation)
Substitute `he` using the available equality. Establish `hcov : ∀ y : Pts Y (I.ε a), ∃ j, y ∈ ((I.alg a j).choose).e.source`. Introduce `y`. Take `⟨j, hj⟩` from `(M.A a).cover ((I.pt a).symm y)`. Use `⟨j, ?_⟩` and prove the remaining obligations.

Rewrite `hj` using `[(I.alg a j).choose_spec]`. Simplify `hj` using `[Homeomorph.transOpenPartialHomeomorph_source]`. Set `R : AnRead Y.str (I.ε a) Y.dim` to `⟨Fin (M.A a).n, fun j => (I.alg a j).choose, hcov⟩`. Use `(AnRead.smoothOn_iff R (Y.an (I.ε a)) isOpen_univ).1 fun j => ?_` and prove the remaining obligations. Establish `h1` using `hG j`.

Rewrite `h1` using `[(I.alg a j).choose_spec]`. Use `((I.alg a j).choose.contDiffOn_finChart_iff _ Set.univ _).1 ?_` and prove the remaining obligations. Simplify `h1` using `[Function.comp_def, Homeomorph.transOpenPartialHomeomorph_symm_apply, Homeomorph.transOpenPartialHomeomorph_target]`.
-/
theorem smoothOn_of_man {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)
    (he : Y.dim = e) (a : Fin (M.n + 1)) {G : M.X a → ℝ} (hG : (M.A a).Smooth G) :
    (Y.an (I.ε a)).SmoothOn Set.univ (fun y => G ((I.pt a).symm y)) := by
  subst he
  have hcov : ∀ y : Pts Y (I.ε a), ∃ j, y ∈ ((I.alg a j).choose).e.source := by
    intro y
    obtain ⟨j, hj⟩ := (M.A a).cover ((I.pt a).symm y)
    refine ⟨j, ?_⟩
    rw [(I.alg a j).choose_spec] at hj
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using hj
  let R : AnRead Y.str (I.ε a) Y.dim := ⟨Fin (M.A a).n, fun j => (I.alg a j).choose, hcov⟩
  refine (AnRead.smoothOn_iff R (Y.an (I.ε a)) isOpen_univ).1 fun j => ?_
  have h1 := hG j
  rw [(I.alg a j).choose_spec] at h1
  refine ((I.alg a j).choose.contDiffOn_finChart_iff _ Set.univ _).1 ?_
  simpa [Function.comp_def, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Homeomorph.transOpenPartialHomeomorph_target] using h1

/- English proof (translation)
Use `interior_eq_empty_iff_dense_compl.1 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨x, hx⟩` from `Set.nonempty_iff_ne_empty.2 hne`. Take `⟨j, hj⟩` from `A.cover x`. Establish `hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' interior Z)` using `(A.chart j).isOpen_inter_preimage_symm isOpen_interior`.

Establish `hxV : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' interior Z`. Use `⟨(A.chart j).map_source hj, ?_⟩` and prove the remaining obligations. Use `show (A.chart j).symm (A.chart j x) ∈ interior Z`. Rewrite using `[(A.chart j).left_inv hj]`. Conclude with `hx`.

Establish `hpos` using `hV.measure_pos MeasureTheory.volume ⟨_, hxV⟩`. Conclude with `hpos.ne' (MeasureTheory.measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono interior_subset)) (h.2.1 j))`.
-/
theorem dense_compl_of_isBd {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {Z : Set X} {r : X → ℝ} {Om : LocPot X} (h : IsBd A Z r Om) : Dense Zᶜ := by
  refine interior_eq_empty_iff_dense_compl.1 ?_
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨j, hj⟩ := A.cover x
  have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' interior Z) :=
    (A.chart j).isOpen_inter_preimage_symm isOpen_interior
  have hxV : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' interior Z := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm (A.chart j x) ∈ interior Z
    rw [(A.chart j).left_inv hj]
    exact hx
  have hpos := hV.measure_pos MeasureTheory.volume ⟨_, hxV⟩
  exact hpos.ne' (MeasureTheory.measure_mono_null
    (Set.inter_subset_inter_right _ (Set.preimage_mono interior_subset)) (h.2.1 j))

/- English proof (translation)
Establish `hsm` using `smoothOn_of_man I he a hG`. Substitute `he` using the available equality. Take `⟨j, hj⟩` from `(M.A a).cover ((I.pt a).symm y)`. Take `⟨cj, hcj⟩` from `I.alg a j`. Establish `hyj : y ∈ cj.e.source`.

Rewrite `hj` using `[hcj]`. Simplify `hj` using `[Homeomorph.transOpenPartialHomeomorph_source]`. Take `⟨Q, hQ, hlev⟩` from `hP a`. Establish `hv : (M.A a).chart j ((I.pt a).symm y) ∈ ((M.A a).chart j).target` using `((M.A a).chart j).map_source hj`. Establish `hvz : ((M.A a).chart j).symm ((M.A a).chart j ((I.pt a).symm y)) = (I.pt a).symm y` using `((M.A a).chart j).left_inv hj`.

Establish `hvc : (M.A a).chart j ((I.pt a).symm y) = cj.finChart y`. Rewrite using `[hcj]`. Simplify using the standard rewrite rules. Use `set w := c.dtrans cj y ξ with hw`. Establish `e0` using `h0 j _ hv w`.

Rewrite `e0` using `[GlobalTheory.ShellMass.leviAt_add_ofFun hPp j hv (GlobalTheory.ShellMass.smoothOn_contDiffAt isOpen_univ hG j hv trivial), hlev j _ hv w]`. Establish `hz0 : leviAt (M.A a) (LocPot.ofFun fun _ : M.X a => (0 : ℝ)) j ((M.A a).chart j ((I.pt a).symm y)) w = 0`. Simplify using `only [leviAt, LocPot.ofFun]`. Use `show levi (fun _ => (0 : ℝ)) _ w = 0`. Simplify using `[levi]`.

Rewrite `e0` using `[hz0]`. Establish `eQ : ∀ i, leviAt (M.A a) (Q i) j ((M.A a).chart j ((I.pt a).symm y)) w = Real.pi / 2 * curvMet (m i (I.ε a)) cj y w`. Introduce `i`. Rewrite using `[← GlobalTheory.ShellMass.levi_base (hQ i).2 ((I.pt a).symm y) j hv (by rw [hvz]; exact (Q i).mem_U _) w]`. Establish `key` using `GlobalTheory.AmplePos.levi_isPot_eq_curvMet (hm i) (I.pt a) (hQ i).1 cj ((I.pt a).symm y) (by simpa using hyj) w`.

Simplify using `only [Homeomorph.apply_symm_apply] at key`. Rewrite using `[hvc, ← key, hcj]`. Establish `hG' : ContDiffAt ℝ 2 ((fun z => G ((I.pt a).symm z)) ∘ cj.e.symm) (cj.e y)` using `hsm.contDiffAt_two isOpen_univ hyj trivial`. Establish `eG : levi (G ∘ ((M.A a).chart j).symm) ((M.A a).chart j ((I.pt a).symm y)) w = cj.levi (fun z => G ((I.pt a).symm z)) y w`. Rewrite using `[hvc, AlgChart.levi, cj.leviV_re_eq hG' w, hcj]`.

Use `congr 1`. Simplify using `only [eQ, eG] at e0`. Establish `eC : ∀ i, curvMet (m i (I.ε a)) c y ξ = curvMet (m i (I.ε a)) cj y w`. Introduce `i`. Establish `hs : ContDiffAt ℝ 2 ((m i (I.ε a)).wt (Var.eqn (Δ i) y) ∘ cj.e.symm) (cj.e y)` using `(((hm i).2 (Var.eqn (Δ i) y)).mono fun _ hz => ⟨trivial, hz⟩).contDiffAt_two (Var.isOpen_eqnSet (Δ i) _) hyj (Var.mem_eqnSet (Δ i) y)`.

Simplify using `only [curvMet, ddcForm]`. Rewrite using `[AlgChart.levi_trans hy hyj hs ξ]`. Establish `eL : c.levi (fun z => G ((I.pt a).symm z)) y ξ = cj.levi (fun z => G ((I.pt a).symm z)) y w` using `AlgChart.levi_trans hy hyj hG' ξ`. Simplify using `only [eC, eL]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem curv_levi_eq_zero {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)
    (he : Y.dim = e) (a : Fin (M.n + 1)) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv}
    (m : ∀ i σ, (cxSt F).Met Y σ (Δ i)) (hm : ∀ i, Y.mSmooth (I.ε a) (Δ i) (m i (I.ε a)))
    (t : ι → ℝ) {P : M.Pot} (hP : I.FormOf m t P) (hPp : ReciprocityTheory.AnForm.M.IsPotential (M.A a) (P a))
    {G : M.X a → ℝ} (hG : (M.A a).Smooth G)
    (h0 : LeviEq (M.A a) (P a + LocPot.ofFun G) (LocPot.ofFun fun _ => 0))
    (c : AlgChart Y.str (I.ε a) Y.dim) (y : Pts Y (I.ε a)) (hy : y ∈ c.e.source) (ξ : Fin Y.dim → ℂ) :
    ∑ i, t i * (Real.pi / 2 * curvMet (m i (I.ε a)) c y ξ) + c.levi (fun z => G ((I.pt a).symm z)) y ξ = 0 := by
  have hsm := smoothOn_of_man I he a hG
  subst he
  obtain ⟨j, hj⟩ := (M.A a).cover ((I.pt a).symm y)
  obtain ⟨cj, hcj⟩ := I.alg a j
  have hyj : y ∈ cj.e.source := by
    rw [hcj] at hj
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using hj
  obtain ⟨Q, hQ, hlev⟩ := hP a
  have hv : (M.A a).chart j ((I.pt a).symm y) ∈ ((M.A a).chart j).target := ((M.A a).chart j).map_source hj
  have hvz : ((M.A a).chart j).symm ((M.A a).chart j ((I.pt a).symm y)) = (I.pt a).symm y :=
    ((M.A a).chart j).left_inv hj
  have hvc : (M.A a).chart j ((I.pt a).symm y) = cj.finChart y := by
    rw [hcj]
    simp
  set w := c.dtrans cj y ξ with hw
  have e0 := h0 j _ hv w
  rw [GlobalTheory.ShellMass.leviAt_add_ofFun hPp j hv (GlobalTheory.ShellMass.smoothOn_contDiffAt isOpen_univ hG j hv trivial),
    hlev j _ hv w] at e0
  have hz0 : leviAt (M.A a) (LocPot.ofFun fun _ : M.X a => (0 : ℝ)) j ((M.A a).chart j ((I.pt a).symm y)) w = 0 := by
    simp only [leviAt, LocPot.ofFun]
    show levi (fun _ => (0 : ℝ)) _ w = 0
    simp [levi]
  rw [hz0] at e0
  have eQ : ∀ i, leviAt (M.A a) (Q i) j ((M.A a).chart j ((I.pt a).symm y)) w =
      Real.pi / 2 * curvMet (m i (I.ε a)) cj y w := by
    intro i
    rw [← GlobalTheory.ShellMass.levi_base (hQ i).2 ((I.pt a).symm y) j hv (by rw [hvz]; exact (Q i).mem_U _) w]
    have key := GlobalTheory.AmplePos.levi_isPot_eq_curvMet (hm i) (I.pt a) (hQ i).1 cj ((I.pt a).symm y)
      (by simpa using hyj) w
    simp only [Homeomorph.apply_symm_apply] at key
    rw [hvc, ← key, hcj]
  have hG' : ContDiffAt ℝ 2 ((fun z => G ((I.pt a).symm z)) ∘ cj.e.symm) (cj.e y) :=
    hsm.contDiffAt_two isOpen_univ hyj trivial
  have eG : levi (G ∘ ((M.A a).chart j).symm) ((M.A a).chart j ((I.pt a).symm y)) w =
      cj.levi (fun z => G ((I.pt a).symm z)) y w := by
    rw [hvc, AlgChart.levi, cj.leviV_re_eq hG' w, hcj]
    congr 1
  simp only [eQ, eG] at e0
  have eC : ∀ i, curvMet (m i (I.ε a)) c y ξ = curvMet (m i (I.ε a)) cj y w := by
    intro i
    have hs : ContDiffAt ℝ 2 ((m i (I.ε a)).wt (Var.eqn (Δ i) y) ∘ cj.e.symm) (cj.e y) :=
      (((hm i).2 (Var.eqn (Δ i) y)).mono fun _ hz => ⟨trivial, hz⟩).contDiffAt_two
        (Var.isOpen_eqnSet (Δ i) _) hyj (Var.mem_eqnSet (Δ i) y)
    simp only [curvMet, ddcForm]
    rw [AlgChart.levi_trans hy hyj hs ξ]
  have eL : c.levi (fun z => G ((I.pt a).symm z)) y ξ = cj.levi (fun z => G ((I.pt a).symm z)) y w :=
    AlgChart.levi_trans hy hyj hG' ξ
  simp only [eC, eL]
  linarith

open Classical in

/- English proof (translation)
Introduce `h2 hH D O x P hcore hN hex c σ τ i hi`. Take `⟨A, T, H, ⟨h⟩⟩` from `hex`. Establish `hO : O.Core` using `⟨x, P, hcore⟩`. Take `⟨a, rfl⟩` from `(h.man c).ε.surjective σ`. Take `⟨g, hg, hgZ⟩` from `GlobalTheory.T.smooth_extension_of_phase_function h2 hH D O hO hN A T H h τ c`.

Establish `hflat` using `GlobalTheory.T.determinant_line_chern_form_flat h2 hH D O hO hN A T H h 0 τ c g hg hgZ a`. Establish `hd : (O.var c).dim = Formalism.MainNotions.WeightThresholdDefs.dimY O.Y` using `by rw [O.dim_eq c]; rfl`. Use `set I := h.man c with hI`. Use `set eτ : D.what₂.Tau → Fin O.N → ℝ := fun σ' _ => if σ' = τ then (-1 : ℝ) else 0 with heτ`. Express the relevant statement in the definitionally equal form `∀ σ', ∀ z ∉ (T.M c).Z σ', g σ' z = (T.F c).ph eτ σ' z at hgZ`.

Express the relevant statement in the definitionally equal form `LeviEq _ ((T.K 0 c).c1 (T.L 0 c eτ + (T.K 0 c).ar g) a) _ at hflat`. Establish `hfund : ∀ (τ' : D.what₂.Tau) (k : Fin O.N), fund τ i τ' k = -eτ τ' k`. Introduce `τ' k`. Establish `hk : k ≤ i` using `Fin.le_iff_val_le_val.2 (by omega)`. Simplify using `only [fund, heτ, hk, and_true]`.

Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hchg : ∀ z, O.chg c none (fund τ i) (I.ε a) z = -O.chg c none eτ (I.ε a) z`. Introduce `z`. Simplify using `only [Setup.chg, hfund, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.

Establish `hoff : ∀ y, y ∈ offBd O.Φ c (I.ε a) ↔ (I.pt a).symm y ∉ (T.M c).Z a`. Introduce `y`. Rewrite using `[(h.an c).Z a, Homeomorph.apply_symm_apply]`. Both sides reduce to the same expression. Establish `hval : ∀ y ∈ offBd O.Φ c (I.ε a), psi O x c (I.ε a) τ i y = -2 * g a ((I.pt a).symm y)`.

Introduce `y hy`. Establish `hz` using `(hoff y).1 hy`. Establish `e1` using `(h.an c).ph eτ a _ hz`. Rewrite `e1` using `[Homeomorph.apply_symm_apply]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hgc : Continuous (g a)` using `continuousOn_univ.1 (GlobalTheory.ShellMass.smoothOn_continuousOn isOpen_univ (hg a))`. Establish `hcont : Continuous fun y => -2 * g a ((I.pt a).symm y)` using `continuous_const.mul (hgc.comp (I.pt a).symm.continuous)`. Establish `hdense : Dense (offBd O.Φ c (I.ε a))`. Establish `e : offBd O.Φ c (I.ε a) = (I.pt a).symm ⁻¹' ((T.M c).Z a)ᶜ` using `Set.ext hoff`. Rewrite using `[e]`.

Conclude with `(dense_compl_of_isBd ((T.M c).bd a)).preimage (I.pt a).symm.isOpenMap`. Establish `hext : extBd O.Φ (psi O x c (I.ε a) τ i) = fun y => -2 * g a ((I.pt a).symm y)`. Use function extensionality and compare the values at `y`. Unfold `extBd`. Use `split_ifs with hy`.

Conclude with `hval y hy`. Use `haveI : (𝓝[offBd O.Φ c (I.ε a)] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hdense.closure_eq ▸ Set.mem_univ y)`. Rewrite using `[Filter.limsup_congr (eventually_nhdsWithin_of_forall hval)]`. Conclude with `((hcont.tendsto y).mono_left nhdsWithin_le_nhds).limsup_eq`. Establish `hsm : ((O.var c).an (I.ε a)).SmoothOn Set.univ fun z => g a ((I.pt a).symm z)` using `smoothOn_of_man I hd a (hg a)`.

Rewrite using `[hext]`. Use `⟨fun j => contDiffOn_const.mul (hsm j), fun ch y hy ξ => ?_⟩` and prove the remaining obligations. Establish `hLevi : LeviEq ((T.M c).A a) ((T.F c).th eτ a + LocPot.ofFun (g a)) (LocPot.ofFun fun _ => 0)`. Introduce `j v hv w`. Establish `e1` using `hflat j v hv w`.

Establish `e2` using `((T.K 0 c).isOneCochain_add (T.L 0 c eτ) ((T.K 0 c).ar g) a) j v hv w`. Rewrite `e2` using `[GlobalTheory.ShellMass.leviAt_add ((T.K 0 c).firstChern_isPotential _ a) ((T.K 0 c).firstChern_isPotential _ a) j hv, (T.c1_L 0 c eτ a) j v hv w, ((T.K 0 c).c1_ar g hg a) j v hv w]`. Rewrite using `[GlobalTheory.ShellMass.leviAt_add_ofFun (T.th_pot c eτ a) j hv (GlobalTheory.ShellMass.smoothOn_contDiffAt isOpen_univ (hg a) j hv trivial), ← e1, e2]`. Both sides reduce to the same expression. Establish `hm0 : ∀ xx, (O.var c).mSmooth (I.ε a) _ (O.met.h0 c (I.ε a) (O.ex xx))`.

Introduce `xx`. Rewrite using `[hcore.h0_eq]`. Conclude with `(FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) (I.ε a) (x.eigMet _) Set.univ isOpen_univ (x.smoothOn_eigMet _) _).2`. Establish `hC` using `curv_levi_eq_zero I hd a (fun xx σ' => O.met.h0 c σ' (O.ex xx)) hm0 (fun xx => -eτ xx.1 xx.2) ((h.an c).th eτ) (T.th_pot c eτ a) (hg a) hLevi ch y hy ξ`. Establish `hf2` using `AlgChart.levi_const_mul (c := ch) (f := fun z => g a ((I.pt a).symm z)) (-2) (hsm.contDiffAt_two isOpen_univ hy trivial) ξ`.

Simplify using `only [thW, ddcForm]`. Rewrite using `[hf2, ← hcore.h0_eq]`. Simplify using `only [hfund]`. Establish `e3 : ∑ xx : DV.Rt D.what₂.Tau O.N, -eτ xx.1 xx.2 * (Real.pi / 2 * curvMet (O.met.h0 c (I.ε a) (O.ex xx)) ch y ξ) = Real.pi / 2 * ∑ xx : DV.Rt D.what₂.Tau O.N, -eτ xx.1 xx.2 * curvMet (O.met.h0 c (I.ε a) (O.ex xx)) ch y ξ`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Rewrite `hC` using `[e3]`. Take `⟨S, hS⟩ : ∃ S, (∑ xx : DV.Rt D.what₂.Tau O.N, -eτ xx.1 xx.2 * curvMet (O.met.h0 c (I.ε a) (O.ex xx)) ch y ξ) = S` from `⟨_, rfl⟩`. Rewrite `hC` using `[hS]`. Rewrite using `[show (∑ xx : DV.Rt D.what₂.Tau O.N, -eτ xx.1 xx.2 * curvMet (O.met.h0 c (I.ε a) (rootExp O.S xx)) ch y ξ) = S from hS]`.

Establish `hL : ch.levi (fun z => g a ((I.pt a).symm z)) y ξ = -(Real.pi / 2 * S)` using `by linarith`. Rewrite using `[hL]`. Establish `hpi : Real.pi ≠ 0` using `Real.pi_ne_zero`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem centSt : Hypotheses2 → HypothesesH → CentSt := by
  intro h2 hH D O x P hcore hN hex c σ τ i hi
  obtain ⟨A, T, H, ⟨h⟩⟩ := hex
  have hO : O.Core := ⟨x, P, hcore⟩
  obtain ⟨a, rfl⟩ := (h.man c).ε.surjective σ
  obtain ⟨g, hg, hgZ⟩ := GlobalTheory.T.smooth_extension_of_phase_function h2 hH D O hO hN A T H h τ c
  have hflat := GlobalTheory.T.determinant_line_chern_form_flat h2 hH D O hO hN A T H h 0 τ c g hg hgZ a
  have hd : (O.var c).dim = Formalism.MainNotions.WeightThresholdDefs.dimY O.Y := by rw [O.dim_eq c]; rfl
  set I := h.man c with hI
  set eτ : D.what₂.Tau → Fin O.N → ℝ := fun σ' _ => if σ' = τ then (-1 : ℝ) else 0 with heτ
  change ∀ σ', ∀ z ∉ (T.M c).Z σ', g σ' z = (T.F c).ph eτ σ' z at hgZ
  change LeviEq _ ((T.K 0 c).c1 (T.L 0 c eτ + (T.K 0 c).ar g) a) _ at hflat
  have hfund : ∀ (τ' : D.what₂.Tau) (k : Fin O.N), fund τ i τ' k = -eτ τ' k := by
    intro τ' k
    have hk : k ≤ i := Fin.le_iff_val_le_val.2 (by omega)
    simp only [fund, heτ, hk, and_true]
    split_ifs <;> norm_num
  have hchg : ∀ z, O.chg c none (fund τ i) (I.ε a) z = -O.chg c none eτ (I.ε a) z := by
    intro z
    simp only [Setup.chg, hfund, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hoff : ∀ y, y ∈ offBd O.Φ c (I.ε a) ↔ (I.pt a).symm y ∉ (T.M c).Z a := by
    intro y
    rw [(h.an c).Z a, Homeomorph.apply_symm_apply]
    rfl
  have hval : ∀ y ∈ offBd O.Φ c (I.ε a), psi O x c (I.ε a) τ i y = -2 * g a ((I.pt a).symm y) := by
    intro y hy
    have hz := (hoff y).1 hy
    have e1 := (h.an c).ph eτ a _ hz
    rw [Homeomorph.apply_symm_apply] at e1
    calc psi O x c (I.ε a) τ i y = 2 * O.chg c none (fund τ i) (I.ε a) y := (hcore.two_mul_chg c _ _ y).symm
      _ = -2 * O.chg c none eτ (I.ε a) y := by rw [hchg]; ring
      _ = -2 * g a ((I.pt a).symm y) := by rw [hgZ a _ hz]; exact congrArg _ e1.symm
  have hgc : Continuous (g a) := continuousOn_univ.1 (GlobalTheory.ShellMass.smoothOn_continuousOn isOpen_univ (hg a))
  have hcont : Continuous fun y => -2 * g a ((I.pt a).symm y) :=
    continuous_const.mul (hgc.comp (I.pt a).symm.continuous)
  have hdense : Dense (offBd O.Φ c (I.ε a)) := by
    have e : offBd O.Φ c (I.ε a) = (I.pt a).symm ⁻¹' ((T.M c).Z a)ᶜ := Set.ext hoff
    rw [e]
    exact (dense_compl_of_isBd ((T.M c).bd a)).preimage (I.pt a).symm.isOpenMap
  have hext : extBd O.Φ (psi O x c (I.ε a) τ i) = fun y => -2 * g a ((I.pt a).symm y) := by
    funext y
    unfold extBd
    split_ifs with hy
    · exact hval y hy
    · haveI : (𝓝[offBd O.Φ c (I.ε a)] y).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.1 (hdense.closure_eq ▸ Set.mem_univ y)
      rw [Filter.limsup_congr (eventually_nhdsWithin_of_forall hval)]
      exact ((hcont.tendsto y).mono_left nhdsWithin_le_nhds).limsup_eq
  have hsm : ((O.var c).an (I.ε a)).SmoothOn Set.univ fun z => g a ((I.pt a).symm z) :=
    smoothOn_of_man I hd a (hg a)
  rw [hext]
  refine ⟨fun j => contDiffOn_const.mul (hsm j), fun ch y hy ξ => ?_⟩
  have hLevi : LeviEq ((T.M c).A a) ((T.F c).th eτ a + LocPot.ofFun (g a)) (LocPot.ofFun fun _ => 0) := by
    intro j v hv w
    have e1 := hflat j v hv w
    have e2 := ((T.K 0 c).isOneCochain_add (T.L 0 c eτ) ((T.K 0 c).ar g) a) j v hv w
    rw [GlobalTheory.ShellMass.leviAt_add ((T.K 0 c).firstChern_isPotential _ a) ((T.K 0 c).firstChern_isPotential _ a) j hv,
      (T.c1_L 0 c eτ a) j v hv w, ((T.K 0 c).c1_ar g hg a) j v hv w] at e2
    rw [GlobalTheory.ShellMass.leviAt_add_ofFun (T.th_pot c eτ a) j hv
      (GlobalTheory.ShellMass.smoothOn_contDiffAt isOpen_univ (hg a) j hv trivial), ← e1, e2]
    rfl
  have hm0 : ∀ xx, (O.var c).mSmooth (I.ε a) _ (O.met.h0 c (I.ε a) (O.ex xx)) := by
    intro xx
    rw [hcore.h0_eq]
    exact (FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) (I.ε a) (x.eigMet _) Set.univ isOpen_univ
      (x.smoothOn_eigMet _) _).2
  have hC := curv_levi_eq_zero I hd a (fun xx σ' => O.met.h0 c σ' (O.ex xx)) hm0 (fun xx => -eτ xx.1 xx.2)
    ((h.an c).th eτ) (T.th_pot c eτ a) (hg a) hLevi ch y hy ξ
  have hf2 := AlgChart.levi_const_mul (c := ch) (f := fun z => g a ((I.pt a).symm z)) (-2)
    (hsm.contDiffAt_two isOpen_univ hy trivial) ξ
  simp only [thW, ddcForm]
  rw [hf2, ← hcore.h0_eq]
  simp only [hfund]
  have e3 : ∑ xx : DV.Rt D.what₂.Tau O.N, -eτ xx.1 xx.2 * (Real.pi / 2 * curvMet (O.met.h0 c (I.ε a) (O.ex xx)) ch y ξ) =
      Real.pi / 2 * ∑ xx : DV.Rt D.what₂.Tau O.N, -eτ xx.1 xx.2 * curvMet (O.met.h0 c (I.ε a) (O.ex xx)) ch y ξ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e3] at hC
  obtain ⟨S, hS⟩ : ∃ S, (∑ xx : DV.Rt D.what₂.Tau O.N, -eτ xx.1 xx.2 * curvMet (O.met.h0 c (I.ε a) (O.ex xx)) ch y ξ) = S :=
    ⟨_, rfl⟩
  rw [hS] at hC
  rw [show (∑ xx : DV.Rt D.what₂.Tau O.N, -eτ xx.1 xx.2 * curvMet (O.met.h0 c (I.ε a) (rootExp O.S xx)) ch y ξ) = S from hS]
  have hL : ch.levi (fun z => g a ((I.pt a).symm z)) y ξ = -(Real.pi / 2 * S) := by linarith
  rw [hL]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end GlobalTheory.CentFlat
