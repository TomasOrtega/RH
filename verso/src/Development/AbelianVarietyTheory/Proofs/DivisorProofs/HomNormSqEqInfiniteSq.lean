import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphismOrthogonalPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagComponentFramePointRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPnHodgeLwEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentsBijectModuliComponentsStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open CategoryTheory AlgebraicGeometry GlobalTheory.ShFam.DeKeyTrue GlobalTheory.TrueGeo GlobalTheory.ProjVar.Var GlobalTheory.CxPts GlobalTheory.Toroidal Formalism.L2.Geo

namespace GlobalTheory.CovHt.Link

/- English proof (translation)
Take `⟨k, fr⟩` from `z`. Take `⟨hd, hon⟩` from `hz`. Establish `hU : IsUnf (unf s σ)`. Establish `h1` using `s.unif.law σ hσ`. Establish `e : s.U σ = s.unif.good σ hσ` using `UnfFam.U_eq _ hσ`.

Use `show IsUnf (GlobalTheory.ThetaDictCompare.toU (s.U σ))`. Rewrite using `[e]`. Conclude with `h1`. Establish `hsec : ((unf s σ).X k).IsSec (modelWt (unf s σ) G k) (rdU (unf s σ) g k)` using `by clear hon`. Establish `key : ∀ P ∈ holSub (unf s σ).X (modelWt (unf s σ) G), ((unf s σ).X k).IsSec (modelWt (unf s σ) G k) (P k)`.

Introduce `P hP`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem P hP => exact (hP k).1.1`. Consider the case `zero => exact ⟨differentiableOn_const _, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩`. Consider the case `add P Q _ _ hP hQ`.

Conclude with `⟨hP.1.add hQ.1, fun x hx b hb => by simp only [Pi.add_apply, hP.2.1 x hx b hb, hQ.2.1 x hx b hb]; ring, fun γ hγ x hx => by simp only [Pi.add_apply, hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx]; ring⟩`. Consider the case `smul a P _ hP`. Conclude with `⟨hP.1.const_smul a, fun x hx b hb => by simp only [Pi.smul_apply, smul_eq_mul, hP.2.1 x hx b hb]; ring, fun γ hγ x hx => by simp only [Pi.smul_apply, smul_eq_mul, hP.2.2 γ hγ x hx]; ring⟩`. Conclude with `key _ hg`. Establish `hb` using `ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem ((unf s σ).X k) hd`.

Establish `hz'` using `ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom ((unf s σ).X k) hd hb`. Establish `ho` using `ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf ((unf s σ).X k) hd`. Establish `hp` using `ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul ((unf s σ).X k) _ _ hsec.2.1 fr hd _ hb`. Take `⟨t₀, ht₀⟩` from `(hU.2.2.2.1 k k ⟨fr, hd⟩ ⟨_, hz'⟩).2 ⟨1, one_mem _, _, hb, by`. Establish `: ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin N) D.host.E) fr = fr`.

Use function extensionality and compare the values at `τ`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`. Both sides reduce to the same expression. Rewrite using `[this]⟩`. Establish `hinv` using `(GlobalTheory.Frames.frBor_calculus _ _ _ _ _ _ (CAt σ) _ _ ((unf s σ).un k ⟨fr, hd⟩)).2.2.2 t₀ ht₀`.

Use `⟨⟨_, hz'⟩, fun τ => ho τ, GlobalTheory.FlatLine.liesOn_frBor hinv hon, ?_⟩` and prove the remaining obligations. Establish `hrd : rdU (unf s σ) g k (ReciprocityTheory.ChartRestriction.G.FD.rmul fr (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf ((unf s σ).X k) fr)) = Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U σ).un k ⟨_, hz'⟩))` using `dif_pos hz'`. Use `show lieFacZ S.Dw ξ G * ((unf s σ).X k).pnorm _ _ fr = _`. Rewrite using `[← hp, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ ho), hrd]`.
-/
theorem hom_norm_orthogonal_frame {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) {σ : κ.c.F →+* ℂ}
    (hσ : GoodEmb κ.c σ) {Z : Comp s.Xo κ.c} {G : WTZ D.host.E} {ξ : ℝ} {g : Rul s.Xo κ.c}
    (hg : rdU (unf s σ) g ∈ holSub (unf s σ).X (modelWt (unf s σ) G)) {z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((unf s σ).X k).Ψ N}
    (hz : z ∈ framesOn (unf s σ) Z) :
    ∃ xx : ((s.U σ).X z.1).dom, ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((s.U σ).X z.1) xx.1 ∧ LiesOn Z ((s.U σ).un z.1 xx) ∧
      homN (unf s σ) ξ G g z = lieFacZ S.Dw ξ G * ‖Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U σ).un z.1 xx))‖ := by
  obtain ⟨k, fr⟩ := z
  obtain ⟨hd, hon⟩ := hz
  have hU : IsUnf (unf s σ) := by
    have h1 := s.unif.law σ hσ
    have e : s.U σ = s.unif.good σ hσ := UnfFam.U_eq _ hσ
    show IsUnf (GlobalTheory.ThetaDictCompare.toU (s.U σ))
    rw [e]
    exact h1
  have hsec : ((unf s σ).X k).IsSec (modelWt (unf s σ) G k) (rdU (unf s σ) g k) := by
    clear hon
    have key : ∀ P ∈ holSub (unf s σ).X (modelWt (unf s σ) G), ((unf s σ).X k).IsSec (modelWt (unf s σ) G k) (P k) := by
      intro P hP
      induction hP using Submodule.span_induction with
      | mem P hP => exact (hP k).1.1
      | zero => exact ⟨differentiableOn_const _, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
      | add P Q _ _ hP hQ =>
        exact ⟨hP.1.add hQ.1, fun x hx b hb => by simp only [Pi.add_apply, hP.2.1 x hx b hb, hQ.2.1 x hx b hb]; ring,
          fun γ hγ x hx => by simp only [Pi.add_apply, hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx]; ring⟩
      | smul a P _ hP =>
        exact ⟨hP.1.const_smul a, fun x hx b hb => by simp only [Pi.smul_apply, smul_eq_mul, hP.2.1 x hx b hb]; ring,
          fun γ hγ x hx => by simp only [Pi.smul_apply, smul_eq_mul, hP.2.2 γ hγ x hx]; ring⟩
    exact key _ hg
  have hb := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem ((unf s σ).X k) hd
  have hz' := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom ((unf s σ).X k) hd hb
  have ho := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf ((unf s σ).X k) hd
  have hp := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul ((unf s σ).X k) _ _ hsec.2.1 fr hd _ hb
  obtain ⟨t₀, ht₀⟩ := (hU.2.2.2.1 k k ⟨fr, hd⟩ ⟨_, hz'⟩).2 ⟨1, one_mem _, _, hb, by
    have : ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin N) D.host.E) fr = fr := by
      funext τ
      simp only [ReciprocityTheory.ChartRestriction.G.FD.lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
      rfl
    rw [this]⟩
  have hinv := (GlobalTheory.Frames.frBor_calculus _ _ _ _ _ _ (CAt σ) _ _ ((unf s σ).un k ⟨fr, hd⟩)).2.2.2 t₀ ht₀
  refine ⟨⟨_, hz'⟩, fun τ => ho τ, GlobalTheory.FlatLine.liesOn_frBor hinv hon, ?_⟩
  have hrd : rdU (unf s σ) g k (ReciprocityTheory.ChartRestriction.G.FD.rmul fr (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf ((unf s σ).X k) fr)) =
      Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U σ).un k ⟨_, hz'⟩)) := dif_pos hz'
  show lieFacZ S.Dw ξ G * ((unf s σ).X k).pnorm _ _ fr = _
  rw [← hp, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ ho), hrd]

end GlobalTheory.CovHt.Link

namespace GlobalTheory.CovHt.Link

/- English proof (translation)
Establish `hκ : 0 < 2 * Real.pi * xiR D` using `by have := GlobalTheory.ShFam.xiR_pos D; positivity`. Establish `hz : ∀ e : ℤ, (2 * Real.pi * xiR D) ^ e = Real.exp (e * Real.log (2 * Real.pi * xiR D))` using `fun e => by`. Rewrite using `[← Real.rpow_intCast, Real.rpow_def_of_pos hκ, mul_comm]`. Repeatedly rewrite using `[hz]`. Rewrite using `[← Real.exp_sum, lieFacZ, ← Real.exp_nat_mul]`.

Use `congr 1`. Rewrite using `[← Finset.sum_mul, Fintype.sum_sigma]`. Simplify using `only [Int.cast_neg, Finset.sum_neg_distrib]`. Establish `e : ∀ (τ : D.host.E →+* ℂ) (i : Fin (S.Dw.mult τ)), ((exOf S.Dw la 0 (some ⟨τ, i⟩) : ℤ) : ℝ) = ((wtOf S.Dw la 0).1 (τ, i) : ℝ)` using `fun τ i => rfl`. Simplify using `only [e]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lieFactor_sq_eq_prod {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} (la : AllWt.Weight S.Dw) :
    lieFacZ S.Dw (xiR D) (wtOf S.Dw la 0) ^ 2 =
      ∏ z : Letter S.Dw, (2 * Real.pi * xiR D) ^ (-exOf S.Dw la 0 (some z)) := by
  have hκ : 0 < 2 * Real.pi * xiR D := by have := GlobalTheory.ShFam.xiR_pos D; positivity
  have hz : ∀ e : ℤ, (2 * Real.pi * xiR D) ^ e = Real.exp (e * Real.log (2 * Real.pi * xiR D)) := fun e => by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hκ, mul_comm]
  simp_rw [hz]
  rw [← Real.exp_sum, lieFacZ, ← Real.exp_nat_mul]
  congr 1
  rw [← Finset.sum_mul, Fintype.sum_sigma]
  simp only [Int.cast_neg, Finset.sum_neg_distrib]
  have e : ∀ (τ : D.host.E →+* ℂ) (i : Fin (S.Dw.mult τ)),
      ((exOf S.Dw la 0 (some ⟨τ, i⟩) : ℤ) : ℝ) = ((wtOf S.Dw la 0).1 (τ, i) : ℝ) := fun τ i => rfl
  simp only [e]
  push_cast
  ring

end GlobalTheory.CovHt.Link

namespace GlobalTheory.CovHt.Link

/- English proof (translation)
Introduce `hb`. Express the relevant statement in the definitionally equal form `(Φ.C k).π (under p) ∉ Set.range s.T.Z.jQ at hb`. Take `⟨t, ht⟩ : ∃ t, (Φ.C k).π (under p) = ((Φ.C k).down p).1 t` from `⟨_, (Scheme.Hom.comp_apply p.1 (Φ.C k).π _).symm⟩`. Rewrite `ht` using `[h]`. Apply `hb` to reduce the goal to its premises.

Rewrite using `[ht]`. Conclude with `⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (Scheme.Hom.comp_apply _ _ _).symm⟩`.
-/
theorem mem_offBoundary_of_complex_point {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)
    {σ : D.what₂.LL →+* ℂ} (ψ : ℂ →+* ℂ) (p : Pts (Φ.C k).Y σ) {σ₁ : κ.c.F →+* ℂ} (y : FrPt s.Xo κ.c (CAt σ₁))
    (h : ((Φ.C k).down p).1 = spMap ψ ≫ (GlobalTheory.ShFam.cxPt s.T.Z y).1) : p ∈ offBd Φ k σ := by
  intro hb
  change (Φ.C k).π (under p) ∉ Set.range s.T.Z.jQ at hb
  obtain ⟨t, ht⟩ : ∃ t, (Φ.C k).π (under p) = ((Φ.C k).down p).1 t :=
    ⟨_, (Scheme.Hom.comp_apply p.1 (Φ.C k).π _).symm⟩
  rw [h] at ht
  apply hb
  rw [ht]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (Scheme.Hom.comp_apply _ _ _).symm⟩

end GlobalTheory.CovHt.Link

namespace GlobalTheory.CovHt.Link

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Set `u : Sp (Φ.C k).Y.Fn` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Φ.C k).Y.Fn)`. Conclude with `Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ _ _ hne) (h u) (h' u)`.
-/
theorem eq_of_over_of_over {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)
    {Z Z' : Comp s.Xo κ.c} (h : Over Φ k Z) (h' : Over Φ k Z') : Z = Z' := by
  by_contra hne
  let u : Sp (Φ.C k).Y.Fn := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Φ.C k).Y.Fn)
  exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ _ _ hne) (h u) (h' u)

/- English proof (translation)
Establish `hsm : Smooth (genStr s.T.Z)` using `haveI := s.T.smooth`. Use the proof step `SmoothOfRelativeDimension.smooth S.Dw.dim _`. Take `⟨t, ht⟩ : ∃ t, (Φ.C k').π (under p) = ((Φ.C k').down p).1 t` from `⟨_, (Scheme.Hom.comp_apply p.1 (Φ.C k').π _).symm⟩`. Rewrite `ht` using `[h]`. Unfold `GlobalTheory.ShFam.cxPt at ht`.

Simplify using `only [Scheme.Hom.comp_apply] at ht`. Establish `hW` using `GlobalTheory.ShFam.PtComp.preimage_connectedComponent_mem s.T.Z hsm ((Φ.C k').π (under p))`. Establish `eZ : (⟨_, hW⟩ : Comp s.Xo κ.c) = Z`. Assume the negation of the conclusion as `hne`. Establish `hy1` using `hy (spMap ψ t)`.

Use `Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ _ _ hne) ?_ hy1` and prove the remaining obligations. Use `show s.T.Z.jQ _ ∈ connectedComponent _`. Rewrite using `[ht]`. Conclude with `mem_connectedComponent`. Establish `hO' : Over Φ k' Z`.

Introduce `u`. Rewrite using `[← eZ]`. Use `show s.T.Z.jQ _ ∈ connectedComponent _`. Rewrite using `[← Scheme.Hom.comp_apply, (Φ.C k').y0_x, Scheme.Hom.comp_apply]`. Conclude with `(isPreconnected_range (Φ.C k').π.continuous).subset_connectedComponent ⟨_, rfl⟩ ⟨_, rfl⟩`.

Take `⟨q, hq⟩` from `GlobalTheory.T.flag_components_biject_moduli_components D A N j S κ s Φ`. Use `q.injective ?_` and prove the remaining obligations. Rewrite using `[eq_of_over_of_over Φ k' (hq k') hO', eq_of_over_of_over Φ k (hq k) hk]`.
-/
theorem component_eq_of_complex_point {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k k' : s.Comp)
    (Z : Comp s.Xo κ.c) (hk : Over Φ k Z) {σ : D.what₂.LL →+* ℂ} (ψ : ℂ →+* ℂ) (p : Pts (Φ.C k').Y σ) {σ₁ : κ.c.F →+* ℂ}
    (y : FrPt s.Xo κ.c (CAt σ₁)) (hy : LiesOn Z y)
    (h : ((Φ.C k').down p).1 = spMap ψ ≫ (GlobalTheory.ShFam.cxPt s.T.Z y).1) : k' = k := by
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  obtain ⟨t, ht⟩ : ∃ t, (Φ.C k').π (under p) = ((Φ.C k').down p).1 t :=
    ⟨_, (Scheme.Hom.comp_apply p.1 (Φ.C k').π _).symm⟩
  rw [h] at ht
  unfold GlobalTheory.ShFam.cxPt at ht
  simp only [Scheme.Hom.comp_apply] at ht
  have hW := GlobalTheory.ShFam.PtComp.preimage_connectedComponent_mem s.T.Z hsm ((Φ.C k').π (under p))
  have eZ : (⟨_, hW⟩ : Comp s.Xo κ.c) = Z := by
    by_contra hne
    have hy1 := hy (spMap ψ t)
    refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ _ _ hne) ?_ hy1
    show s.T.Z.jQ _ ∈ connectedComponent _
    rw [ht]
    exact mem_connectedComponent
  have hO' : Over Φ k' Z := by
    intro u
    rw [← eZ]
    show s.T.Z.jQ _ ∈ connectedComponent _
    rw [← Scheme.Hom.comp_apply, (Φ.C k').y0_x, Scheme.Hom.comp_apply]
    exact (isPreconnected_range (Φ.C k').π.continuous).subset_connectedComponent ⟨_, rfl⟩ ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := GlobalTheory.T.flag_components_biject_moduli_components D A N j S κ s Φ
  refine q.injective ?_
  rw [eq_of_over_of_over Φ k' (hq k') hO', eq_of_over_of_over Φ k (hq k) hk]

end GlobalTheory.CovHt.Link

/- English proof (translation)
Introduce `D A N j S κ s Φ x k Z hO la g hg σ hσ z hz`. Take `⟨hgc, hgZ⟩` from `hg`. Establish `hgW` using `mem_cuspW.1 hgc`. Take `⟨xx, ho, hon, hN⟩` from `hom_norm_orthogonal_frame s hσ (hgW.2 σ hσ) hz (ξ := xiR D)`. Choose the witnesses or unpack the hypotheses as in `⟨σ', e1⟩ : ∃ σ' : D.what₂.LL →+* ℂ, Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ') = σ := by`.

Use `⟨σ.comp κ.e.toRingHom, ?_⟩` and prove the remaining obligations. Establish `e2 : GlobalTheory.ShFam.embOf κ.e (σ.comp κ.e.toRingHom) = σ`. Use extensionality with `a`. Simplify using `[GlobalTheory.ShFam.embOf]`. Rewrite using `[e2]`.

Conclude with `if_pos hσ`. Substitute `e1` using the available equality. Take `⟨ψ, ⟨k', p⟩, g', hψ, hσψ, hg', hc, hd, hm⟩` from `GlobalTheory.T.exists_automorphism_orthogonal_point s Φ σ' z.1 xx ho`. Establish `hk : k' = k` using `component_eq_of_complex_point Φ k k' Z hO ψ p _ hon hd`. Substitute `hk` using the available equality.

Establish `hex0 : exOf S.Dw la 0 none = 0` using `rfl`. Establish `hco` using `GlobalTheory.T.flag_component_frame_point_relation (Φ.C k') ψ p g' ((s.U _).un z.1 xx) (exOf S.Dw la 0) g (by rcases hψ with rfl | rfl; exacts [rfl, RingHom.ext Complex.conj_conj]) hσψ hc hd hm hex0 hgW.1`. Use `⟨σ', p, mem_offBoundary_of_complex_point Φ k' ψ p _ hd, ?_⟩` and prove the remaining obligations. Rewrite using `[hN]`. Establish `hn : (fun z : Letter S.Dw => -exOf S.Dw la 0 (some z)) = fun z => -exOf S.Dw la 0 (some z)` using `rfl`.

Establish `hpn : (geoTrue D.what₂.LL).pn (Φ.C k').Y σ' ((Φ.C k').Lw la) (hodgeLw x Φ k' σ' la) ((geoTrue D.what₂.LL).cx (Φ.C k').Y σ' ((Φ.C k').val g)) p = ‖ψ (Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U _).un z.1 xx)))‖ ^ 2 * ∏ z : Letter S.Dw, (2 * Real.pi * xiR D) ^ (-exOf S.Dw la 0 (s …` using `(pn_cast_met _ _ _ _).trans (pn_metsOf_none hg' hco)`. Establish `hψn : ‖ψ (Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U _).un z.1 xx)))‖ = ‖Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U _).un z.1 xx))‖`. Break down `hψ with rfl | rfl` into its components or cases. Both sides reduce to the same expression. Conclude with `RCLike.norm_conj _`.

Use `show _ = (geoTrue D.what₂.LL).pn (Φ.C k').Y σ' ((Φ.C k').Lw la) (hodgeLw x Φ k' σ' la) ((geoTrue D.what₂.LL).cx (Φ.C k').Y σ' ((Φ.C k').val g)) p`. Rewrite using `[hpn, hψn, ← lieFactor_sq_eq_prod la]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.CovHt.Link.homN_sq_eq_infSq : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (x : ToroidalCompactificationData s) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ (la : AllWt.Weight S.Dw), ∀ g ∈ cuspOn (unf s) Z (wtOf S.Dw la 0), ∀ σ : κ.c.F →+* ℂ, GoodEmb κ.c σ → ∀ z ∈ framesOn (unf s σ) Z, ∃ (σ' : D.what₂.LL →+* ℂ) (y : Pts (Φ.C k).Y σ'), y ∈ offBd Φ k σ' ∧ homN (unf s σ) (xiR D) (wtOf S.Dw la 0) g z ^ 2 = infSq Φ k x la σ' ((Φ.C k).val g) y := by
  intro D A N j S κ s Φ x k Z hO la g hg σ hσ z hz
  obtain ⟨hgc, hgZ⟩ := hg
  have hgW := mem_cuspW.1 hgc
  obtain ⟨xx, ho, hon, hN⟩ := hom_norm_orthogonal_frame s hσ (hgW.2 σ hσ) hz (ξ := xiR D)
  obtain ⟨σ', e1⟩ : ∃ σ' : D.what₂.LL →+* ℂ, Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ') = σ := by
    refine ⟨σ.comp κ.e.toRingHom, ?_⟩
    have e2 : GlobalTheory.ShFam.embOf κ.e (σ.comp κ.e.toRingHom) = σ := by
      ext a; simp [GlobalTheory.ShFam.embOf]
    rw [e2]
    exact if_pos hσ
  subst e1
  obtain ⟨ψ, ⟨k', p⟩, g', hψ, hσψ, hg', hc, hd, hm⟩ := GlobalTheory.T.exists_automorphism_orthogonal_point s Φ σ' z.1 xx ho
  have hk : k' = k := component_eq_of_complex_point Φ k k' Z hO ψ p _ hon hd
  subst hk
  have hex0 : exOf S.Dw la 0 none = 0 := rfl
  have hco := GlobalTheory.T.flag_component_frame_point_relation (Φ.C k') ψ p g' ((s.U _).un z.1 xx) (exOf S.Dw la 0) g
    (by rcases hψ with rfl | rfl; exacts [rfl, RingHom.ext Complex.conj_conj]) hσψ hc hd hm hex0 hgW.1
  refine ⟨σ', p, mem_offBoundary_of_complex_point Φ k' ψ p _ hd, ?_⟩
  rw [hN]
  have hn : (fun z : Letter S.Dw => -exOf S.Dw la 0 (some z)) = fun z => -exOf S.Dw la 0 (some z) := rfl
  have hpn : (geoTrue D.what₂.LL).pn (Φ.C k').Y σ' ((Φ.C k').Lw la) (hodgeLw x Φ k' σ' la)
      ((geoTrue D.what₂.LL).cx (Φ.C k').Y σ' ((Φ.C k').val g)) p =
      ‖ψ (Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U _).un z.1 xx)))‖ ^ 2 *
        ∏ z : Letter S.Dw, (2 * Real.pi * xiR D) ^ (-exOf S.Dw la 0 (some z)) :=
    (pn_cast_met _ _ _ _).trans (pn_metsOf_none hg' hco)
  have hψn : ‖ψ (Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U _).un z.1 xx)))‖ =
      ‖Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U _).un z.1 xx))‖ := by
    rcases hψ with rfl | rfl
    · rfl
    · exact RCLike.norm_conj _
  show _ = (geoTrue D.what₂.LL).pn (Φ.C k').Y σ' ((Φ.C k').Lw la) (hodgeLw x Φ k' σ' la)
      ((geoTrue D.what₂.LL).cx (Φ.C k').Y σ' ((Φ.C k').val g)) p
  rw [hpn, hψn, ← lieFactor_sq_eq_prod la]
  ring
