import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section
namespace GlobalTheory.Mem.R3.MKExt
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Substitute `hH` using the available equality. Consider the cases of `hDw`. Consider the cases of `hl`. Consider the cases of `hXo`. Consider the cases of `hc`.

Consider the cases of `hU`. Substitute `ha` using the available equality. Substitute `hn` using the available equality. Substitute `hj` using the available equality. Conclude with `⟨f', HEq.rfl, Iff.rfl⟩`.
-/
theorem cusp_match {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : Host E} {Dw : ℕ → Datum H}
    {Dw' : ℕ → Datum H'} {l : Level H} {l' : Level H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {c : Coeff l} {c' : Coeff l'} {r : ℕ} {U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ r}
    {U' : ∀ j (σ : c'.F →+* ℂ), Unf (Xo' j) c' σ r} (hH : H' = H) (hDw : HEq Dw' Dw) (hl : HEq l' l)
    (hXo : HEq Xo' Xo) (hc : HEq c' c) (hU : HEq U' U) {j j' : ℕ} (hj : j' = j) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ}
    (ha : a' = a) (hn : n' = n) (f' : cusp (Xo' j') c' (U' j') a' n') :
    ∃ f : cusp (Xo j) c (U j) a n, HEq f' f ∧
      ((∀ la, ∀ v ∈ valSet (Xo' j') c' (algCls (Xo' j') c') la, 0 ≤ v (f' : Rul (Xo' j') c')) ↔
        (∀ la, ∀ v ∈ valSet (Xo j) c (algCls (Xo j) c) la, 0 ≤ v (f : Rul (Xo j) c))) := by
  subst hH; cases hDw; cases hl; cases hXo; cases hc; cases hU; subst ha; subst hn; subst hj
  exact ⟨f', HEq.rfl, Iff.rfl⟩

/- English proof (translation)
Substitute `hH` using the available equality. Consider the cases of `hDw`. Consider the cases of `hl`. Consider the cases of `hXo`. Consider the cases of `hc`.

Consider the cases of `hU`. Substitute `ha` using the available equality. Substitute `hn` using the available equality. Substitute `hj` using the available equality. Conclude with `⟨f, HEq.rfl, Iff.rfl⟩`.
-/
theorem cusp_match' {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : Host E} {Dw : ℕ → Datum H}
    {Dw' : ℕ → Datum H'} {l : Level H} {l' : Level H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {c : Coeff l} {c' : Coeff l'} {r : ℕ} {U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ r}
    {U' : ∀ j (σ : c'.F →+* ℂ), Unf (Xo' j) c' σ r} (hH : H' = H) (hDw : HEq Dw' Dw) (hl : HEq l' l)
    (hXo : HEq Xo' Xo) (hc : HEq c' c) (hU : HEq U' U) {j j' : ℕ} (hj : j' = j) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ}
    (ha : a' = a) (hn : n' = n) (f : cusp (Xo j) c (U j) a n) :
    ∃ f' : cusp (Xo' j') c' (U' j') a' n', HEq f' f ∧
      ((∀ la, ∀ v ∈ valSet (Xo' j') c' (algCls (Xo' j') c') la, 0 ≤ v (f' : Rul (Xo' j') c')) ↔
        (∀ la, ∀ v ∈ valSet (Xo j) c (algCls (Xo j) c) la, 0 ≤ v (f : Rul (Xo j) c))) := by
  subst hH; cases hDw; cases hl; cases hXo; cases hc; cases hU; subst ha; subst hn; subst hj
  exact ⟨f, HEq.rfl, Iff.rfl⟩

/- English proof (translation)
Substitute `hj` using the available equality. Consider the cases of `h`. Both sides reduce to the same expression.
-/
theorem extendByZero_eq_of_heq_families {Tau : Type} (p : ℕ → ℕ) {j j' : ℕ} (hj : j' = j) {a : Tau → Fin (p j) → ℕ}
    {a' : Tau → Fin (p j') → ℕ} (h : HEq a' a) (t : Tau) : ext0 (a' t) = ext0 (a t) := by
  subst hj; cases h; rfl

section Comparison₂
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h la v hv`. Establish `h1` using `h la ((fw.pt i la).symm ⟨v, hv⟩)`. Rewrite `h1` using `[fw.nrm_eq, Core.nrmM_le_one_iff, Equiv.apply_symm_apply]`. Conclude with `h1`.

Introduce `h la y`. Rewrite using `[fw.nrm_eq, Core.nrmM_le_one_iff]`. Conclude with `h la _ (fw.pt i la y).2`.
-/
theorem nrm_le_one_iff (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m)
    (f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) :
    (∀ la (y : (R.FW i).Pt la), (R.FW i).nrm la y (fw.e i f) ≤ 1) ↔
      ∀ la, ∀ v ∈ valSet (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (algCls (T.Q.Xo ((i : ℕ) + 1)) T.Q.c) la,
        0 ≤ v (f : T.R ((i : ℕ) + 1)) := by
  constructor
  · intro h la v hv
    have h1 := h la ((fw.pt i la).symm ⟨v, hv⟩)
    rw [fw.nrm_eq, Core.nrmM_le_one_iff, Equiv.apply_symm_apply] at h1
    exact h1
  · intro h la y
    rw [fw.nrm_eq, Core.nrmM_le_one_iff]
    exact h la _ (fw.pt i la y).2

end Comparison₂

end GlobalTheory.Mem.R3.MKExt

namespace GlobalTheory.Mem.R3.MKExt
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `_ _ _ _ _ _ _`. Use `StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hN j j' hj φ hφ => ?_` and prove the remaining obligations. Take `⟨hB, -⟩` from `hE`. Use `clear * - hB hN hj φ hφ`. Consider the cases of `B with | mk P => ?_`.

Consider the cases of `B' with | mk P' => ?_`. Simplify using `only at hB`. Substitute `hB` using the available equality. Establish `hH : z'.core.Q.H = z.core.Q.H` using `eq_of_heq hN.H`. Establish `hκ` using `hN.κ j j' hj`.

Establish `ha : wtA (z'.geo.κ j') = wtA (z.geo.κ j)`. Use function extensionality and compare the values at `x`. Unfold `wtA`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Establish `e1 : ext0 ((z'.geo.κ j').aP t) = ext0 ((z.geo.κ j).aP t)` using `extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t`.

Establish `e2 : ext0 ((z'.geo.κ j').aM t) = ext0 ((z.geo.κ j).aM t)` using `extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t`. Rewrite using `[e1, e2]`. Both sides reduce to the same expression. Establish `hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1` using `by rw [hj]`. Establish `M1` using `fun f' => cusp_match hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f'`.

Establish `M2` using `fun f => cusp_match' hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f`. Establish `hn : z'.R.nW j' = z.R.nW j` using `(congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))`. Establish `hinj : Function.Injective (w'.st Z').toD7.what₂.embLL` using `RingHom.injective _`. Use extensionality with `x'`. Simplify using `only [SetLike.mem_coe, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Take `⟨f', he'⟩ : ∃ f', z'.geo.fw.e j' f' = ⟨x', h1⟩` from `⟨_, LinearEquiv.apply_symm_apply _ _⟩`. Take `⟨f, hff, hP⟩` from `M1 f'`. Establish `hI' : ∀ la (y : (z'.R.FW j').Pt la), (z'.R.FW j').nrm la y (z'.geo.fw.e j' f') ≤ 1`.

Rewrite using `[he']`. Conclude with `h2`. Establish `hI` using `hP.1 ((nrm_le_one_iff z'.geo.fw j' f').1 hI')`. Establish `hx' : ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = x'` using `congrArg Subtype.val he'`. Use `⟨((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL), ⟨(z.geo.fw.e j f).2, (nrm_le_one_iff z.geo.fw j f).2 hI⟩, fun k k' hk => ?_⟩` and prove the remaining obligations.

Establish `h3` using `hN.forms j j' hj f f' hff k k' hk`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hφ]`. Conclude with `(congrArg (fun v => (w'.st Z').toD7.what₂.embLL (v k')) hx').symm.trans h3`. Introduce and unpack `⟨x, ⟨h1, h2⟩, hrel⟩`.

Take `⟨f, he⟩ : ∃ f, z.geo.fw.e j f = ⟨x, h1⟩` from `⟨_, LinearEquiv.apply_symm_apply _ _⟩`. Take `⟨f', hff, hP⟩` from `M2 f`. Establish `hI : ∀ la (y : (z.R.FW j).Pt la), (z.R.FW j).nrm la y (z.geo.fw.e j f) ≤ 1`. Rewrite using `[he]`. Conclude with `h2`.

Establish `hI'` using `hP.2 ((nrm_le_one_iff z.geo.fw j f).1 hI)`. Establish `hx : ((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = x` using `congrArg Subtype.val he`. Establish `hx' : x' = ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)`. Use function extensionality and compare the values at `k'`. Establish `hk : ((Fin.cast hn k' : Fin (z.R.nW j)) : ℕ) = k'` using `rfl`.

Establish `h3` using `hN.forms j j' hj f f' hff (Fin.cast hn k') k' hk`. Establish `h4` using `hrel (Fin.cast hn k') k' hk`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[h4]`. Conclude with `(hφ _).trans ((congrArg (fun v => (w.st Z).toD7.what₂.embLL (v (Fin.cast hn k'))) hx).symm.trans h3.symm)`.

Substitute `hx'` using the available equality. Conclude with `⟨(z'.geo.fw.e j' f').2, (nrm_le_one_iff z'.geo.fw j' f').2 hI'⟩`.
-/
theorem mk_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ((z'.R.FW j').MK : Set (Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)) = {x' | ∃ x ∈ (z.R.FW j).MK, ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hN j j' hj φ hφ => ?_
  obtain ⟨hB, -⟩ := hE
  clear * - hB hN hj φ hφ
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : wtA (z'.geo.κ j') = wtA (z.geo.κ j) := by
    funext x
    unfold wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : ext0 ((z'.geo.κ j').aP t) = ext0 ((z.geo.κ j).aP t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : ext0 ((z'.geo.κ j').aM t) = ext0 ((z.geo.κ j).aM t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have M1 := fun f' => cusp_match hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f'
  have M2 := fun f => cusp_match' hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  ext x'
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨f', he'⟩ : ∃ f', z'.geo.fw.e j' f' = ⟨x', h1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨f, hff, hP⟩ := M1 f'
    have hI' : ∀ la (y : (z'.R.FW j').Pt la), (z'.R.FW j').nrm la y (z'.geo.fw.e j' f') ≤ 1 := by
      rw [he']; exact h2
    have hI := hP.1 ((nrm_le_one_iff z'.geo.fw j' f').1 hI')
    have hx' : ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = x' :=
      congrArg Subtype.val he'
    refine ⟨((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL),
      ⟨(z.geo.fw.e j f).2, (nrm_le_one_iff z.geo.fw j f).2 hI⟩, fun k k' hk => ?_⟩
    have h3 := hN.forms j j' hj f f' hff k k' hk
    apply hinj
    rw [hφ]
    exact (congrArg (fun v => (w'.st Z').toD7.what₂.embLL (v k')) hx').symm.trans h3
  · rintro ⟨x, ⟨h1, h2⟩, hrel⟩
    obtain ⟨f, he⟩ : ∃ f, z.geo.fw.e j f = ⟨x, h1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨f', hff, hP⟩ := M2 f
    have hI : ∀ la (y : (z.R.FW j).Pt la), (z.R.FW j).nrm la y (z.geo.fw.e j f) ≤ 1 := by
      rw [he]; exact h2
    have hI' := hP.2 ((nrm_le_one_iff z.geo.fw j f).1 hI)
    have hx : ((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = x :=
      congrArg Subtype.val he
    have hx' : x' = ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) := by
      funext k'
      have hk : ((Fin.cast hn k' : Fin (z.R.nW j)) : ℕ) = k' := rfl
      have h3 := hN.forms j j' hj f f' hff (Fin.cast hn k') k' hk
      have h4 := hrel (Fin.cast hn k') k' hk
      apply hinj
      rw [h4]
      exact (hφ _).trans ((congrArg (fun v => (w.st Z).toD7.what₂.embLL (v (Fin.cast hn k'))) hx).symm.trans h3.symm)
    subst hx'
    exact ⟨(z'.geo.fw.e j' f').2, (nrm_le_one_iff z'.geo.fw j' f').2 hI'⟩

end GlobalTheory.Mem.R3.MKExt
