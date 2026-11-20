import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSncCoordinatesComplexPointSmoothVariety
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.DivSec

/- English proof (translation)
Introduce `R _ _ n r hR ι e s hs`. Set `r' : Fin n → R` to `fun j => if h : ∃ i, e i = j then s h.choose else r j`. Establish `hr' : ∀ i, r' (e i) = s i` using `fun i => by`. Establish `h : ∃ i', e i' = e i` using `⟨i, rfl⟩`. Simplify using `only [r', dif_pos h]`.

Use `congr 1`. Conclude with `e.injective h.choose_spec`. Use `⟨r', ⟨?_, hR.2⟩, hr'⟩` and prove the remaining obligations. Rewrite using `[← hR.1]`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Distinguish the cases in `h : ∃ i, e i = j`. Take `⟨i, rfl⟩` from `h`. Rewrite using `[hr']`.

Establish `: s i ∈ Ideal.span {r (e i)}` using `hs i ▸ Ideal.subset_span rfl`. Conclude with `Ideal.span_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (e i))) this`. Simplify using `only [r', dif_neg h]`. Conclude with `Ideal.subset_span ⟨j, rfl⟩`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Distinguish the cases in `h : ∃ i, e i = j`. Take `⟨i, rfl⟩` from `h`. Establish `: r (e i) ∈ Ideal.span {s i}` using `(hs i).symm ▸ Ideal.subset_span rfl`. Conclude with `Ideal.span_mono (Set.singleton_subset_iff.2 (show s i ∈ Set.range r' from ⟨e i, hr' i⟩)) this`.

Establish `: r j = r' j` using `by simp only [r', dif_neg h]`. Rewrite using `[this]`. Conclude with `Ideal.subset_span ⟨j, rfl⟩`.
-/
theorem exists_rsp_replace : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (r : Fin n → R), Rsp R n r →
    ∀ (ι : Type) (e : ι ↪ Fin n) (s : ι → R), (∀ i, Ideal.span {s i} = Ideal.span {r (e i)}) →
    ∃ r' : Fin n → R, Rsp R n r' ∧ ∀ i, r' (e i) = s i := by
  intro R _ _ n r hR ι e s hs
  classical
  let r' : Fin n → R := fun j => if h : ∃ i, e i = j then s h.choose else r j
  have hr' : ∀ i, r' (e i) = s i := fun i => by
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    simp only [r', dif_pos h]
    congr 1
    exact e.injective h.choose_spec
  refine ⟨r', ⟨?_, hR.2⟩, hr'⟩
  rw [← hR.1]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases h : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := h
      rw [hr']
      have : s i ∈ Ideal.span {r (e i)} := hs i ▸ Ideal.subset_span rfl
      exact Ideal.span_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (e i))) this
    · simp only [r', dif_neg h]
      exact Ideal.subset_span ⟨j, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases h : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := h
      have : r (e i) ∈ Ideal.span {s i} := (hs i).symm ▸ Ideal.subset_span rfl
      exact Ideal.span_mono (Set.singleton_subset_iff.2 (show s i ∈ Set.range r' from ⟨e i, hr' i⟩)) this
    · have : r j = r' j := by simp only [r', dif_neg h]
      rw [this]
      exact Ideal.subset_span ⟨j, rfl⟩

/- English proof (translation)
Introduce `Y y n r`. Use `choose U hU s hs using fun j => TopCat.Presheaf.germ_exist Y.presheaf (r j)`. Establish `hmem : ∀ t : Finset (Fin n), y ∈ t.inf U`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert a t ha ih`. Rewrite using `[Finset.inf_insert]`. Conclude with `⟨hU a, ih⟩`. Take `⟨V, hV, hyV, hVO⟩` from `Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (hmem Finset.univ)`.

Establish `hle : ∀ j, V ≤ U j` using `fun j => le_trans hVO (Finset.inf_le (Finset.mem_univ j))`. Use `⟨⟨V, hV⟩, hyV, fun j => resG Y (hle j) (s j), fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← hs j]`. Conclude with `Y.presheaf.germ_res_apply (homOfLE (hle j)) y hyV (s j)`.
-/
theorem exists_affine_germ_eq : ∀ (Y : Scheme.{0}) (y : Y) (n : ℕ) (r : Fin n → Y.presheaf.stalk y),
    ∃ (V : Y.affineOpens) (hy : y ∈ V.1) (F : Fin n → Γ(Y, V.1)), ∀ j, Y.presheaf.germ V.1 y hy (F j) = r j := by
  intro Y y n r
  classical
  choose U hU s hs using fun j => TopCat.Presheaf.germ_exist Y.presheaf (r j)
  have hmem : ∀ t : Finset (Fin n), y ∈ t.inf U := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.inf_insert]
      exact ⟨hU a, ih⟩
  obtain ⟨V, hV, hyV, hVO⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (hmem Finset.univ)
  have hle : ∀ j, V ≤ U j := fun j => le_trans hVO (Finset.inf_le (Finset.mem_univ j))
  refine ⟨⟨V, hV⟩, hyV, fun j => resG Y (hle j) (s j), fun j => ?_⟩
  rw [← hs j]
  exact Y.presheaf.germ_res_apply (homOfLE (hle j)) y hyV (s j)

/- English proof (translation)
Introduce `k _ Y p σ n c x₀ hx U V hU hV f g h`. Take `⟨W, hW, iU, iV, he⟩` from `TopCat.Presheaf.germ_eq Y.presheaf _ hU hV f g h`. Establish `hWU : W ≤ U` using `leOfHom iU`. Establish `hWV : W ≤ V` using `leOfHom iV`. Establish `hx' : x₀ ∈ ptsIn p σ W` using `mem_ptsIn.2 hW`.

Establish `hres : resG Y hWU f = resG Y hWV g` using `he`. Establish `e1 : ∀ z ∈ ptsIn p σ W, ev p σ U f z = ev p σ V g z`. Introduce `z hz`. Rewrite using `[← ev_res hWU hz, ← ev_res hWV hz, hres]`. Establish `e2 : ev p σ U f ∘ c.e.symm =ᶠ[nhds (c.e x₀)] ev p σ V g ∘ c.e.symm` using `Filter.eventually_of_mem ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hx hx')) fun v hv => e1 _ hv.2`.

Conclude with `e2.fderiv_eq`.
-/
theorem fderiv_ev_eq_of_germ_eq : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (n : ℕ)
    (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source → ∀ (U V : Y.Opens)
    (hU : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U) (hV : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ V) (f : Γ(Y, U)) (g : Γ(Y, V)),
    Y.presheaf.germ U _ hU f = Y.presheaf.germ V _ hV g →
    fderiv ℂ (ev p σ U f ∘ c.e.symm) (c.e x₀) = fderiv ℂ (ev p σ V g ∘ c.e.symm) (c.e x₀) := by
  intro k _ Y p σ n c x₀ hx U V hU hV f g h
  obtain ⟨W, hW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq Y.presheaf _ hU hV f g h
  have hWU : W ≤ U := leOfHom iU
  have hWV : W ≤ V := leOfHom iV
  have hx' : x₀ ∈ ptsIn p σ W := mem_ptsIn.2 hW
  have hres : resG Y hWU f = resG Y hWV g := he
  have e1 : ∀ z ∈ ptsIn p σ W, ev p σ U f z = ev p σ V g z := by
    intro z hz
    rw [← ev_res hWU hz, ← ev_res hWV hz, hres]
  have e2 : ev p σ U f ∘ c.e.symm =ᶠ[nhds (c.e x₀)] ev p σ V g ∘ c.e.symm :=
    Filter.eventually_of_mem ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)).mem_nhds
      (GlobalTheory.ChartGlue.mem_over c.e hx hx')) fun v hv => e1 _ hv.2
  exact e2.fderiv_eq

/- English proof (translation)
Introduce `k _ _ Y p n σ hsm c x₀ hx m C hL U f hU hf`. Use `haveI := hsm`. Take `⟨hreg, N, r, e, hR, hr⟩` from `hL`. Establish `hyU : ∀ i, x₀.1 (IsLocalRing.closedPoint ℂ) ∈ (U i).1` using `fun i => mem_ptsIn.1 (hU i)`. Set `s : {i : Fin m // x₀.1 (IsLocalRing.closedPoint ℂ) ∈ C i} → Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))` to `fun i => Y.presheaf.germ (U i.1).1 _ (hyU i.1) (f i.1)`.

Establish `hs : ∀ i, Ideal.span {s i} = Ideal.span {r (e i)}` using `fun i => by`. Rewrite using `[← hr i, ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ _ (U i.1) (hyU i.1), hf, Ideal.map_span, Set.image_singleton]`. Take `⟨r', hR', hr'⟩` from `exists_rsp_replace _ N r hR _ e s hs`. Take `⟨V, hyV, F, hF⟩` from `exists_affine_germ_eq Y _ N r'`. Establish `hR'' : Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) N (fun j => Y.presheaf.germ V.1 _ hyV (F j))`.

Establish `: (fun j => Y.presheaf.germ V.1 _ hyV (F j)) = r'` using `funext hF`. Rewrite using `[this]`. Conclude with `hR'`. Establish `hli` using `SncChart.linearIndependent_fderiv_params k Y p n σ c x₀ hx V hyV N F hR''`. Establish `h2` using `hli.comp e e.injective`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply]`. Conclude with `fderiv_ev_eq_of_germ_eq k Y p σ n c x₀ hx _ _ (hyU i.1) hyV (f i.1) (F (e i)) ((hr' i).symm.trans (hF (e i)).symm)`.
-/
theorem linearIndependent_fderiv_eqns : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ),
    SmoothOfRelativeDimension n p → ∀ (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source →
    ∀ (m : ℕ) (C : Fin m → Closeds Y), LSncAt Y C (x₀.1 (IsLocalRing.closedPoint ℂ)) →
    ∀ (U : Fin m → Y.affineOpens) (f : ∀ i, Γ(Y, (U i).1)), (∀ i, x₀ ∈ ptsIn p σ (U i).1) →
    (∀ i, (Scheme.IdealSheafData.vanishingIdeal (C i)).ideal (U i) = Ideal.span {f i}) →
    LinearIndependent ℂ (fun i : {i : Fin m // x₀.1 (IsLocalRing.closedPoint ℂ) ∈ C i} =>
      fderiv ℂ (ev p σ (U i.1).1 (f i.1) ∘ c.e.symm) (c.e x₀)) := by
  intro k _ _ Y p n σ hsm c x₀ hx m C hL U f hU hf
  haveI := hsm
  obtain ⟨hreg, N, r, e, hR, hr⟩ := hL
  have hyU : ∀ i, x₀.1 (IsLocalRing.closedPoint ℂ) ∈ (U i).1 := fun i => mem_ptsIn.1 (hU i)
  let s : {i : Fin m // x₀.1 (IsLocalRing.closedPoint ℂ) ∈ C i} → Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)) :=
    fun i => Y.presheaf.germ (U i.1).1 _ (hyU i.1) (f i.1)
  have hs : ∀ i, Ideal.span {s i} = Ideal.span {r (e i)} := fun i => by
    rw [← hr i, ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ _ (U i.1) (hyU i.1), hf, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨r', hR', hr'⟩ := exists_rsp_replace _ N r hR _ e s hs
  obtain ⟨V, hyV, F, hF⟩ := exists_affine_germ_eq Y _ N r'
  have hR'' : Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) N
      (fun j => Y.presheaf.germ V.1 _ hyV (F j)) := by
    have : (fun j => Y.presheaf.germ V.1 _ hyV (F j)) = r' := funext hF
    rw [this]; exact hR'
  have hli := SncChart.linearIndependent_fderiv_params k Y p n σ c x₀ hx V hyV N F hR''
  have h2 := hli.comp e e.injective
  convert h2 using 1
  funext i
  simp only [Function.comp_apply]
  exact fderiv_ev_eq_of_germ_eq k Y p σ n c x₀ hx _ _ (hyU i.1) hyV (f i.1) (F (e i)) ((hr' i).symm.trans (hF (e i)).symm)

/- English proof (translation)
Introduce `k _ Y p σ n B hB e hhol hsymm j`. Take `⟨c, hcj⟩` from `hB j`. Rewrite using `[hcj]`. Prove the components needed by the constructor for the conclusion. Use `(c.analyticOnNhd_finChart_iff e.open_source e).2 ?_` and prove the remaining obligations.

Use `differentiableOn_pi.2 fun i => ?_` and prove the remaining obligations. Establish `hO` using `GlobalTheory.ChartGlue.isOpen_over c.e e.open_source`. Conclude with `hhol i _ _ c.e.symm hO (GlobalTheory.ShFam.Hor.Sec.isHolTo_symm c hO Set.inter_subset_left) (fun b hb => hb.2)`. Establish `hO : IsOpen (e.target ∩ e.symm ⁻¹' c.finChart.source)` using `e.isOpen_inter_preimage_symm c.finChart.open_source`. Use `(SCV.analyticOnNhd_iff_differentiableOn hO).2 ?_` and prove the remaining obligations.

Introduce `b hb`. Establish `h1` using `GlobalTheory.TrueCx.TorHolo.differentiableAt_chart e.open_target hsymm c hb.1 hb.2`. Conclude with `((EuclideanSpace.equiv (Fin n) ℂ).differentiable.differentiableAt.comp b h1).differentiableWithinAt`.
-/
theorem isCompatChart_of_holAlong : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (n : ℕ)
    (B : FinHolAtlas n (CxPts p σ)), IsAlgAtlas B → ∀ (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)),
    (∀ j, HolAlong e.source fun x => e x j) → IsHolTo e.target (fun z => (e.symm z).1) → IsCompatChart B e := by
  intro k _ Y p σ n B hB e hhol hsymm j
  obtain ⟨c, hcj⟩ := hB j
  rw [hcj]
  constructor
  · refine (c.analyticOnNhd_finChart_iff e.open_source e).2 ?_
    refine differentiableOn_pi.2 fun i => ?_
    have hO := GlobalTheory.ChartGlue.isOpen_over c.e e.open_source
    exact hhol i _ _ c.e.symm hO (GlobalTheory.ShFam.Hor.Sec.isHolTo_symm c hO Set.inter_subset_left) (fun b hb => hb.2)
  · have hO : IsOpen (e.target ∩ e.symm ⁻¹' c.finChart.source) := e.isOpen_inter_preimage_symm c.finChart.open_source
    refine (SCV.analyticOnNhd_iff_differentiableOn hO).2 ?_
    intro b hb
    have h1 := GlobalTheory.TrueCx.TorHolo.differentiableAt_chart e.open_target hsymm c hb.1 hb.2
    exact ((EuclideanSpace.equiv (Fin n) ℂ).differentiable.differentiableAt.comp b h1).differentiableWithinAt

/- English proof (translation)
Introduce `F _ _ Y σ m C n hn B hB hsnc`. Introduce `x`. Set `S : Finset (Fin m)` to `Finset.univ.filter fun i => LiesIn x (C i)`. Establish `hS : ∀ i, i ∈ S ↔ LiesIn x (C i)` using `fun i => by simp [S]`. Take `⟨c, hc⟩` from `AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := σ) x`.

Set `W : Y.X.Opens` to `Finset.univ.inf fun i => (GlobalTheory.DivSec.eqV hn i x).1`. Establish `hWle : ∀ i, W ≤ (GlobalTheory.DivSec.eqV hn i x).1` using `fun i => Finset.inf_le (Finset.mem_univ i)`. Establish `hmemI : ∀ (z : Pts Y σ) (s : Finset (Fin m)), z ∈ ptsIn Y.str σ (s.inf fun i => (GlobalTheory.DivSec.eqV hn i x).1) ↔ ∀ i ∈ s, z ∈ ptsIn Y.str σ (GlobalTheory.DivSec.eqV hn i x).1`. Introduce `z s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.inf_insert, mem_ptsIn_inf, ih, Finset.forall_mem_insert]`. Establish `hWU : ptsIn Y.str σ W = (GlobalTheory.DivSec.divPot hn).U x`. Use extensionality with `z`. Rewrite using `[hmemI z Finset.univ]`.

Simplify using `only [GlobalTheory.DivSec.divPot, Set.mem_iInter, Finset.mem_univ, true_implies]`. Establish `hxW : x ∈ ptsIn Y.str σ W` using `hWU ▸ (GlobalTheory.DivSec.divPot hn).mem_U x`. Set `ix : Fin S.card → Fin m` to `fun j => (S.equivFin.symm j).1`. Establish `hix : Function.Injective ix` using `fun i j h => S.equivFin.symm.injective (Subtype.ext h)`. Establish `hixS : ∀ j, LiesIn x (C (ix j))` using `fun j => (hS _).1 (S.equivFin.symm j).2`.

Set `g : Fin S.card → Γ(Y.X, W)` to `fun j => resG Y.X (hWle (ix j)) (GlobalTheory.DivSec.eqT hn (ix j) x)`. Establish `hgev : ∀ i z, z ∈ ptsIn Y.str σ W → ev Y.str σ W (resG Y.X (hWle i) (GlobalTheory.DivSec.eqT hn i x)) z = ev Y.str σ _ (GlobalTheory.DivSec.eqT hn i x) z` using `fun i z hz => ev_res _ hz _`. Establish `hzero : ∀ i z, z ∈ ptsIn Y.str σ W → (ev Y.str σ _ (GlobalTheory.DivSec.eqT hn i x) z = 0 ↔ LiesIn z (C i))` using `fun i z hz => ev_eq_zero_iff (GlobalTheory.DivSec.eq_spec hn i x).2.1 (ptsIn_mono (hWle i) hz)`. Establish `h0 : ∀ j, ev Y.str σ W (g j) x = 0` using `fun j => by`. Simplify using `only [g]`.

Rewrite using `[hgev _ _ hxW]`. Conclude with `(hzero _ _ hxW).2 (hixS j)`. Establish `hliA` using `linearIndependent_fderiv_eqns F Y.X Y.str Y.dim σ inferInstance c x hc m C (hsnc _) (fun i => GlobalTheory.DivSec.eqV hn i x) (fun i => GlobalTheory.DivSec.eqT hn i x) (fun i => (GlobalTheory.DivSec.eq_spec hn i x).1) (fun i => (GlobalTheory.DivSec.eq_spec hn i x).2.1)`. Establish `hli : LinearIndependent ℂ (fun j => fderiv ℂ (ev Y.str σ W (g j) ∘ c.e.symm) (c.e x))`. Establish `h2` using `hliA.comp (fun j => (⟨ix j, hixS j⟩ : {i : Fin m // x.1 (IsLocalRing.closedPoint ℂ) ∈ C i})) (by intro a b h; exact hix (by simpa using congrArg Subtype.val h))`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Establish `e : ev Y.str σ W (g j) ∘ c.e.symm =ᶠ[nhds (c.e x)] ev Y.str σ _ (GlobalTheory.DivSec.eqT hn (ix j) x) ∘ c.e.symm` using `Filter.eventually_of_mem ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hc hxW)) fun v hv => hgev _ _ hv.2`. Simplify using `only [Function.comp_apply]`. Conclude with `e.fderiv_eq`.

Establish `hcard : S.card ≤ Y.dim`. Use `hli.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V Y.dim) (F' := ℂ)).finrank_eq, Module.finrank_linearMap, Module.finrank_self, _root_.mul_one]`. Simplify `this` using `[ReciprocityTheory.L2DbarEstimates.V]`. Take `⟨e, hx0, hsub, -, hhol, hsymm, hev⟩` from `SncChart.exists_chart_of_fderiv F Y.X Y.str Y.dim σ c x hc W hxW S.card g h0 hli`.

Set `O : Set (Pts Y σ)` to `(GlobalTheory.DivSec.divPot hn).U x ∩ ⋂ k, {z | LiesIn x (C k) ∨ ¬ LiesIn z (C k)}`. Establish `hO : IsOpen O`. Use `((GlobalTheory.DivSec.divPot hn).isOpen_U x).inter (isOpen_iInter_of_finite fun k => ?_)` and prove the remaining obligations. Distinguish the cases in `h : LiesIn x (C k)`. Simplify using `[h]`.

Simplify `isOpen_not_liesIn (p := Y.str) (σ := σ) (C k)` using `[h]`. Set `ψ` to `e.restrOpen O hO`. Establish `hψs : ψ.source = e.source ∩ O` using `e.restrOpen_source O hO`. Establish `hψa : ∀ z, ψ z = e z` using `fun z => rfl`. Establish `hψW : ∀ z ∈ ψ.source, z ∈ ptsIn Y.str σ W` using `fun z hz => hsub (hψs ▸ hz).1`.

Establish `hψO : ∀ z ∈ ψ.source, z ∈ O` using `fun z hz => (hψs ▸ hz).2`. Establish `hcompat : IsCompatChart B ψ`. Use `isCompatChart_of_holAlong F Y.X Y.str σ Y.dim B hB ψ (fun j => ?_) ?_` and prove the remaining obligations. Introduce `V _ _ _ B' y hB' hy hm`. Conclude with `hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)`.

Conclude with `GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1`. Set `pos : ∀ k, LiesIn x (C k) → Fin Y.dim` to `fun k hk => ⟨S.equivFin ⟨k, (hS k).2 hk⟩, lt_of_lt_of_le (Fin.isLt _) hcard⟩`. Set `τ : Fin m → Option (Fin Y.dim)` to `fun k => if hk : LiesIn x (C k) then some (pos k hk) else none`. Establish `hτ : ∀ k (hk : LiesIn x (C k)) z, z ∈ ψ.source → ψ z (pos k hk) = ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) z`. Introduce `k hk z hz`.

Rewrite using `[hψa, hev z (hψs ▸ hz).1 (pos k hk) (S.equivFin ⟨k, (hS k).2 hk⟩).isLt]`. Establish `hj : (⟨(pos k hk : ℕ), (S.equivFin ⟨k, (hS k).2 hk⟩).isLt⟩ : Fin S.card) = S.equivFin ⟨k, (hS k).2 hk⟩` using `rfl`. Establish `hk' : ix (S.equivFin ⟨k, (hS k).2 hk⟩) = k` using `by simp [ix]`. Rewrite using `[hj]`. Simplify using `only [g]`.

Rewrite using `[hgev _ _ (hψW z hz)]`. Rewrite using `[hk']`. Use `⟨ψ, hcompat, hψs ▸ ⟨hx0, (GlobalTheory.DivSec.divPot hn).mem_U x, Set.mem_iInter.2 fun k => ?_⟩, fun z hz => (hψO z hz).1, τ, ?_, ?_, fun z => ∏ k ∈ Finset.univ.filter (fun k => ¬ LiesIn x (C k)), ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) z, ?_, ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : LiesIn x (C k)`. Conclude with `Or.inl h`.

Conclude with `Or.inr h`. Introduce `k k' i h1 h2`. Simplify using `only [τ] at h1 h2`. Use `split_ifs at h1 h2 with hk hk'`. Use `(Option.some.inj h1).trans (Option.some.inj h2).symm` as an intermediate fact.

Establish `h3 : S.equivFin ⟨k, (hS k).2 hk⟩ = S.equivFin ⟨k', (hS k').2 hk'⟩` using `Fin.ext (by simpa [pos] using congrArg Fin.val this)`. Conclude with `congrArg Subtype.val (S.equivFin.injective h3)`. Introduce `k`. Use extensionality with `z`. Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, τ]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hzk, hz⟩`. Use `⟨hz, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : LiesIn x (C k)`. Use `⟨pos k hk, by simp [hk], ?_⟩` and prove the remaining obligations.

Rewrite using `[hτ k hk z hz]`. Conclude with `(hzero k z (hψW z hz)).2 hzk`. Conclude with `absurd hzk ((Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk)`. Introduce and unpack `⟨hz, i, hi, h0⟩`. Use `⟨?_, hz⟩` and prove the remaining obligations.

Distinguish the cases in `hk : LiesIn x (C k)`. Simplify using `only [hk, dite_true, Option.some.injEq] at hi`. Substitute `hi` using the available equality. Rewrite `h0` using `[hτ k hk z hz]`. Conclude with `(hzero k z (hψW z hz)).1 h0`.

Simplify using `[hk] at hi`. Use `(hB.holoOn_iff (Y.an σ) ψ.open_source).2 fun j => ?_` and prove the remaining obligations. Establish `h : ∀ k, DifferentiableOn ℂ (fun v => ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) (((Y.an σ).chart j).e.symm v)) (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ψ.source)` using `fun k => ((Y.an σ).holoOn_ev _ (GlobalTheory.DivSec.eqT hn k x) j).mono fun v hv => ⟨hv.1, ptsIn_mono (hWle k) (hψW _ hv.2)⟩`. Establish `key : ∀ s : Finset (Fin m), DifferentiableOn ℂ (fun v => ∏ k ∈ s, ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) (((Y.an σ).chart j).e.symm v)) (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ψ.source)`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using differentiableOn_const (1 : ℂ)`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.prod_insert ha]`. Conclude with `(h a).mul ih`.

Conclude with `(key _).congr fun v _ => rfl`. Introduce `z hz`. Use `Finset.prod_ne_zero_iff.2 fun k hk => ?_` and prove the remaining obligations. Establish `hk' : ¬ LiesIn x (C k)` using `(Finset.mem_filter.1 hk).2`. Introduce `h`.

Conclude with `(Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk' ((hzero k z (hψW z hz)).1 h)`. Introduce `z hz`. Simplify using `only [GlobalTheory.DivSec.divSec]`. Rewrite using `[← Finset.prod_filter_not_mul_prod_filter Finset.univ (fun k => LiesIn x (C k))]`. Use `congr 1`.

Rewrite using `[Finset.prod_filter]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : LiesIn x (C k)`. Simplify using `only [hk, if_true, τ, dite_true, pow_one]`. Conclude with `(hτ k hk z hz).symm`.

Simplify using `[hk, τ]`.
-/
theorem isSNC_divSec : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (m : ℕ) (C : Fin m → Closeds Y.X) (n : Fin m → Pts Y σ → ℝ) (hn : ∀ i, IsDivNorm (Y.an σ) (C i) (n i)) (B : FinHolAtlas Y.dim (Pts Y σ)), IsAlgAtlas B → (∀ y : Y.X, LSncAt Y.X C y) → IsSNC B (GlobalTheory.DivSec.divPot hn) (GlobalTheory.DivSec.divSec hn) (fun _ : Fin m => 1) (fun i => {z | LiesIn z (C i)}) := by
  intro F _ _ Y σ m C n hn B hB hsnc
  classical
  intro x
  let S : Finset (Fin m) := Finset.univ.filter fun i => LiesIn x (C i)
  have hS : ∀ i, i ∈ S ↔ LiesIn x (C i) := fun i => by simp [S]
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := σ) x
  let W : Y.X.Opens := Finset.univ.inf fun i => (GlobalTheory.DivSec.eqV hn i x).1
  have hWle : ∀ i, W ≤ (GlobalTheory.DivSec.eqV hn i x).1 := fun i => Finset.inf_le (Finset.mem_univ i)
  have hmemI : ∀ (z : Pts Y σ) (s : Finset (Fin m)), z ∈ ptsIn Y.str σ (s.inf fun i => (GlobalTheory.DivSec.eqV hn i x).1) ↔
      ∀ i ∈ s, z ∈ ptsIn Y.str σ (GlobalTheory.DivSec.eqV hn i x).1 := by
    intro z s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.inf_insert, mem_ptsIn_inf, ih, Finset.forall_mem_insert]
  have hWU : ptsIn Y.str σ W = (GlobalTheory.DivSec.divPot hn).U x := by
    ext z
    rw [hmemI z Finset.univ]
    simp only [GlobalTheory.DivSec.divPot, Set.mem_iInter, Finset.mem_univ, true_implies]
  have hxW : x ∈ ptsIn Y.str σ W := hWU ▸ (GlobalTheory.DivSec.divPot hn).mem_U x
  let ix : Fin S.card → Fin m := fun j => (S.equivFin.symm j).1
  have hix : Function.Injective ix := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  have hixS : ∀ j, LiesIn x (C (ix j)) := fun j => (hS _).1 (S.equivFin.symm j).2
  let g : Fin S.card → Γ(Y.X, W) := fun j => resG Y.X (hWle (ix j)) (GlobalTheory.DivSec.eqT hn (ix j) x)
  have hgev : ∀ i z, z ∈ ptsIn Y.str σ W →
      ev Y.str σ W (resG Y.X (hWle i) (GlobalTheory.DivSec.eqT hn i x)) z = ev Y.str σ _ (GlobalTheory.DivSec.eqT hn i x) z :=
    fun i z hz => ev_res _ hz _
  have hzero : ∀ i z, z ∈ ptsIn Y.str σ W →
      (ev Y.str σ _ (GlobalTheory.DivSec.eqT hn i x) z = 0 ↔ LiesIn z (C i)) := fun i z hz =>
    ev_eq_zero_iff (GlobalTheory.DivSec.eq_spec hn i x).2.1 (ptsIn_mono (hWle i) hz)
  have h0 : ∀ j, ev Y.str σ W (g j) x = 0 := fun j => by
    simp only [g]; rw [hgev _ _ hxW]; exact (hzero _ _ hxW).2 (hixS j)
  have hliA := linearIndependent_fderiv_eqns F Y.X Y.str Y.dim σ inferInstance c x hc m C (hsnc _) (fun i => GlobalTheory.DivSec.eqV hn i x)
    (fun i => GlobalTheory.DivSec.eqT hn i x) (fun i => (GlobalTheory.DivSec.eq_spec hn i x).1) (fun i => (GlobalTheory.DivSec.eq_spec hn i x).2.1)
  have hli : LinearIndependent ℂ (fun j => fderiv ℂ (ev Y.str σ W (g j) ∘ c.e.symm) (c.e x)) := by
    have h2 := hliA.comp (fun j => (⟨ix j, hixS j⟩ : {i : Fin m // x.1 (IsLocalRing.closedPoint ℂ) ∈ C i}))
      (by intro a b h; exact hix (by simpa using congrArg Subtype.val h))
    convert h2 using 1
    funext j
    have e : ev Y.str σ W (g j) ∘ c.e.symm =ᶠ[nhds (c.e x)]
        ev Y.str σ _ (GlobalTheory.DivSec.eqT hn (ix j) x) ∘ c.e.symm :=
      Filter.eventually_of_mem ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)).mem_nhds
        (GlobalTheory.ChartGlue.mem_over c.e hc hxW)) fun v hv => hgev _ _ hv.2
    simp only [Function.comp_apply]
    exact e.fderiv_eq
  have hcard : S.card ≤ Y.dim := by
    have := hli.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V Y.dim) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, -, hhol, hsymm, hev⟩ :=
    SncChart.exists_chart_of_fderiv F Y.X Y.str Y.dim σ c x hc W hxW S.card g h0 hli
  let O : Set (Pts Y σ) := (GlobalTheory.DivSec.divPot hn).U x ∩ ⋂ k, {z | LiesIn x (C k) ∨ ¬ LiesIn z (C k)}
  have hO : IsOpen O := by
    refine ((GlobalTheory.DivSec.divPot hn).isOpen_U x).inter (isOpen_iInter_of_finite fun k => ?_)
    by_cases h : LiesIn x (C k)
    · simp [h]
    · simpa [h] using isOpen_not_liesIn (p := Y.str) (σ := σ) (C k)
  let ψ := e.restrOpen O hO
  have hψs : ψ.source = e.source ∩ O := e.restrOpen_source O hO
  have hψa : ∀ z, ψ z = e z := fun z => rfl
  have hψW : ∀ z ∈ ψ.source, z ∈ ptsIn Y.str σ W := fun z hz => hsub (hψs ▸ hz).1
  have hψO : ∀ z ∈ ψ.source, z ∈ O := fun z hz => (hψs ▸ hz).2
  have hcompat : IsCompatChart B ψ := by
    refine isCompatChart_of_holAlong F Y.X Y.str σ Y.dim B hB ψ (fun j => ?_) ?_
    · intro V _ _ _ B' y hB' hy hm
      exact hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)
    · exact GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1
  let pos : ∀ k, LiesIn x (C k) → Fin Y.dim := fun k hk =>
    ⟨S.equivFin ⟨k, (hS k).2 hk⟩, lt_of_lt_of_le (Fin.isLt _) hcard⟩
  let τ : Fin m → Option (Fin Y.dim) := fun k => if hk : LiesIn x (C k) then some (pos k hk) else none
  have hτ : ∀ k (hk : LiesIn x (C k)) z, z ∈ ψ.source → ψ z (pos k hk) = ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) z := by
    intro k hk z hz
    rw [hψa, hev z (hψs ▸ hz).1 (pos k hk) (S.equivFin ⟨k, (hS k).2 hk⟩).isLt]
    have hj : (⟨(pos k hk : ℕ), (S.equivFin ⟨k, (hS k).2 hk⟩).isLt⟩ : Fin S.card) = S.equivFin ⟨k, (hS k).2 hk⟩ := rfl
    have hk' : ix (S.equivFin ⟨k, (hS k).2 hk⟩) = k := by simp [ix]
    rw [hj]
    simp only [g]
    rw [hgev _ _ (hψW z hz)]
    rw [hk']
  refine ⟨ψ, hcompat, hψs ▸ ⟨hx0, (GlobalTheory.DivSec.divPot hn).mem_U x, Set.mem_iInter.2 fun k => ?_⟩,
    fun z hz => (hψO z hz).1, τ, ?_, ?_, fun z => ∏ k ∈ Finset.univ.filter (fun k => ¬ LiesIn x (C k)),
      ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) z, ?_, ?_, ?_⟩
  · by_cases h : LiesIn x (C k)
    · exact Or.inl h
    · exact Or.inr h
  · intro k k' i h1 h2
    simp only [τ] at h1 h2
    split_ifs at h1 h2 with hk hk'
    have := (Option.some.inj h1).trans (Option.some.inj h2).symm
    have h3 : S.equivFin ⟨k, (hS k).2 hk⟩ = S.equivFin ⟨k', (hS k').2 hk'⟩ := Fin.ext (by simpa [pos] using congrArg Fin.val this)
    exact congrArg Subtype.val (S.equivFin.injective h3)
  · intro k
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, τ]
    constructor
    · rintro ⟨hzk, hz⟩
      refine ⟨hz, ?_⟩
      by_cases hk : LiesIn x (C k)
      · refine ⟨pos k hk, by simp [hk], ?_⟩
        rw [hτ k hk z hz]
        exact (hzero k z (hψW z hz)).2 hzk
      · exact absurd hzk ((Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk)
    · rintro ⟨hz, i, hi, h0⟩
      refine ⟨?_, hz⟩
      by_cases hk : LiesIn x (C k)
      · simp only [hk, dite_true, Option.some.injEq] at hi
        subst hi
        rw [hτ k hk z hz] at h0
        exact (hzero k z (hψW z hz)).1 h0
      · simp [hk] at hi
  · refine (hB.holoOn_iff (Y.an σ) ψ.open_source).2 fun j => ?_
    have h : ∀ k, DifferentiableOn ℂ (fun v => ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) (((Y.an σ).chart j).e.symm v))
        (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ψ.source) := fun k =>
      ((Y.an σ).holoOn_ev _ (GlobalTheory.DivSec.eqT hn k x) j).mono fun v hv => ⟨hv.1, ptsIn_mono (hWle k) (hψW _ hv.2)⟩
    have key : ∀ s : Finset (Fin m), DifferentiableOn ℂ
        (fun v => ∏ k ∈ s, ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) (((Y.an σ).chart j).e.symm v))
        (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ψ.source) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using differentiableOn_const (1 : ℂ)
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact (h a).mul ih
    exact (key _).congr fun v _ => rfl
  · intro z hz
    refine Finset.prod_ne_zero_iff.2 fun k hk => ?_
    have hk' : ¬ LiesIn x (C k) := (Finset.mem_filter.1 hk).2
    intro h
    exact (Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk' ((hzero k z (hψW z hz)).1 h)
  · intro z hz
    simp only [GlobalTheory.DivSec.divSec]
    rw [← Finset.prod_filter_not_mul_prod_filter Finset.univ (fun k => LiesIn x (C k))]
    congr 1
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : LiesIn x (C k)
    · simp only [hk, if_true, τ, dite_true, pow_one]
      exact (hτ k hk z hz).symm
    · simp [hk, τ]

end GlobalTheory.DivSec
