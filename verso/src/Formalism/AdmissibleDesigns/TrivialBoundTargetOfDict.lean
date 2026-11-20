import Formalism.AdmissibleDesigns.RowTrivialBoundOfAdmitted

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Len

variable {R S : Type} [CommRing R] [CommRing S] (σ : R ≃+* S)

/- English proof (translation)
Rewrite using `[Module.length_eq_height, Module.length_eq_height]`. Set `F : Submodule R M → Submodule S N` to `fun p => { carrier := f '' p add_mem' := by`. Introduce and unpack `_ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩`. Conclude with `⟨x + y, p.add_mem hx hy, map_add f x y⟩`. Use the proof step `zero_mem' := ⟨0, p.zero_mem, map_zero f⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `s _ ⟨x, hx, rfl⟩`. Use `⟨σ.symm s • x, p.smul_mem _ hx, ?_⟩` and prove the remaining obligations. Rewrite using `[hs, RingEquiv.apply_symm_apply] }`. Establish `hF : StrictMono F`.

Introduce `p q hpq`. Rewrite `hpq`, the goal using `[SetLike.lt_iff_le_and_exists]`. Take `⟨hle, x, hxq, hxp⟩` from `hpq`. Use `⟨?_, f x, ⟨x, hxq, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `⟨y, hle hy, rfl⟩`. Introduce and unpack `⟨y, hy, hyx⟩`. Conclude with `hxp (hf hyx ▸ hy)`. Conclude with `(Order.height_le_height_apply_of_strictMono F hF ⊤).trans (Order.height_mono le_top)`.
-/
theorem length_le_semi {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →+ N) (hf : Function.Injective f) (hs : ∀ (a : R) (m : M), f (a • m) = σ a • f m) :
    Module.length R M ≤ Module.length S N := by
  classical
  rw [Module.length_eq_height, Module.length_eq_height]
  let F : Submodule R M → Submodule S N := fun p =>
    { carrier := f '' p
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, p.add_mem hx hy, map_add f x y⟩
      zero_mem' := ⟨0, p.zero_mem, map_zero f⟩
      smul_mem' := by
        rintro s _ ⟨x, hx, rfl⟩
        refine ⟨σ.symm s • x, p.smul_mem _ hx, ?_⟩
        rw [hs, RingEquiv.apply_symm_apply] }
  have hF : StrictMono F := by
    intro p q hpq
    rw [SetLike.lt_iff_le_and_exists] at hpq ⊢
    obtain ⟨hle, x, hxq, hxp⟩ := hpq
    refine ⟨?_, f x, ⟨x, hxq, rfl⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hle hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact hxp (hf hyx ▸ hy)
  exact (Order.height_le_height_apply_of_strictMono F hF ⊤).trans (Order.height_mono le_top)

/- English proof (translation)
Establish `hJ : Ideal.span {σ a} = (Ideal.span {a}).map (σ : R →+* S)`. Simplify using `[Ideal.map_span]`. Set `e` to `Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {σ a}) σ hJ`. Establish `he : ∀ (r : R) (x : R ⧸ Ideal.span {a}), e (r • x) = σ r • e x`. Introduce `r x`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Simplify using `[e, Ideal.quotientEquiv_apply, Algebra.smul_def, Ideal.quotientMap_mk, Ideal.Quotient.algebraMap_eq]`. Use `le_antisymm (length_le_semi σ e.toAddEquiv.toAddMonoidHom e.injective he) ?_` and prove the remaining obligations. Use `length_le_semi σ.symm e.symm.toAddEquiv.toAddMonoidHom e.symm.injective ?_` and prove the remaining obligations. Introduce `s y`.

Apply `e.injective` to reduce the goal to its premises. Use `show e (e.symm (s • y)) = e (σ.symm s • e.symm y)`. Rewrite using `[he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`.
-/
theorem length_quot_eq (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = Module.length S (S ⧸ Ideal.span {σ a}) := by
  classical
  have hJ : Ideal.span {σ a} = (Ideal.span {a}).map (σ : R →+* S) := by
    simp [Ideal.map_span]
  let e := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {σ a}) σ hJ
  have he : ∀ (r : R) (x : R ⧸ Ideal.span {a}), e (r • x) = σ r • e x := by
    intro r x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [e, Ideal.quotientEquiv_apply, Algebra.smul_def, Ideal.quotientMap_mk, Ideal.Quotient.algebraMap_eq]
  refine le_antisymm (length_le_semi σ e.toAddEquiv.toAddMonoidHom e.injective he) ?_
  refine length_le_semi σ.symm e.symm.toAddEquiv.toAddMonoidHom e.symm.injective ?_
  intro s y
  apply e.injective
  show e (e.symm (s • y)) = e (σ.symm s • e.symm y)
  rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end Len

section QRec

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] {e : ℕ}

abbrev QrecS (Ce : TwLat PD LL O e) (cB : ℕ) : Submodule O (G → Ce.V ⧸ Ce.L.T) :=
  divisibleCocycles Ce.L ⊓ (HfD PD Ce.L).comap (((PD.p : O) ^ cB) • LinearMap.id)

abbrev Qrec (Ce : TwLat PD LL O e) (cB : ℕ) : Type :=
  ↥(QrecS PD Ce cB) ⧸ (divisibleCocycles Ce.L ⊓ HfD PD Ce.L).comap (QrecS PD Ce cB).subtype

def LenMap {O' : Type} [CommRing O'] (σ : O' ≃+* O) (X : Type) [AddCommGroup X] [Module O' X]
    (Ce : TwLat PD LL O e) (cB : ℕ) : Prop :=
  ∃ f : X →+ Qrec PD Ce cB, Function.Injective f ∧ ∀ (a : O') (x : X), f (a • x) = σ a • f x

/- English proof (translation)
Take `⟨f, hf, hs⟩` from `h`. Use `(length_le_semi σ f hf hs).trans ?_` and prove the remaining obligations. Consider the cases of `Ce`. Conclude with `(hTB.2 e het _ _ _ (by assumption) (by assumption)).2.2`.
-/
theorem len_gen {t cB : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (het : e < t) (Ce : TwLat PD LL O e)
    {O' : Type} [CommRing O'] (σ : O' ≃+* O) {X : Type} [AddCommGroup X] [Module O' X]
    (h : LenMap PD σ X Ce cB) :
    Module.length O' X ≤ ((finrank Qp K : ℕ∞) + 1) * (cB : ℕ∞) * lenOl PD (O := O) := by
  obtain ⟨f, hf, hs⟩ := h
  refine (length_le_semi σ f hf hs).trans ?_
  cases Ce
  exact (hTB.2 e het _ _ _ (by assumption) (by assumption)).2.2

end QRec

section RecLen

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def TBDict2 (cB : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∃ (Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL))
        (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1)),
        YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
        PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd ∧
        YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) ∧
        LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB

set_option maxHeartbeats 800000 in

/- English proof (translation)
The claim follows from `(hd w hw hwrow c hc).elim fun _ h => h.elim fun Cd h' => ⟨Cd, h'.2.2.2⟩`.
-/
private theorem lenMap_Qcore (cB : ℕ) (hd : TBDict2 i dc r π Dd cB) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hwrow : w ∈ dc.row)
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) :
    ∃ Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1),
      LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB :=
  (hd w hw hwrow c hc).elim fun _ h => h.elim fun Cd h' => ⟨Cd, h'.2.2.2⟩

/- English proof (translation)
Unfold `TBDict2 at h`. Unfold `TBDict`. Introduce `w hw hrow c hc`. Take `⟨Y, Cd, h1, h2, h3, -⟩` from `h w hw hrow c hc`. Conclude with `⟨Y, Cd, h1, h2, h3⟩`.
-/
theorem tbDict_of (cB : ℕ) (h : TBDict2 i dc r π Dd cB) : TBDict i dc r π Dd := by
  unfold TBDict2 at h
  unfold TBDict
  intro w hw hrow c hc
  obtain ⟨Y, Cd, h1, h2, h3, -⟩ := h w hw hrow c hc
  exact ⟨Y, Cd, h1, h2, h3⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hw : w ∈ placesOver D.host.E (D.nd.l i)` using `(dc.cover w).1 (Or.inl hwrow)`. Establish `hpl : w ∈ plSet i dc` using `by simp [plSet, hwrow]`. Unfold `TrivialBoundAtRows at hTB`. Unfold `TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility at hTie`. Take `⟨Cd, hL⟩` from `lenMap_Qcore (hd := hd) (hw := hw) (hwrow := hwrow) (c := c) (hc := hc)`.

Establish `het : (c : ℕ) - 1 < D.R.t` using `by have := c.isLt; omega`. Establish `hdeg` using `(hTie w hw).2.2`. Unfold `Br.DegW at hdeg`. Establish `aux : ∀ {R' S' : Type} [CommRing R'] [CommRing S'] (σ' : R' ≃+* S') (n : ℕ), Module.length R' (R' ⧸ Ideal.span {(n : R')}) = Module.length S' (S' ⧸ Ideal.span {(n : S')})`. Introduce `R' S' _ _ σ' n`.

Rewrite using `[length_quot_eq σ', map_natCast]`. Unfold `TBLenAt`. Use `le_trans (len_gen (Br.PD D.loc D.nbr i w hw) (hTB w hw hwrow) het Cd.Ce (selfO i hw) hL) (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[plOf_idx (h := hpl), ← hdeg]`. Unfold `lenOl`.

Rewrite using `[Br.PD_p, ← aux (selfO i hw) (D.nd.l i)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tbLen_w (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) {w : HeightOneSpectrum (𝓞 D.host.E)} (hwrow : w ∈ dc.row)
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) : TBLenAt i dc Dd cB (idx i dc w) c := by
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := (dc.cover w).1 (Or.inl hwrow)
  have hpl : w ∈ plSet i dc := by simp [plSet, hwrow]
  unfold TrivialBoundAtRows at hTB
  unfold TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility at hTie
  obtain ⟨Cd, hL⟩ := lenMap_Qcore (hd := hd) (hw := hw) (hwrow := hwrow) (c := c) (hc := hc)
  have het : (c : ℕ) - 1 < D.R.t := by have := c.isLt; omega
  have hdeg := (hTie w hw).2.2
  unfold Br.DegW at hdeg

  have aux : ∀ {R' S' : Type} [CommRing R'] [CommRing S'] (σ' : R' ≃+* S') (n : ℕ),
      Module.length R' (R' ⧸ Ideal.span {(n : R')}) = Module.length S' (S' ⧸ Ideal.span {(n : S')}) := by
    intro R' S' _ _ σ' n
    rw [length_quot_eq σ', map_natCast]
  unfold TBLenAt
  refine le_trans (len_gen (Br.PD D.loc D.nbr i w hw) (hTB w hw hwrow) het Cd.Ce (selfO i hw) hL) (le_of_eq ?_)
  rw [plOf_idx (h := hpl), ← hdeg]
  unfold lenOl
  rw [Br.PD_p, ← aux (selfO i hw) (D.nd.l i)]
  ring

/- English proof (translation)
Unfold `TBLen`. Introduce `n hn c hc`. Unfold `rowsN at hn`. Take `⟨w, hw, rfl⟩` from `Finset.mem_image.1 hn`. Conclude with `tbLen_w (hTB := hTB) (hTie := hTie) (hd := hd) (hwrow := hw) (c := c) (hc := hc)`.
-/
theorem tbLen_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) : TBLen i dc Dd cB := by
  unfold TBLen
  intro n hn c hc
  unfold rowsN at hn
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hn
  exact tbLen_w (hTB := hTB) (hTie := hTie) (hd := hd) (hwrow := hw) (c := c) (hc := hc)

/- English proof (translation)
The claim follows from `tbTarget_of (hTB := hTB) (hd := tbDict_of (h := hd)) (hlen := tbLen_of (hTB := hTB) (hTie := hTie) (hd := hd))`.
-/
theorem trivial_bound_target_of_dict (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) : TBTarget i dc Dd cB :=
  tbTarget_of (hTB := hTB) (hd := tbDict_of (h := hd)) (hlen := tbLen_of (hTB := hTB) (hTie := hTie) (hd := hd))

end RecLen

end Formalism.MainNotions.N.K.TB

end
