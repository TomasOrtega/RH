import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.TopForm GlobalTheory.Adelic GlobalTheory.TangentOrigin
open GlobalTheory.FlagTan (IsDef)

/- English proof (translation)
Use `letI := α.toAlgebra`. Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h`. Take `⟨ι, σ, _, _, P, hP⟩` from `‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out`. Use `letI := Fintype.ofFinite ι`. Use `letI := Fintype.ofFinite σ`.

Establish `hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D`. Rewrite using `[Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]`. Simplify using `[Algebra.Presentation.dimension]`. Set `e` to `Fintype.equivFinOfCardEq hc`. Conclude with `⟨fun i => P.val (e.symm i), isFreeGen_dForm _ (P.basisKaehler.reindex e) fun i => by simp⟩`.
-/
theorem exists_isFreeGen_dForm {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) : ∃ f : Fin D → A, IsFreeGen A (dForm α f) := by
  classical
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨fun i => P.val (e.symm i), isFreeGen_dForm _ (P.basisKaehler.reindex e) fun i => by
    simp⟩

/- English proof (translation)
Take `⟨V, hV, hx, -⟩` from `Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top x)`. Establish `h` using `HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top`. Take `⟨s, hs, h⟩` from `(RingHom.locally_iff_isLocalization RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h`. Take `⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), x ∈ Y.basicOpen (t : Γ(Y, V))` from `Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)`. Use `IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))` as an intermediate fact.

Establish `h₁` using `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))`. Establish `h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D`. Rewrite using `[← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]`. Conclude with `h₁`. Take `⟨f, hf⟩` from `exists_isFreeGen_dForm h₂`.

Conclude with `⟨_, f, hxt, IsAffineOpen.basicOpen hV _, hf⟩`.
-/
theorem exists_isFrame_dOn {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ)
    [SmoothOfRelativeDimension D p] (x : Y) :
    ∃ (U : Y.Opens) (f : Fin D → Γ(Y, U)), x ∈ U ∧ IsFrame (dOn p f) := by
  obtain ⟨V, hV, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top x)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), x ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨f, hf⟩ := exists_isFreeGen_dForm h₂
  exact ⟨_, f, hxt, IsAffineOpen.basicOpen hV _, hf⟩

/- English proof (translation)
Establish `h : ∀ z : PrimeSpectrum (DualNumber L), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0` using `fun z a => by`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Assume the negation of the conclusion as `h0`. Conclude with `z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))`.

Introduce `ha`. Use `z.2.mem_of_pow_mem 2 ?_` and prove the remaining obligations. Apply the tactic sequence `rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]`. Conclude with `z.asIdeal.zero_mem`. Use extensionality with `a`.

Rewrite using `[h, h]`.
-/
theorem primeSpectrum_dualNumber_eq {L : Type} [Field L] (x y : PrimeSpectrum (DualNumber L)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber L), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

/- English proof (translation)
Introduce `s _`. Establish `hp : (spMap φ) (IsLocalRing.closedPoint L) = s` using `primeSpectrum_dualNumber_eq _ _`. Establish `h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V` using `h (Set.mem_univ _)`. Conclude with `hp ▸ h₁`.
-/
theorem le_preimage_of_dualNumber {L : Type} [Field L] {T : Scheme.{0}} (φ : DualNumber L →+* L)
    (x : Sp (DualNumber L) ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint L) = s := primeSpectrum_dualNumber_eq _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

/- English proof (translation)
Establish `e` using `(X.ptY_frMap hd).trans hz.symm`. Establish `hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z` using `fun s _ => by`. Use `ho (Set.mem_univ s)` as an intermediate fact. Rewrite `this` using `[M.off_eq]`. Conclude with `this`.

Establish `hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange` using `le_preimage_of_dualNumber _ _ _ (by`. Rewrite using `[e]`. Introduce and unpack `s -`. Conclude with `⟨(z ≫ M.σ) s, rfl⟩)`. Establish `hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z)`.

Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `hb (Set.mem_univ s)`. Take `⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v` from `⟨_, IsOpenImmersion.lift_fac _ _ hr⟩`. Establish `ered : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ w = z ≫ M.σ`. Rewrite using `[← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]`.

Establish `hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z` using `le_preimage_of_dualNumber _ _ _ (by rw [ered]; exact hU)`. Take `⟨zv, hzv, -⟩` from `M.existsUnique_lift w hwU`. Establish `hred : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ zv = z` using `(M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl`. Use `⟨zv, ?_, fun O hO => le_preimage_of_dualNumber _ _ _ (by rw [hred]; exact hO)⟩` and prove the remaining obligations. Rewrite using `[toFlag, ← Category.assoc, hzv, hw]`.
-/
theorem exists_tanLift {L : Type} [Field L] [Algebra c.F L] {Q : FrPt Xo c L} {v : FrPt Xo c (DualNumber L)}
    (hd : IsDef Q v) {z : Sp L ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ zv : Sp (DualNumber L) ⟶ M.X, zv ≫ toFlag M = X.ptY v ∧ ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ zv ⁻¹ᵁ O := by
  have e := (X.ptY_frMap hd).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_dualNumber _ _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_dualNumber _ _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, fun O hO => le_preimage_of_dualNumber _ _ _ (by rw [hred]; exact hO)⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

/- English proof (translation)
Establish `hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z` using `fun s _ => by`. Use `ho (Set.mem_univ s)` as an intermediate fact. Rewrite `this` using `[M.off_eq]`. Conclude with `this`. Establish `hF : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ flagOpen X` using `hU`.

Establish `hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k` using `fun s _ => (((common₀ X Z).pull M.σ).mem _ _ _).1 (hi (Set.mem_univ s)).2`. Take `⟨_, hch⟩` from `exists_chartFr _ hF`. Take `⟨Q, hQ⟩` from `hch k hk`. Establish `hb` using `(GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).1 Q`. Take `⟨v, hv⟩` from `(hKS L Q).exists_isTanFrame`.

Establish `e : z ≫ toFlag M = X.ptY Q` using `GlobalTheory.FlagMod.FlagCover.eq_ptY hQ.lies`. Use `choose zv hzv hzO using fun b => exists_tanLift M (hv.isDef b) e ho`. Establish `hpi : ptOf z ∈ M.K.bundle.U i` using `((le_iff_ptOf_mem z _).1 hi).1`. Take `⟨V, f, hx, hf⟩` from `exists_isFrame_dOn M.str (GlobalTheory.FlagTan.dimFlag Dw) (ptOf z)`. Take `⟨O, hO, hxO, hOV⟩` from `Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens (show ptOf z ∈ V ⊓ M.K.bundle.U i from ⟨hx, hpi⟩)`.

Establish `hOV' : O ≤ V` using `hOV.trans inf_le_left`. Establish `hOi : O ≤ M.K.bundle.U i` using `hOV.trans inf_le_right`. Set `g : Fin (GlobalTheory.FlagTan.dimFlag Dw) → Γ(M.X, O)` to `fun a => resG M.X hOV' (f a)`. Establish `hu : IsUnit (M.K.jacobian i hOi g)` using `(M.K.isUnit_jacobian_iff i hO hOi g).2 (by`. Use `hf.res hO hOV'` as an intermediate fact.

Rewrite using `[resForm_dOn] at this)` and apply the resulting hypothesis. Establish `hzO' : ⊤ ≤ z ⁻¹ᵁ O` using `(le_iff_ptOf_mem z _).2 hxO`. Establish `a` using `h L Q Q 1 v z zv i k O hOi g hzO' (fun b => hzO b O hzO') hk ho hi hQ hb hv hzv`. Establish `hd : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzO _ O hzO') (g a)).snd).det ≠ 0` using `fun h0 => by`. Rewrite `a` using `[h0, mul_zero]`.

Conclude with `mul_ne_zero (Units.ne_zero _) (hu.map (evalPt z O hzO')).ne_zero a.symm`. Conclude with `IsKS.val_eq M h h' hOi hzO' (hzv := fun b => hzO b O hzO') ho hi hQ hb hv hzv hd`.
-/
theorem IsKS.val_eq_of_ksIso
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y)
    {ω ω' : H0 M.str (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)) M.off} (h : IsKS M ω) (h' : IsKS M ω')
    {L : Type} [Field L] (z : Sp L ⟶ M.X) (i : M.K.bundle.ι) (k : X.F.J) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)) :
    H0.val (B := LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω =
      H0.val (B := LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω' := by
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hF : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ flagOpen X := hU
  have hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s _ =>
    (((common₀ X Z).pull M.σ).mem _ _ _).1 (hi (Set.mem_univ s)).2
  obtain ⟨_, hch⟩ := exists_chartFr _ hF
  obtain ⟨Q, hQ⟩ := hch k hk
  have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).1 Q
  obtain ⟨v, hv⟩ := (hKS L Q).exists_isTanFrame
  have e : z ≫ toFlag M = X.ptY Q := GlobalTheory.FlagMod.FlagCover.eq_ptY hQ.lies
  choose zv hzv hzO using fun b => exists_tanLift M (hv.isDef b) e ho
  have hpi : ptOf z ∈ M.K.bundle.U i := ((le_iff_ptOf_mem z _).1 hi).1
  obtain ⟨V, f, hx, hf⟩ := exists_isFrame_dOn M.str (GlobalTheory.FlagTan.dimFlag Dw) (ptOf z)
  obtain ⟨O, hO, hxO, hOV⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens (show ptOf z ∈ V ⊓ M.K.bundle.U i from ⟨hx, hpi⟩)
  have hOV' : O ≤ V := hOV.trans inf_le_left
  have hOi : O ≤ M.K.bundle.U i := hOV.trans inf_le_right
  let g : Fin (GlobalTheory.FlagTan.dimFlag Dw) → Γ(M.X, O) := fun a => resG M.X hOV' (f a)
  have hu : IsUnit (M.K.jacobian i hOi g) := (M.K.isUnit_jacobian_iff i hO hOi g).2 (by
    have := hf.res hO hOV'
    rwa [resForm_dOn] at this)
  have hzO' : ⊤ ≤ z ⁻¹ᵁ O := (le_iff_ptOf_mem z _).2 hxO
  have a := h L Q Q 1 v z zv i k O hOi g hzO' (fun b => hzO b O hzO') hk ho hi hQ hb hv hzv
  have hd : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzO _ O hzO') (g a)).snd).det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at a
    exact mul_ne_zero (Units.ne_zero _) (hu.map (evalPt z O hzO')).ne_zero a.symm
  exact IsKS.val_eq M h h' hOi hzO' (hzv := fun b => hzO b O hzO') ho hi hQ hb hv hzv hd

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y X Z M hKS ω ω'`. Use `haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (GlobalTheory.FlagTan.dimFlag Dw) M.str`. Use `haveI : IsReduced M.X := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isReduced_of_smooth M.str`. Establish `e : ω.ω = ω'.ω`. Use `H0.ext_germ fun y hy => ?_` and prove the remaining obligations.

Take `⟨k, hk⟩` from `Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (toFlag M y)))`. Take `⟨i, hi⟩` from `exists_chart M.K.isLB y`. Establish `hm : y ∈ ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k)` using `(((common₀ X Z).pull M.σ).mem _ _ _).2 hk`. Use `⟨(i, flagIdx M _ k), ⟨hi, hm⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ger y _ (H0.loc ω.ω _) = ger y _ (H0.loc ω'.ω _)`.

Use `congrArg _ (GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => ?_)` and prove the remaining obligations. Conclude with `IsKS.val_eq_of_ksIso M hKS ω.isKS ω'.isKS z i k (GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz) (GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz)`. Consider the cases of `ω`. Consider the cases of `ω'`. Consider the cases of `e`.

Both sides reduce to the same expression.
-/
theorem CanId.eq_of_ksIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ ω ω' : CanId M, ω = ω' := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS ω ω'
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (GlobalTheory.FlagTan.dimFlag Dw) M.str
  haveI : IsReduced M.X := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isReduced_of_smooth M.str
  have e : ω.ω = ω'.ω := by
    refine H0.ext_germ fun y hy => ?_
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (toFlag M y)))
    obtain ⟨i, hi⟩ := exists_chart M.K.isLB y
    have hm : y ∈ ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k) := (((common₀ X Z).pull M.σ).mem _ _ _).2 hk
    refine ⟨(i, flagIdx M _ k), ⟨hi, hm⟩, ?_⟩
    change ger y _ (H0.loc ω.ω _) = ger y _ (H0.loc ω'.ω _)
    refine congrArg _ (GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => ?_)
    exact IsKS.val_eq_of_ksIso M hKS ω.isKS ω'.isKS z i k (GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz)
  cases ω
  cases ω'
  cases e
  rfl

end GlobalTheory.CompHS
