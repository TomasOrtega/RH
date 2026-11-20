import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitOfClassicalPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.SuppTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Use `haveI := ArithBase.ded (o := o') (Ω := Ω)`. Use `haveI := M.lft`. Conclude with `LocallyOfFiniteType.isLocallyNoetherian M.s`.
-/
theorem isLocallyNoetherian_model {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω]
    (M : RatModel o' Ω) : IsLocallyNoetherian M.Z := by
  haveI := ArithBase.ded (o := o') (Ω := Ω)
  haveI := M.lft
  exact LocallyOfFiniteType.isLocallyNoetherian M.s

/- English proof (translation)
Use `(Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg (X.fromSpecStalk x) ?_) (Scheme.fromSpecStalk_closedPoint (x := x)))` and prove the remaining obligations. Conclude with `comap_closedPoint g`.
-/
theorem centre_apply {X : Scheme.{0}} {x : X} {V : Type} [CommRing V] [IsLocalRing V] (g : X.presheaf.stalk x →+* V)
    [IsLocalHom g] : (spMap g ≫ X.fromSpecStalk x) (closedPoint V) = x := by
  refine (Scheme.Hom.comp_apply _ _ _).trans
    (Eq.trans (congrArg (X.fromSpecStalk x) ?_) (Scheme.fromSpecStalk_closedPoint (x := x)))
  exact comap_closedPoint g

/- English proof (translation)
Use `haveI := ArithBase.char (o := o') (Ω := Ω)`. Use `haveI := isLocallyNoetherian_model M`. Use `haveI : CharZero (M.Z.presheaf.stalk x) := RingHom.charZero (M.stalkHom x)`. Take `⟨V, _, _, _, θ, ⟨hd, hcomp, -⟩, hθ, hl⟩` from `GlobalTheory.DvrDom.exists_cdvr_dominating (M.Z.presheaf.stalk x)`. Use `haveI := hd`.

Use `haveI := hcomp`. Use `haveI : CharZero V := charZero_of_injective_ringHom hθ`. Establish `hB : GlobalTheory.Mum.Base V` using `⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩`. Set `θ' : M.O x →+* FractionRing V` to `((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom`. Establish `hθ' : Function.Injective θ'` using `(IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)`.

Set `γ₀ : Ω →+* FractionRing V` to `IsFractionRing.lift (A := M.O x) (K := Ω) hθ'`. Establish `hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a)`. Introduce `a`. Establish `h` using `IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)`. Rewrite using `[← RatModel.coe_stalkEquiv]`.

Use `h.trans ?_` and prove the remaining obligations. Simplify using `[θ']`. Take `⟨T, f, fK, -, hfl, -, hc, hy⟩` from `GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V hB hd (spMap γ₀ ≫ y₀)`. Use `haveI := hfl`. Use `⟨T, spMap (f.comp θ) ≫ M.Z.fromSpecStalk x, fK.comp γ₀, centre_apply _, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x)`. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, hγ₀, hc]`. Rewrite using `[← GlobalTheory.Poinc.GenTrait.spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e, ← Formalism.L2.Pj.spMap_comp', Category.assoc]`. Rewrite using `[hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']`.
-/
theorem exists_uTrait_centre {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω)
    (y₀ : Sp Ω ⟶ Xo.XF c) (x : M.Z) :
    ∃ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V),
      ξ (closedPoint T.V) = x ∧ jK T.V ≫ ξ = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  haveI := ArithBase.char (o := o') (Ω := Ω)
  haveI := isLocallyNoetherian_model M
  haveI : CharZero (M.Z.presheaf.stalk x) := RingHom.charZero (M.stalkHom x)
  obtain ⟨V, _, _, _, θ, ⟨hd, hcomp, -⟩, hθ, hl⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (M.Z.presheaf.stalk x)
  haveI := hd
  haveI := hcomp
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : M.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)
  let γ₀ : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O x) (K := Ω) hθ'
  have hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, -, hfl, -, hc, hy⟩ := GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V hB hd (spMap γ₀ ≫ y₀)
  haveI := hfl
  refine ⟨T, spMap (f.comp θ) ≫ M.Z.fromSpecStalk x, fK.comp γ₀, centre_apply _, ?_, ?_⟩
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← GlobalTheory.Poinc.GenTrait.spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e,
      ← Formalism.L2.Pj.spMap_comp', Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']

end GlobalTheory.UPoinc.SuppTrait

namespace GlobalTheory.UPoinc.SuppTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Use `letI := C.b.toAlgebra`. Use `haveI := C.isFractionRing`. Use `haveI := C.ded`. Use `haveI := C.iF_open`. Use `haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)`.

Use `haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := inferInstance`. Establish `hinj : Function.Injective (pullback.fst C.z (spMap C.b))` using `(pullback.fst C.z (spMap C.b)).isEmbedding.injective`. Take `⟨x, hx⟩` from `hg`. Set `φ : C.o →+* V` to `(Spec.preimage (g ≫ C.z)).hom`. Establish `hφ : spMap φ = g ≫ C.z` using `Spec.map_preimage _`.

Establish `hc : spMap φ (closedPoint V) = spMap C.b ((C.iF ≫ pullback.snd C.z (spMap C.b)) x)`. Rewrite using `[hφ]`. Use `(Scheme.Hom.comp_apply g C.z _).trans ((congrArg C.z hx.symm).trans ?_)` and prove the remaining obligations. Use `show C.z ((C.iF ≫ pullback.fst C.z (spMap C.b)) x) = _`. Rewrite using `[← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc]`.

Both sides reduce to the same expression. Establish `hunit : ∀ a : C.o, a ≠ 0 → IsUnit (φ a)`. Introduce `a ha`. Assume the negation of the conclusion as `hn`. Establish `hm : a ∈ (spMap φ (closedPoint V)).asIdeal` using `by show φ a ∈ (closedPoint V).asIdeal`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).2 hn`. Rewrite `hm` using `[hc]`. Use `haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).isPrime`. Establish `hb : C.b a ∈ ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal` using `hm`. Rewrite `hb` using `[Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal), Ideal.mem_bot]`.

Conclude with `ha (C.inj (hb.trans (map_zero C.b).symm))`. Set `ψ : c.F →+* V` to `IsLocalization.lift (M := nonZeroDivisors C.o) (S := c.F) (g := φ) (fun a => hunit a (nonZeroDivisors.ne_zero a.2))`. Establish `hψ : ψ.comp C.b = φ` using `RingHom.ext fun a => IsLocalization.lift_eq (M := nonZeroDivisors C.o) (S := c.F) _ a`. Establish `hsq : g ≫ C.z = spMap ψ ≫ spMap C.b`. Rewrite using `[← hφ, ← hψ]`.

Conclude with `GlobalTheory.UTraitPt.spMap_comp_eq _ _`. Set `g₁ : Sp V ⟶ pullback C.z (spMap C.b)` to `pullback.lift g (spMap ψ) hsq`. Establish `e1 : g₁ ≫ pullback.fst C.z (spMap C.b) = g` using `pullback.lift_fst _ _ _`. Establish `hx₁ : g₁ (closedPoint V) = C.iF x` using `hinj ((Scheme.Hom.comp_apply g₁ (pullback.fst C.z (spMap C.b)) _).symm.trans ((congrArg (fun h : Sp V ⟶ C.Z => h (closedPoint V)) e1).trans (hx.symm.trans (Scheme.Hom.comp_apply C.iF (pullback.fst C.z (spMap C.b)) x))))`. Establish `hr : Set.range g₁ ⊆ Set.range C.iF`.

Introduce and unpack `_ ⟨w, rfl⟩`. Establish `hs : g₁ w ⤳ g₁ (closedPoint V)` using `(IsLocalRing.specializes_closedPoint w).map g₁.continuous`. Rewrite `hs` using `[hx₁]`. Conclude with `hs.mem_open (IsOpenImmersion.isOpen_range C.iF) ⟨x, rfl⟩`. Use `⟨IsOpenImmersion.lift C.iF g₁ hr, ?_⟩` and prove the remaining obligations.

Use `show _ ≫ C.iF ≫ pullback.fst C.z (spMap C.b) = g`. Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]`.
-/
theorem lift_i_of_closedPoint (C : UCompact Xo c) (V : Type) [CommRing V] [IsLocalRing V] (g : Sp V ⟶ C.Z)
    (hg : g (closedPoint V) ∈ Set.range C.i) : ∃ σ : Sp V ⟶ Xo.XF c, σ ≫ C.i = g := by
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  haveI := C.iF_open
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := inferInstance
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) :=
    (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  obtain ⟨x, hx⟩ := hg
  let φ : C.o →+* V := (Spec.preimage (g ≫ C.z)).hom
  have hφ : spMap φ = g ≫ C.z := Spec.map_preimage _
  have hc : spMap φ (closedPoint V) = spMap C.b ((C.iF ≫ pullback.snd C.z (spMap C.b)) x) := by
    rw [hφ]
    refine (Scheme.Hom.comp_apply g C.z _).trans ((congrArg C.z hx.symm).trans ?_)
    show C.z ((C.iF ≫ pullback.fst C.z (spMap C.b)) x) = _
    rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc]
    rfl
  have hunit : ∀ a : C.o, a ≠ 0 → IsUnit (φ a) := by
    intro a ha
    by_contra hn
    have hm : a ∈ (spMap φ (closedPoint V)).asIdeal := by
      show φ a ∈ (closedPoint V).asIdeal
      exact (IsLocalRing.mem_maximalIdeal _).2 hn
    rw [hc] at hm
    haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).isPrime
    have hb : C.b a ∈ ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal := hm
    rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal), Ideal.mem_bot] at hb
    exact ha (C.inj (hb.trans (map_zero C.b).symm))
  let ψ : c.F →+* V := IsLocalization.lift (M := nonZeroDivisors C.o) (S := c.F) (g := φ)
    (fun a => hunit a (nonZeroDivisors.ne_zero a.2))
  have hψ : ψ.comp C.b = φ := RingHom.ext fun a => IsLocalization.lift_eq (M := nonZeroDivisors C.o) (S := c.F) _ a
  have hsq : g ≫ C.z = spMap ψ ≫ spMap C.b := by
    rw [← hφ, ← hψ]; exact GlobalTheory.UTraitPt.spMap_comp_eq _ _
  let g₁ : Sp V ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap ψ) hsq
  have e1 : g₁ ≫ pullback.fst C.z (spMap C.b) = g := pullback.lift_fst _ _ _
  have hx₁ : g₁ (closedPoint V) = C.iF x := hinj ((Scheme.Hom.comp_apply g₁ (pullback.fst C.z (spMap C.b)) _).symm.trans
    ((congrArg (fun h : Sp V ⟶ C.Z => h (closedPoint V)) e1).trans
      (hx.symm.trans (Scheme.Hom.comp_apply C.iF (pullback.fst C.z (spMap C.b)) x))))
  have hr : Set.range g₁ ⊆ Set.range C.iF := by
    rintro _ ⟨w, rfl⟩
    have hs : g₁ w ⤳ g₁ (closedPoint V) := (IsLocalRing.specializes_closedPoint w).map g₁.continuous
    rw [hx₁] at hs
    exact hs.mem_open (IsOpenImmersion.isOpen_range C.iF) ⟨x, rfl⟩
  refine ⟨IsOpenImmersion.lift C.iF g₁ hr, ?_⟩
  show _ ≫ C.iF ≫ pullback.fst C.z (spMap C.b) = g
  rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

/- English proof (translation)
Take `⟨hdvr, -, -⟩` from `T.cdvr`. Use `haveI := hdvr`. Take `⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩` from `T.gen`. Establish `hsemi` using `Xo.univ.t.semi`. Establish `hAb : IsAbelianScheme Xo.univ.t.G` using `{ comm := hsemi.comm, smooth := hsemi.smooth, proper := Xo.univ.proper, geomConnected := hsemi.geomConnected }`.

Set `f : Sp T.V ⟶ Xo.X` to `σ ≫ pullback.fst _ _`. Establish `hB` using `GlobalTheory.isAbelianScheme_pullback_obj f Xo.univ.t.G hAb`. Take `⟨e₁, he₁, -⟩` from `grpPullback_iso m₁.cart (isGrpPullback_pullback T.t.G (jK T.V))`. Establish `h₂` using `(isGrpPullback_pullback ((Over.pullback f).obj Xo.univ.t.G) (jK T.V)).comp (isGrpPullback_pullback Xo.univ.t.G f)`. Take `⟨e₂, he₂, -⟩` from `grpPullback_iso (m₂.cart.congr (by rw [← h, Category.assoc]) rfl) h₂`.

Use `haveI := he₁`. Use `haveI := he₂`. Take `⟨F, -, -⟩` from `GlobalTheory.Poinc.TraitUniq.extIso T.t.semi (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB) (e₁.symm ≪≫ e₂) (show IsMonHom (e₁.inv ≫ e₂.hom) from inferInstance)`. Establish `hp : IsProper T.t.G.hom`. Use `hB.proper` as an intermediate fact.

Establish `: IsIso F.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map F.hom))`. Rewrite using `[← Over.w F.hom]`. Use `infer_instance`. Conclude with `GlobalTheory.ChartNotAb.subsingleton_of_closed_mem_abLocus T.P (fun _ _ _ _ _ => inferInstance)`.
-/
theorem subsingleton_of_extends (T : UTrait Xo c) (σ : Sp T.V ⟶ Xo.XF c) (h : jK T.V ≫ σ = T.y) :
    Subsingleton T.P.D.toPre.X := by
  obtain ⟨hdvr, -, -⟩ := T.cdvr
  haveI := hdvr
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  have hsemi := Xo.univ.t.semi
  have hAb : IsAbelianScheme Xo.univ.t.G :=
    { comm := hsemi.comm, smooth := hsemi.smooth, proper := Xo.univ.proper, geomConnected := hsemi.geomConnected }
  let f : Sp T.V ⟶ Xo.X := σ ≫ pullback.fst _ _
  have hB := GlobalTheory.isAbelianScheme_pullback_obj f Xo.univ.t.G hAb
  obtain ⟨e₁, he₁, -⟩ := grpPullback_iso m₁.cart (isGrpPullback_pullback T.t.G (jK T.V))
  have h₂ := (isGrpPullback_pullback ((Over.pullback f).obj Xo.univ.t.G) (jK T.V)).comp
    (isGrpPullback_pullback Xo.univ.t.G f)
  obtain ⟨e₂, he₂, -⟩ := grpPullback_iso (m₂.cart.congr (by rw [← h, Category.assoc]) rfl) h₂
  haveI := he₁
  haveI := he₂
  obtain ⟨F, -, -⟩ := GlobalTheory.Poinc.TraitUniq.extIso T.t.semi (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB) (e₁.symm ≪≫ e₂)
    (show IsMonHom (e₁.inv ≫ e₂.hom) from inferInstance)
  have hp : IsProper T.t.G.hom := by
    have := hB.proper
    have : IsIso F.hom.left := inferInstanceAs (IsIso ((Over.forget _).map F.hom))
    rw [← Over.w F.hom]
    infer_instance
  exact GlobalTheory.ChartNotAb.subsingleton_of_closed_mem_abLocus T.P (fun _ _ _ _ _ => inferInstance)

end GlobalTheory.UPoinc.SuppTrait

open GlobalTheory.UPoinc.SuppTrait in

/- English proof (translation)
Introduce `E _ _ _ H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hhom ι D hoff hord y hy hC`. Take `⟨T, ξ, γ, hcen, hgen, hTy⟩` from `exists_uTrait_centre Y X₁.uΩ y`. Establish `hU₀ : Set.range Y.pt ⊆ Set.range U₀.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨w, rfl⟩`.

Conclude with `Y.top_le_preimage_pt hAdm.1.ne (x := w) trivial`. Establish `hthru : ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y`. Use `⟨spMap γ ≫ IsOpenImmersion.lift U₀.ι Y.pt hU₀, by rw [Category.assoc, IsOpenImmersion.lift_fac, hgen], ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, out.u₀_gen _ (IsOpenImmersion.lift_fac _ _ _)]`. Take `⟨x', hx', hu⟩` from `X₁.lies_uΩ`.

Conclude with `⟨spMap γ ≫ x', by rw [Category.assoc, hx'], by rw [Category.assoc, hu, hTy]⟩`. Take `⟨a, ha, hJ⟩` from `hord T ξ hthru`. Establish `hpt : Y.pt ≫ πY ≫ X₁.π = X₁.uΩ ≫ C.i`. Establish `h : Y.pt ≫ πY = X₁.M.pt` using `hhom.trans (by`. Rewrite using `[show spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom = 𝟙 _ from Spec.map_id _, Category.id_comp])`.

Rewrite using `[← Category.assoc, h, X₁.comp, Category.assoc]`. Establish `hsq : jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ C.i`. Rewrite using `[← Category.assoc, hgen, Category.assoc, hpt, hTy]`. Simplify using `only [USetup.uΩ, Category.assoc]`. Take `⟨σ, hσ⟩` from `lift_i_of_closedPoint C T.V (ξ ≫ πY ≫ X₁.π) (by show X₁.π (πY (ξ (closedPoint T.V))) ∈ _`.

Rewrite using `[hcen]`. Conclude with `hC)`. Use `haveI := C.isPreimmersion_i`. Establish `hσ' : jK T.V ≫ σ = T.y`. Rewrite using `[← cancel_mono C.i, Category.assoc, hσ, hsq]`.

Use `haveI := subsingleton_of_extends T σ hσ'`. Establish `ha0 : a = 0`. Rewrite `ha` using `[InvFun.evalZ, InvFun.eval_of_subsingleton, mul_zero]`. Conclude with `ha` after adjusting the coercions. Substitute `ha0` using the available equality.

Rewrite `hJ` using `[pow_zero, Ideal.span_singleton_one]`. Establish `htop : FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V)) = ⊤`. Assume the negation of the conclusion as `h`. Establish `hle : (FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V))).map (Scheme.stalkClosedPointTo ξ).hom ≤ maximalIdeal T.V` using `Ideal.map_le_iff_le_comap.2 fun b hb => (map_mem_nonunits_iff _ b).2 (IsLocalRing.le_maximalIdeal h hb)`. Establish `hle' : idlAlong D.idealSheaf ξ ≤ maximalIdeal T.V` using `hle`.

Rewrite `hle'` using `[hJ]`. Conclude with `(maximalIdeal.isMaximal T.V).ne_top (top_le_iff.1 hle')`. Conclude with `(mem_support_iff_stalkId _ y).1 hy (hcen ▸ htop)`.
-/
theorem GlobalTheory.UPoinc.SuppTrait.support_not_mem_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (ι : ℕ) (D : GlobalTheory.EffCartierData Y.Z), (∀ y ∈ D.idealSheaf.support, y ∉ U₀) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hhom ι D hoff hord y hy hC
  obtain ⟨T, ξ, γ, hcen, hgen, hTy⟩ := exists_uTrait_centre Y X₁.uΩ y
  have hU₀ : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact Y.top_le_preimage_pt hAdm.1.ne (x := w) trivial
  have hthru : ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y := by
    refine ⟨spMap γ ≫ IsOpenImmersion.lift U₀.ι Y.pt hU₀, by rw [Category.assoc, IsOpenImmersion.lift_fac, hgen], ?_⟩
    rw [Category.assoc, out.u₀_gen _ (IsOpenImmersion.lift_fac _ _ _)]
    obtain ⟨x', hx', hu⟩ := X₁.lies_uΩ
    exact ⟨spMap γ ≫ x', by rw [Category.assoc, hx'], by rw [Category.assoc, hu, hTy]⟩
  obtain ⟨a, ha, hJ⟩ := hord T ξ hthru
  have hpt : Y.pt ≫ πY ≫ X₁.π = X₁.uΩ ≫ C.i := by
    have h : Y.pt ≫ πY = X₁.M.pt := hhom.trans (by
      rw [show spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom = 𝟙 _ from Spec.map_id _, Category.id_comp])
    rw [← Category.assoc, h, X₁.comp, Category.assoc]
  have hsq : jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ C.i := by
    rw [← Category.assoc, hgen, Category.assoc, hpt, hTy]
    simp only [USetup.uΩ, Category.assoc]
  obtain ⟨σ, hσ⟩ := lift_i_of_closedPoint C T.V (ξ ≫ πY ≫ X₁.π) (by
    show X₁.π (πY (ξ (closedPoint T.V))) ∈ _
    rw [hcen]; exact hC)
  haveI := C.isPreimmersion_i
  have hσ' : jK T.V ≫ σ = T.y := by
    rw [← cancel_mono C.i, Category.assoc, hσ, hsq]
  haveI := subsingleton_of_extends T σ hσ'
  have ha0 : a = 0 := by
    rw [InvFun.evalZ, InvFun.eval_of_subsingleton, mul_zero] at ha
    exact_mod_cast ha
  subst ha0
  rw [pow_zero, Ideal.span_singleton_one] at hJ
  have htop : FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V)) = ⊤ := by
    by_contra h
    have hle : (FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V))).map (Scheme.stalkClosedPointTo ξ).hom ≤
        maximalIdeal T.V := Ideal.map_le_iff_le_comap.2 fun b hb =>
          (map_mem_nonunits_iff _ b).2 (IsLocalRing.le_maximalIdeal h hb)
    have hle' : idlAlong D.idealSheaf ξ ≤ maximalIdeal T.V := hle
    rw [hJ] at hle'
    exact (maximalIdeal.isMaximal T.V).ne_top (top_le_iff.1 hle')
  exact (mem_support_iff_stalkId _ y).1 hy (hcen ▸ htop)
