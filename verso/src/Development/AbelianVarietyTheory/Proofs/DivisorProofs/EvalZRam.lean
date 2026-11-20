import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtPointLiftOfSurjectiveLocFinType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrIntegralClosureFiniteFractionRi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapEqSpanPowUniformizerDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTrait
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.LiftOrd

/- English proof (translation)
Take `⟨hdvr, hcpl, hz⟩` from `T'.cdvr`. Establish `hB : GlobalTheory.Mum.Base T'.V` using `⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hz⟩`. Establish `hself : Associated (RingHom.id T'.V T'.ϖ) (T'.ϖ ^ 1)` using `by simp [Associated.refl]`. Establish `hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _` using `Spec.map_id _`. Take `⟨e, he⟩` from `GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices E H Dw l Xo c T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB hdvr hf Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm hself`.

Establish `hon : IsPolFanOn H.bar φ T.P.D.toPre.X` using `by haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X`. Conclude with `hφ _ (GlobalTheory.UPoinc.UTrait.finrank_le_min E H Dw l Xo c T)`. Establish `hc : toReal T.be ∈ psdCone H.bar T.P.D.toPre.X` using `GlobalTheory.PolFan.StrictData.toReal_mem_psdCone ((balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev) fun y => by simpa using T.mono.nonneg 0 y`. Rewrite using `[← evalR_toReal φ T.be, ← hon.homog _ hc m m.cast_nonneg, ← evalZ_pull φ (r := e.toLinearMap) e.surjective, ← evalR_toReal]`. Use `congr 1`.

Use `LinearMap.ext₂ fun a b => ?_` and prove the remaining obligations. Establish `h` using `he a b`. Rewrite `h` using `[Nat.cast_one, one_mul]`. Simplify using `only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `h.symm` after adjusting the coercions.
-/
theorem evalZ_ram {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V)
    (hf : Function.Injective f) (hl : IsLocalHom f)
    (hK : ∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a))
    (hy : T'.y = spMap fK ≫ T.y) (m : ℕ) (hm : Associated (f T.ϖ) (T'.ϖ ^ m)) (φ : InvFun (𝓞 E))
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) : φ.evalZ T'.be = m * φ.evalZ T.be := by
  obtain ⟨hdvr, hcpl, hz⟩ := T'.cdvr
  have hB : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hz⟩
  have hself : Associated (RingHom.id T'.V T'.ϖ) (T'.ϖ ^ 1) := by simp [Associated.refl]
  have hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ := Spec.map_id _
  obtain ⟨e, he⟩ := GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices E H Dw l Xo c T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB hdvr hf
    Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm
    hself
  have hon : IsPolFanOn H.bar φ T.P.D.toPre.X := by
    haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X
    exact hφ _ (GlobalTheory.UPoinc.UTrait.finrank_le_min E H Dw l Xo c T)
  have hc : toReal T.be ∈ psdCone H.bar T.P.D.toPre.X :=
    GlobalTheory.PolFan.StrictData.toReal_mem_psdCone ((balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev)
      fun y => by simpa using T.mono.nonneg 0 y
  rw [← evalR_toReal φ T.be, ← hon.homog _ hc m m.cast_nonneg,
    ← evalZ_pull φ (r := e.toLinearMap) e.surjective, ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  rw [Nat.cast_one, one_mul] at h
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

end GlobalTheory.UPoinc.LiftOrd

/- English proof (translation)
Introduce `E _ _ _ H Dw hpq φ hφ l Xo c C X₁ Y πY hhom hprop ι J₁ hsupp hval`. Use `haveI := hprop`. Establish `hsurj : Function.Surjective πY`. Establish `hgen : genericPoint X₁.M.Z ∈ Set.range πY`. Establish `w : Sp X₁.Ω₁` using `IsLocalRing.closedPoint X₁.Ω₁`.

Use `⟨Y.pt w, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun h : Sp X₁.Ω₁ ⟶ X₁.M.Z => h w) (show Y.pt ≫ πY = _ from hhom)`. Simplify using `only [Scheme.Hom.comp_apply] at h`. Rewrite using `[h]`. Conclude with `X₁.M.pt_apply _`.

Establish `hcl : IsClosed (Set.range πY)` using `πY.isClosedMap.isClosed_range`. Introduce `x`. Establish `: x ∈ closure (Set.range πY)` using `closure_mono (Set.singleton_subset_iff.2 hgen) (by rw [genericPoint_spec X₁.M.Z]; trivial)`. Rewrite `this` using `[hcl.closure_eq]`. Then use the resulting hypothesis. Use `⟨fun x hx => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `hsurj x`. Conclude with `hsupp y (by rw [Scheme.IdealSheafData.support_comap]; exact hx)`. Introduce `W _ _ _ hW ϖ hϖ χ y hy _ t tK h1 h2 P be hbe hmono`. Set `T : UTrait Xo c` to `⟨W, hW, ϖ, hϖ, y, t, ⟨tK, h1, h2⟩, P, be, hbe, hmono⟩`. Take `⟨hdvr, hcpl, hz⟩` from `hW`.

Use `haveI := hdvr`. Use `haveI := hz`. Take `⟨K', _, σ, yK, hσ, hyK⟩` from `GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft πY inferInstance hsurj (FractionRing W) (jK W ≫ χ)`. Take `⟨V', _, _, _, _, f, τ, hc', hfi, hfl, hff, hτ⟩` from `GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom W hcpl K' σ hσ`. Establish `hfK : ∀ a, (τ.comp σ) (algebraMap W _ a) = algebraMap V' _ (f a)` using `hτ`.

Take `⟨ξ', hξπ, hξg⟩` from `GlobalTheory.proper_lift_trait πY hprop W V' f (τ.comp σ) hfK χ (spMap τ ≫ yK) (by`. Rewrite using `[Category.assoc, hyK, spMap_comp, Category.assoc])`. Establish `hB' : GlobalTheory.Mum.Base V'` using `⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩`. Take `⟨T₂, f₂, fK₂, hf₂i, hf₂l, -, hf₂K, hT₂y⟩` from `GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V' hB' inferInstance (spMap (τ.comp σ) ≫ y)`. Use `haveI := hfl`.

Use `haveI := hf₂l`. Establish `hjK : ∀ {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (u : R →+* S) (uK : FractionRing R →+* FractionRing S), (∀ a, uK (algebraMap R _ a) = algebraMap S _ (u a)) → jK S ≫ spMap u = spMap uK ≫ jK R`. Introduce `R S _ _ _ _ u uK hu`. Express the relevant statement in the definitionally equal form `spMap (algebraMap S (FractionRing S)) ≫ spMap u = spMap uK ≫ spMap (algebraMap R (FractionRing R))`. Rewrite using `[← spMap_comp, ← spMap_comp]`.

Conclude with `congrArg spMap (RingHom.ext fun a => (hu a).symm)`. Establish `hcomm : T₂.y ≫ C.i = jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π`. Establish `e1` using `hjK f₂ fK₂ hf₂K`. Use `symm`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Category.assoc]`. Use `_ = spMap fK₂ ≫ (jK V' ≫ ξ') ≫ πY ≫ X₁.π := by rw [e1]; simp only [Category.assoc]`. Use `_ = spMap fK₂ ≫ spMap τ ≫ (yK ≫ πY) ≫ X₁.π := by rw [hξg]; simp only [Category.assoc]`. Use `_ = spMap fK₂ ≫ spMap τ ≫ spMap σ ≫ (jK W ≫ χ ≫ X₁.π) := by rw [hyK]; simp only [Category.assoc]`. Use `_ = T₂.y ≫ C.i := by rw [← hy, hT₂y, spMap_comp]; simp only [Category.assoc]`.

Take `⟨tK₂, m₁, m₂⟩` from `T₂.gen`. Take `⟨a', ha', hid⟩` from `hval T₂.V T₂.cdvr T₂.ϖ T₂.irr (spMap f₂ ≫ ξ') T₂.y hcomm trivial T₂.t tK₂ m₁ m₂ T₂.P T₂.be T₂.lev T₂.mono`. Rewrite `hid` using `[GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc, hξπ, ← Category.assoc, ← spMap_comp, GlobalTheory.TraitOrder.idlAlong_comp]`. Use `set h := f₂.comp f with hh`. Establish `hinj : Function.Injective h` using `hf₂i.comp hfi`.

Establish `hloc : IsLocalHom h` using `inferInstance`. Take `⟨hdvr₂, -, -⟩` from `T₂.cdvr`. Use `haveI := hdvr₂`. Establish `hne : h ϖ ≠ 0` using `(map_ne_zero_iff h hinj).2 hϖ.ne_zero`. Take `⟨e, he⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hne T₂.irr`.

Establish `he1 : 1 ≤ e`. Break down `Nat.eq_zero_or_pos e with rfl | hpos` into its components or cases. Conclude with `absurd ((isUnit_map_iff h ϖ).1 (he.isUnit_iff.2 (by simp))) hϖ.not_isUnit`. Conclude with `hpos`. Take `⟨b, hb, hI⟩` from `GlobalTheory.ideal_map_eq_span_pow_uniformizer W T₂.V h hinj ϖ T₂.ϖ e a' _ hϖ T₂.irr he hid`.

Apply the tactic sequence `have hval2 : φ.evalZ T₂.be = e * φ.evalZ be := GlobalTheory.UPoinc.LiftOrd.evalZ_ram T T₂ h (fK₂.comp (τ.comp σ)) hinj hloc (fun a => by rw [RingHom.comp_apply, hfK, hf₂K]; rfl) (by rw [hT₂y]; simp only [spMap_comp, Category.assoc]; first | rfl | skip) e he φ hφ`. Use `⟨b, ?_, hI⟩` and prove the remaining obligations. Establish `h1 : (e : ℝ) * b = e * (ι * φ.evalZ be)`. Rewrite using `[← Nat.cast_mul, hb, ha', hval2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : (e : ℝ) ≠ 0` using `by exact_mod_cast (by omega : e ≠ 0)`. Conclude with `mul_left_cancel₀ h2 h1`.
-/
theorem _root_.GlobalTheory.UPoinc.ideal_orders_of_proper_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ∀ (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range C.i) → UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ (J₁.comap πY) ι → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) ∧ UValThru Xo c C.i X₁.π Set.univ φ J₁ ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ Y πY hhom hprop ι J₁ hsupp hval
  haveI := hprop
  have hsurj : Function.Surjective πY := by
    have hgen : genericPoint X₁.M.Z ∈ Set.range πY := by
      have w : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
      refine ⟨Y.pt w, ?_⟩
      have h := congrArg (fun h : Sp X₁.Ω₁ ⟶ X₁.M.Z => h w) (show Y.pt ≫ πY = _ from hhom)
      simp only [Scheme.Hom.comp_apply] at h
      rw [h]
      exact X₁.M.pt_apply _
    have hcl : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
    intro x
    have : x ∈ closure (Set.range πY) :=
      closure_mono (Set.singleton_subset_iff.2 hgen) (by rw [genericPoint_spec X₁.M.Z]; trivial)
    rwa [hcl.closure_eq] at this
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hsurj x
    exact hsupp y (by rw [Scheme.IdealSheafData.support_comap]; exact hx)
  intro W _ _ _ hW ϖ hϖ χ y hy _ t tK h1 h2 P be hbe hmono
  let T : UTrait Xo c := ⟨W, hW, ϖ, hϖ, y, t, ⟨tK, h1, h2⟩, P, be, hbe, hmono⟩
  obtain ⟨hdvr, hcpl, hz⟩ := hW
  haveI := hdvr
  haveI := hz

  obtain ⟨K', _, σ, yK, hσ, hyK⟩ := GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft πY inferInstance hsurj
    (FractionRing W) (jK W ≫ χ)
  obtain ⟨V', _, _, _, _, f, τ, hc', hfi, hfl, hff, hτ⟩ :=
    GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom W hcpl K' σ hσ
  have hfK : ∀ a, (τ.comp σ) (algebraMap W _ a) = algebraMap V' _ (f a) := hτ
  obtain ⟨ξ', hξπ, hξg⟩ := GlobalTheory.proper_lift_trait πY hprop W V' f (τ.comp σ) hfK χ (spMap τ ≫ yK) (by
    rw [Category.assoc, hyK, spMap_comp, Category.assoc])
  have hB' : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hf₂i, hf₂l, -, hf₂K, hT₂y⟩ :=
    GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V' hB' inferInstance (spMap (τ.comp σ) ≫ y)
  haveI := hfl
  haveI := hf₂l
  have hjK : ∀ {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (u : R →+* S)
      (uK : FractionRing R →+* FractionRing S), (∀ a, uK (algebraMap R _ a) = algebraMap S _ (u a)) →
      jK S ≫ spMap u = spMap uK ≫ jK R := by
    intro R S _ _ _ _ u uK hu
    change spMap (algebraMap S (FractionRing S)) ≫ spMap u = spMap uK ≫ spMap (algebraMap R (FractionRing R))
    rw [← spMap_comp, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun a => (hu a).symm)

  have hcomm : T₂.y ≫ C.i = jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π := by
    have e1 := hjK f₂ fK₂ hf₂K
    symm
    calc jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ ξ' ≫ πY ≫ X₁.π := by
          simp only [Category.assoc]
      _ = spMap fK₂ ≫ (jK V' ≫ ξ') ≫ πY ≫ X₁.π := by rw [e1]; simp only [Category.assoc]
      _ = spMap fK₂ ≫ spMap τ ≫ (yK ≫ πY) ≫ X₁.π := by rw [hξg]; simp only [Category.assoc]
      _ = spMap fK₂ ≫ spMap τ ≫ spMap σ ≫ (jK W ≫ χ ≫ X₁.π) := by rw [hyK]; simp only [Category.assoc]
      _ = T₂.y ≫ C.i := by rw [← hy, hT₂y, spMap_comp]; simp only [Category.assoc]
  obtain ⟨tK₂, m₁, m₂⟩ := T₂.gen
  obtain ⟨a', ha', hid⟩ := hval T₂.V T₂.cdvr T₂.ϖ T₂.irr (spMap f₂ ≫ ξ') T₂.y hcomm trivial T₂.t tK₂ m₁ m₂ T₂.P T₂.be
    T₂.lev T₂.mono
  rw [GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc, hξπ, ← Category.assoc, ← spMap_comp,
    GlobalTheory.TraitOrder.idlAlong_comp] at hid

  set h := f₂.comp f with hh
  have hinj : Function.Injective h := hf₂i.comp hfi
  have hloc : IsLocalHom h := inferInstance
  obtain ⟨hdvr₂, -, -⟩ := T₂.cdvr
  haveI := hdvr₂
  have hne : h ϖ ≠ 0 := (map_ne_zero_iff h hinj).2 hϖ.ne_zero
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T₂.irr
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exact absurd ((isUnit_map_iff h ϖ).1 (he.isUnit_iff.2 (by simp))) hϖ.not_isUnit
    · exact hpos
  obtain ⟨b, hb, hI⟩ := GlobalTheory.ideal_map_eq_span_pow_uniformizer W T₂.V h hinj ϖ T₂.ϖ e a' _ hϖ T₂.irr he hid
  have hval2 : φ.evalZ T₂.be = e * φ.evalZ be :=
    GlobalTheory.UPoinc.LiftOrd.evalZ_ram T T₂ h (fK₂.comp (τ.comp σ)) hinj hloc
      (fun a => by rw [RingHom.comp_apply, hfK, hf₂K]; rfl) (by rw [hT₂y]; simp only [spMap_comp, Category.assoc]; first | rfl | skip) e he φ hφ
  refine ⟨b, ?_, hI⟩
  have h1 : (e : ℝ) * b = e * (ι * φ.evalZ be) := by
    rw [← Nat.cast_mul, hb, ha', hval2]; ring
  have h2 : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  exact mul_left_cancel₀ h2 h1
