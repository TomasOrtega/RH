import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSeparableCompositum
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFibrewiseThetaOfOpenImmersionCover
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Models
open scoped CategoryTheory.Obj

namespace GlobalTheory.GlobalClauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Use `haveI := c.fin`. Use `haveI : NumberField c.F := {}`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal ((IsLocalRing.maximalIdeal R).comap φ) (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top)`. Establish `hm0 : m ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField _)`. Use `haveI : Finite (𝓞 c.F ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm0`.

Take `⟨p, hchar⟩` from `CharP.exists (𝓞 c.F ⧸ m)`. Establish `hp : p.Prime` using `CharP.char_is_prime (𝓞 c.F ⧸ m) p`. Establish `hpm : (p : 𝓞 c.F) ∈ m`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero]`. Set `ι : 𝓞 c.F →+* ℂ` to `c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)`.

Establish `hι : Function.Injective ι` using `Subtype.val_injective.comp (RingOfIntegers.coe_injective)`. Establish `hbij : Function.Bijective ι.rangeRestrict` using `⟨fun a b h => hι (congrArg (fun z : ι.range => (z : ℂ)) h), ι.rangeRestrict_surjective⟩`. Establish `hne : m.map ι.rangeRestrict ≠ ⊤` using `(Ideal.map_isMaximal_of_equiv (RingEquiv.ofBijective _ hbij) (p := m)).ne_top`. Take `⟨W, -, hW⟩` from `Ideal.image_subset_nonunits_valuationSubring _ hne`. Establish `hnon : ∀ x ∈ m, ι x ∈ W.nonunits` using `fun x hx => hW ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩`.

Establish `hpW : (p : ℂ) ∈ W.nonunits` using `map_natCast ι p ▸ hnon _ hpm`. Take `⟨b, hb, -⟩` from `GlobalModelGuards.exists_incl c W`. Take `⟨v, -, hv⟩` from `GlobalModelGuards.exists_prime_eq c W p hp hpW`. Use `haveI hl : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) := Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors`. Establish `hu : ∀ s : v.asIdeal.primeCompl, IsUnit (φ s)`.

Introduce `s`. Assume the negation of the conclusion as `h`. Establish `h1` using `hnon _ (hle (show (s : 𝓞 c.F) ∈ (IsLocalRing.maximalIdeal R).comap φ from h))`. Take `⟨u, hu⟩` from `(IsLocalization.map_units (v.valuationSubringAtPrime c.F) s).exists_right_inv`. Establish `h2 : ((u : c.F) : ℂ) ∈ W` using `(hv ▸ u.2 : (u : c.F) ∈ c.V W)`.

Establish `h3 : ι s * ((u : c.F) : ℂ) = 1` using `congrArg (fun z : v.valuationSubringAtPrime c.F => ((z : c.F) : ℂ)) hu`. Rewrite `h1` using `[ValuationSubring.mem_nonunits_iff]`. Establish `h4` using `congrArg W.valuation h3`. Rewrite `h4` using `[map_mul, map_one]`. Conclude with `(mul_lt_one_of_lt_of_le h1 ((W.valuation_le_one_iff _).2 h2)).ne h4`.

Use `⟨p, W, hp, hpW, b, (IsLocalization.lift (S := v.valuationSubringAtPrime c.F) hu).comp (ValuationSubring.inclusion _ _ hv.ge), hb, RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Establish `e : ValuationSubring.inclusion _ _ hv.ge (b x) = algebraMap _ (v.valuationSubringAtPrime c.F) x` using `Subtype.ext (hb x)`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, e, IsLocalization.lift_eq]`.
-/
theorem exists_factor {l : Level H} (c : Coeff l) {R : Type} [CommRing R] [IsLocalRing R] (φ : 𝓞 c.F →+* R) :
    ∃ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W)
      (ψ : c.V W →+* R), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) ∧ ψ.comp b = φ := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal ((IsLocalRing.maximalIdeal R).comap φ)
    (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top)
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField _)
  haveI : Finite (𝓞 c.F ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm0
  obtain ⟨p, hchar⟩ := CharP.exists (𝓞 c.F ⧸ m)
  have hp : p.Prime := CharP.char_is_prime (𝓞 c.F ⧸ m) p
  have hpm : (p : 𝓞 c.F) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero]
  let ι : 𝓞 c.F →+* ℂ := c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)
  have hι : Function.Injective ι := Subtype.val_injective.comp (RingOfIntegers.coe_injective)
  have hbij : Function.Bijective ι.rangeRestrict :=
    ⟨fun a b h => hι (congrArg (fun z : ι.range => (z : ℂ)) h), ι.rangeRestrict_surjective⟩
  have hne : m.map ι.rangeRestrict ≠ ⊤ := (Ideal.map_isMaximal_of_equiv (RingEquiv.ofBijective _ hbij) (p := m)).ne_top
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  have hnon : ∀ x ∈ m, ι x ∈ W.nonunits := fun x hx => hW ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩
  have hpW : (p : ℂ) ∈ W.nonunits := map_natCast ι p ▸ hnon _ hpm
  obtain ⟨b, hb, -⟩ := GlobalModelGuards.exists_incl c W
  obtain ⟨v, -, hv⟩ := GlobalModelGuards.exists_prime_eq c W p hp hpW
  haveI hl : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) :=
    Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  have hu : ∀ s : v.asIdeal.primeCompl, IsUnit (φ s) := by
    intro s
    by_contra h
    have h1 := hnon _ (hle (show (s : 𝓞 c.F) ∈ (IsLocalRing.maximalIdeal R).comap φ from h))
    obtain ⟨u, hu⟩ := (IsLocalization.map_units (v.valuationSubringAtPrime c.F) s).exists_right_inv
    have h2 : ((u : c.F) : ℂ) ∈ W := (hv ▸ u.2 : (u : c.F) ∈ c.V W)
    have h3 : ι s * ((u : c.F) : ℂ) = 1 := congrArg (fun z : v.valuationSubringAtPrime c.F => ((z : c.F) : ℂ)) hu
    rw [ValuationSubring.mem_nonunits_iff] at h1
    have h4 := congrArg W.valuation h3
    rw [map_mul, map_one] at h4
    exact (mul_lt_one_of_lt_of_le h1 ((W.valuation_le_one_iff _).2 h2)).ne h4
  refine ⟨p, W, hp, hpW, b, (IsLocalization.lift (S := v.valuationSubringAtPrime c.F) hu).comp
    (ValuationSubring.inclusion _ _ hv.ge), hb, RingHom.ext fun x => ?_⟩
  have e : ValuationSubring.inclusion _ _ hv.ge (b x) = algebraMap _ (v.valuationSubringAtPrime c.F) x :=
    Subtype.ext (hb x)
  rw [RingHom.comp_apply, RingHom.comp_apply, e, IsLocalization.lift_eq]

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {s : Sys Xo} {l : Level H} {c : Coeff l}
  {hg : ∀ p : ℕ, p.Prime → l.GoodAt p} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)}

/- English proof (translation)
Take `⟨φ, hφ⟩ : ∃ φ : 𝓞 c.F →+* R, spMap φ = ξ ≫ Y.s` from `⟨(Spec.preimage (ξ ≫ Y.s)).hom, Spec.map_preimage _⟩`. Take `⟨p, W, hp, hW, b, ψ, hb, rfl⟩` from `exists_factor c φ`. Take `⟨f, t₁, m₁, m₂, -⟩` from `h.2.1 p W hp hW b hb`. Take `⟨ξ₁, rfl⟩ : ∃ ξ₁ : Sp R ⟶ pullback Y.s (spMap b), ξ₁ ≫ pullback.fst _ _ = ξ` from `⟨pullback.lift ξ (spMap ψ) (hφ.symm.trans (spMap_comp _ _)), pullback.lift_fst _ _ _⟩`. Take `⟨m', -⟩` from `ObjMaps.exists_sab_cancel m₁ m`.

Take `⟨n, -⟩` from `ObjMaps.exists_sab_comp m₂ m'`. Conclude with `⟨p, W, hp, hW, _, ⟨n⟩⟩`.
-/
theorem exists_local_point (h : IsGlob s.Y hg Y) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X)
    (t : SAB H (Sp R)) (m : SABMap t Y.t ξ) :
    ∃ p W hp hW, ∃ ξ' : Sp R ⟶ (s.Y p W hp hW ⟨l, c, hg p hp⟩).X,
      Nonempty (SABMap t (s.Y p W hp hW ⟨l, c, hg p hp⟩).t ξ') := by
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓞 c.F →+* R, spMap φ = ξ ≫ Y.s := ⟨(Spec.preimage (ξ ≫ Y.s)).hom, Spec.map_preimage _⟩
  obtain ⟨p, W, hp, hW, b, ψ, hb, rfl⟩ := exists_factor c φ
  obtain ⟨f, t₁, m₁, m₂, -⟩ := h.2.1 p W hp hW b hb
  obtain ⟨ξ₁, rfl⟩ : ∃ ξ₁ : Sp R ⟶ pullback Y.s (spMap b), ξ₁ ≫ pullback.fst _ _ = ξ :=
    ⟨pullback.lift ξ (spMap ψ) (hφ.symm.trans (spMap_comp _ _)), pullback.lift_fst _ _ _⟩
  obtain ⟨m', -⟩ := ObjMaps.exists_sab_cancel m₁ m
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp m₂ m'
  exact ⟨p, W, hp, hW, _, ⟨n⟩⟩

/- English proof (translation)
Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial`. Set `ι` to `pullback.fst G.hom hU.fromSpec`.

Set `f` to `pullback.snd G.hom hU.fromSpec`. Establish `hξ : Spec.map (X.presheaf.germ U x hx) ≫ hU.fromSpec = X.fromSpecStalk x` using `hU.fromSpecStalk_eq_fromSpecStalk hx`. Set `π : G'.left ⟶ pullback G.hom hU.fromSpec` to `pullback.lift φ (G'.hom ≫ Spec.map (X.presheaf.germ U x hx)) (by rw [Category.assoc, hξ, hφ.w])`. Establish `hπ : π ≫ ι = φ` using `pullback.lift_fst _ _ _`. Establish `hP : IsPullback π G'.hom f (Spec.map (X.presheaf.germ U x hx))` using `IsPullback.of_right (by rw [hπ, hξ]; exact hφ) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)`.

Establish `: CompactSpace (pullback G.hom hU.fromSpec : Scheme.{0})` using `QuasiCompact.compactSpace_of_compactSpace f`. Establish `: QuasiSeparatedSpace (pullback G.hom hU.fromSpec : Scheme.{0})` using `quasiSeparatedSpace_of_quasiSeparated f`. Establish `hflat : (X.presheaf.germ U x hx).hom.Flat`. Use `letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)`. Use `hU.isLocalization_stalk ⟨x, hx⟩` as an intermediate fact.

Conclude with `RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)`. Establish `hM` using `pull_isLB hL ι`. Take `⟨w, hw'⟩ : LBIso ((L.pull ι).pull π) (L'.pull (𝟙 _))` from `LBIso.chartPull (chartPullLinComb L ι (fun _ : PUnit => π) (fun _ => φ) (fun _ => 1) (𝟙 _) fun _ => hπ.trans (Category.id_comp _).symm) (Geo.Tor.chartPullPull L' _ _ rfl) hw.symm`. Take `⟨θ', hθ'⟩` from `hθ`. Take `⟨σ, hσ⟩` from `ThetaLocal.exists_sec_pull hL' (pull_isLB hM π) (𝟙 _) w hw' (O := ⊤) le_top _ (SecSpread.res_mem_secOn θ' ⊤)`.

Take `⟨z, i, hz, hi⟩` from `hθ' (IsLocalRing.closedPoint _)`. Take `⟨k, hk⟩` from `hσ z i ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, G'.left.basicOpen_le _ hi⟩, hi⟩)`. Take `⟨k, rfl⟩ : ∃ j, k = fun _ => j` from `⟨k PUnit.unit, rfl⟩`. Establish `hk₁` using `G'.left.basicOpen_le _ hk`. Establish `hk₂ : π z ∈ (L.pull ι).U k` using `mem_pull.1 hk₁`.

Take `⟨n, a, u, hu⟩` from `FlatSec.exists_comb_of_flat _ _ _ hflat _ f _ π G'.hom hP _ hM σ`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, π z ∈ Scheme.basicOpen _ ((u j).f k) := by`. Assume the negation of the conclusion as `hn`. Establish `h₁` using `(AbLocusPull.isUnit_gs_iff (𝟙 _) z _ hk₁ _).2 hk`. Rewrite `h₁` using `[hu z k hk₂]`.

Use `(IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_) h₁` and prove the remaining obligations. Conclude with `fun h₂ => hn ⟨j, (AbLocusPull.isUnit_gs_iff π z _ hk₂ _).1 h₂⟩`. Set `V : X.Opens` to `⟨(ι ≫ G.hom) '' Scheme.basicOpen _ ((u j).f k), (ι ≫ G.hom).isOpenMap _ (Scheme.basicOpen _ ((u j).f k)).isOpen⟩`. Establish `hr : G.hom ⁻¹ᵁ V ≤ ι.opensRange`. Introduce and unpack `g ⟨y, -, e⟩`.

Take `⟨q, hq, -⟩` from `Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback G.hom hU.fromSpec) g (f y) (e.symm.trans (congrArg (fun r : pullback G.hom hU.fromSpec ⟶ X => r y) pullback.condition))`. Conclude with `⟨q, hq⟩`. Take `⟨θ, hθ, hb⟩` from `ThetaLocal.exists_secOn_push hL hM (lbIso_refl hM) hr le_top (SecSpread.res_mem_secOn (u j) ⊤)`. Use `⟨V, ⟨π z, hj, ?_⟩, θ, hθ, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Category.assoc, hπ, hφ.w, Scheme.Hom.comp_apply, hz]`.

Conclude with `Scheme.fromSpecStalk_closedPoint`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Take `⟨i', hi'⟩` from `exists_chart hL (ι y)`. Conclude with `⟨ι y, i', rfl, hb y ⟨y, hy, rfl⟩ i' k hi' ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, Scheme.basicOpen_le _ _ hy⟩, hy⟩)⟩`.
-/
theorem exists_theta_of_stalk {X : Scheme.{0}} {G : Over X} [GrpObj G] (hG : IsSemiAbelian G) {L : LB G.left}
    (hL : L.IsLB) (x : X) {G' : Over (Sp (X.presheaf.stalk x))} {φ : G'.left ⟶ G.left}
    (hφ : IsPullback φ G'.hom G.hom (X.fromSpecStalk x)) {L' : LB G'.left} (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull φ)) (hθ : LN.ThetaNZ G' L') :
    ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V),
      ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i) := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  let ι := pullback.fst G.hom hU.fromSpec
  let f := pullback.snd G.hom hU.fromSpec
  have hξ : Spec.map (X.presheaf.germ U x hx) ≫ hU.fromSpec = X.fromSpecStalk x := hU.fromSpecStalk_eq_fromSpecStalk hx
  let π : G'.left ⟶ pullback G.hom hU.fromSpec := pullback.lift φ (G'.hom ≫ Spec.map (X.presheaf.germ U x hx))
    (by rw [Category.assoc, hξ, hφ.w])
  have hπ : π ≫ ι = φ := pullback.lift_fst _ _ _
  have hP : IsPullback π G'.hom f (Spec.map (X.presheaf.germ U x hx)) :=
    IsPullback.of_right (by rw [hπ, hξ]; exact hφ) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have : CompactSpace (pullback G.hom hU.fromSpec : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace (pullback G.hom hU.fromSpec : Scheme.{0}) := quasiSeparatedSpace_of_quasiSeparated f
  have hflat : (X.presheaf.germ U x hx).hom.Flat := by
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact RingHom.flat_algebraMap_iff.2
      (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
  have hM := pull_isLB hL ι
  obtain ⟨w, hw'⟩ : LBIso ((L.pull ι).pull π) (L'.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullLinComb L ι (fun _ : PUnit => π) (fun _ => φ) (fun _ => 1) (𝟙 _)
      fun _ => hπ.trans (Category.id_comp _).symm) (Geo.Tor.chartPullPull L' _ _ rfl) hw.symm
  obtain ⟨θ', hθ'⟩ := hθ
  obtain ⟨σ, hσ⟩ := ThetaLocal.exists_sec_pull hL' (pull_isLB hM π) (𝟙 _) w hw' (O := ⊤) le_top _
    (SecSpread.res_mem_secOn θ' ⊤)
  obtain ⟨z, i, hz, hi⟩ := hθ' (IsLocalRing.closedPoint _)
  obtain ⟨k, hk⟩ := hσ z i ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, G'.left.basicOpen_le _ hi⟩, hi⟩)
  obtain ⟨k, rfl⟩ : ∃ j, k = fun _ => j := ⟨k PUnit.unit, rfl⟩
  have hk₁ := G'.left.basicOpen_le _ hk
  have hk₂ : π z ∈ (L.pull ι).U k := mem_pull.1 hk₁
  obtain ⟨n, a, u, hu⟩ := FlatSec.exists_comb_of_flat _ _ _ hflat _ f _ π G'.hom hP _ hM σ
  obtain ⟨j, hj⟩ : ∃ j, π z ∈ Scheme.basicOpen _ ((u j).f k) := by
    by_contra hn
    have h₁ := (AbLocusPull.isUnit_gs_iff (𝟙 _) z _ hk₁ _).2 hk
    rw [hu z k hk₂] at h₁
    refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_) h₁
    exact fun h₂ => hn ⟨j, (AbLocusPull.isUnit_gs_iff π z _ hk₂ _).1 h₂⟩
  let V : X.Opens := ⟨(ι ≫ G.hom) '' Scheme.basicOpen _ ((u j).f k),
    (ι ≫ G.hom).isOpenMap _ (Scheme.basicOpen _ ((u j).f k)).isOpen⟩
  have hr : G.hom ⁻¹ᵁ V ≤ ι.opensRange := by
    rintro g ⟨y, -, e⟩
    obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback G.hom hU.fromSpec) g (f y)
      (e.symm.trans (congrArg (fun r : pullback G.hom hU.fromSpec ⟶ X => r y) pullback.condition))
    exact ⟨q, hq⟩
  obtain ⟨θ, hθ, hb⟩ := ThetaLocal.exists_secOn_push hL hM (lbIso_refl hM) hr le_top
    (SecSpread.res_mem_secOn (u j) ⊤)
  refine ⟨V, ⟨π z, hj, ?_⟩, θ, hθ, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Category.assoc, hπ, hφ.w, Scheme.Hom.comp_apply, hz]
    exact Scheme.fromSpecStalk_closedPoint
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨i', hi'⟩ := exists_chart hL (ι y)
    exact ⟨ι y, i', rfl, hb y ⟨y, hy, rfl⟩ i' k hi'
      ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, Scheme.basicOpen_le _ _ hy⟩, hy⟩)⟩

/- English proof (translation)
Introduce `x`. Take `⟨t, ⟨m⟩⟩` from `exists_sab (S' := Sp (Y.X.presheaf.stalk x)) (Y.X.fromSpecStalk x) Y.t`. Take `⟨p, W, hp, hW, ξ', ⟨n⟩⟩` from `exists_local_point h _ t m`. Conclude with `exists_theta_of_stalk Y.t.semi Y.t.PP.isLB x m.cart.1 t.PP.isLB (m.lin.imp fun _ h => h.1) (ThetaLocal.thetaNZ_of_pushInvertible E H _ _ ((s.clauses p W hp hW).1.1 ⟨l, c, hg p hp⟩).2.2.1 _ ξ' t n)`.
-/
theorem hasTheta (h : IsGlob s.Y hg Y) : HasTheta Y.t.G Y.t.PP.L := by
  intro x
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (S' := Sp (Y.X.presheaf.stalk x)) (Y.X.fromSpecStalk x) Y.t
  obtain ⟨p, W, hp, hW, ξ', ⟨n⟩⟩ := exists_local_point h _ t m
  exact exists_theta_of_stalk Y.t.semi Y.t.PP.isLB x m.cart.1 t.PP.isLB (m.lin.imp fun _ h => h.1)
    (ThetaLocal.thetaNZ_of_pushInvertible E H _ _ ((s.clauses p W hp hW).1.1 ⟨l, c, hg p hp⟩).2.2.1 _ ξ' t n)

end GlobalTheory.GlobalClauses
