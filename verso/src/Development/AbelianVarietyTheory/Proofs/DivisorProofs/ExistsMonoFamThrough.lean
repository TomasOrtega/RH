import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLiftOfGeometricPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformization
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitRamifiedExtensionFormMultipleStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartTrait

/- English proof (translation)
Establish `: IsDominant j` using `⟨hd⟩`. Set `O` to `S.presheaf.stalk x`. Take `⟨ge, hge, hs⟩` from `exists_mem_genericPoints_specializes x`. Establish `hge'` using `genericPoints_subset_range_of_isDominant j hge`. Establish `h1 : ge ∈ Set.range (S.fromSpecStalk x)`.

Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hs`. Take `⟨q, rfl⟩` from `h1`. Establish `hop : IsOpen (S.fromSpecStalk x ⁻¹' Set.range j)` using `j.isOpenEmbedding.isOpen_range.preimage (S.fromSpecStalk x).continuous`. Take `⟨_, ⟨f, rfl⟩, hqf, hf⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := q) hge' hop`.

Establish `hfm : f ∈ maximalIdeal O`. Assume the negation of the conclusion as `hn`. Establish `: S.fromSpecStalk x (closedPoint O) ∈ Set.range j` using `hf (show closedPoint O ∈ PrimeSpectrum.basicOpen f from hn)`. Rewrite `this` using `[Scheme.fromSpecStalk_closedPoint]`. Conclude with `hx this`.

Set `Ω` to `AlgebraicClosure (ResidueField O)`. Set `φ : O →+* Ω` to `(algebraMap (ResidueField O) Ω).comp (residue O)`. Establish `: IsLocalHom φ` using `⟨fun a ha => by`. Assume the negation of the conclusion as `h`. Establish `: residue O a = 0` using `(residue_eq_zero_iff a).2 h`.

Simplify using `[φ, this] at ha⟩`. Take `⟨W, _, _, _, _, ψ, ιW, hψ, hιW⟩` from `GlobalTheory.GeomTrait.exists_dvr (O := O) (Ω := Ω) hfm q.asIdeal q.isPrime hqf φ`. Set `a : Sp W ⟶ S` to `Spec.map (CommRingCat.ofHom ψ) ≫ S.fromSpecStalk x`. Take `⟨y, hy⟩` from `GlobalTheory.HomExt.exists_lift_of_range_subset j (spMap (algebraMap W (FractionRing W)) ≫ a) (by`. Introduce and unpack `_ ⟨t, rfl⟩`.

Establish `: spMap (algebraMap W (FractionRing W)) t = (⊥ : PrimeSpectrum W)`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥`. Rewrite using `[@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)`.

Rewrite using `[Scheme.Hom.comp_apply, this]`. Conclude with `hf (a := PrimeSpectrum.comap ψ ⊥) hψ)`. Establish `hloc : IsLocalHom ψ` using `⟨fun r hr => by`. Assume the negation of the conclusion as `h`. Establish `h2 : φ r = ιW (residue W (ψ r))` using `by rw [← hιW]; rfl`.

Establish `: residue W (ψ r) ≠ 0`. Rewrite using `[Ne, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]`. Conclude with `hr`. Establish `h3 : φ r ≠ 0` using `by rw [h2]; exact (map_ne_zero ιW).2 this`. Conclude with `h (isUnit_of_map_unit φ r (IsUnit.mk0 _ h3))⟩`.

Use `⟨W, inferInstance, inferInstance, inferInstance, inferInstance, a, y, hy, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `S.fromSpecStalk x (Spec.map (CommRingCat.ofHom ψ) (closedPoint W)) = x`. Establish `: Spec.map (CommRingCat.ofHom ψ) (closedPoint W) = closedPoint O` using `IsLocalRing.comap_closedPoint ψ`. Rewrite using `[this, Scheme.fromSpecStalk_closedPoint]`.
-/
theorem exists_cdvr_through {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (hd : Dense (Set.range j))
    [IsLocallyNoetherian S] (x : S) (hx : x ∉ Set.range j) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (a : Sp W ⟶ S) (y₀ : Sp (FractionRing W) ⟶ U),
      y₀ ≫ j = jK W ≫ a ∧ a (closedPoint W) = x := by
  have : IsDominant j := ⟨hd⟩
  let O := S.presheaf.stalk x
  obtain ⟨ge, hge, hs⟩ := exists_mem_genericPoints_specializes x
  have hge' := genericPoints_subset_range_of_isDominant j hge
  have h1 : ge ∈ Set.range (S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hs
  obtain ⟨q, rfl⟩ := h1
  have hop : IsOpen (S.fromSpecStalk x ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage (S.fromSpecStalk x).continuous
  obtain ⟨_, ⟨f, rfl⟩, hqf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := q) hge' hop
  have hfm : f ∈ maximalIdeal O := by
    by_contra hn
    have : S.fromSpecStalk x (closedPoint O) ∈ Set.range j :=
      hf (show closedPoint O ∈ PrimeSpectrum.basicOpen f from hn)
    rw [Scheme.fromSpecStalk_closedPoint] at this
    exact hx this
  let Ω := AlgebraicClosure (ResidueField O)
  let φ : O →+* Ω := (algebraMap (ResidueField O) Ω).comp (residue O)
  have : IsLocalHom φ := ⟨fun a ha => by
    by_contra h
    have : residue O a = 0 := (residue_eq_zero_iff a).2 h
    simp [φ, this] at ha⟩
  obtain ⟨W, _, _, _, _, ψ, ιW, hψ, hιW⟩ := GlobalTheory.GeomTrait.exists_dvr (O := O) (Ω := Ω) hfm q.asIdeal q.isPrime hqf φ
  let a : Sp W ⟶ S := Spec.map (CommRingCat.ofHom ψ) ≫ S.fromSpecStalk x
  obtain ⟨y, hy⟩ := GlobalTheory.HomExt.exists_lift_of_range_subset j
    (spMap (algebraMap W (FractionRing W)) ≫ a) (by
      rintro _ ⟨t, rfl⟩
      have : spMap (algebraMap W (FractionRing W)) t = (⊥ : PrimeSpectrum W) := by
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
      rw [Scheme.Hom.comp_apply, this]
      exact hf (a := PrimeSpectrum.comap ψ ⊥) hψ)
  have hloc : IsLocalHom ψ := ⟨fun r hr => by
    by_contra h
    have h2 : φ r = ιW (residue W (ψ r)) := by rw [← hιW]; rfl
    have : residue W (ψ r) ≠ 0 := by
      rw [Ne, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]; exact hr
    have h3 : φ r ≠ 0 := by rw [h2]; exact (map_ne_zero ιW).2 this
    exact h (isUnit_of_map_unit φ r (IsUnit.mk0 _ h3))⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, a, y, hy, ?_⟩
  change S.fromSpecStalk x (Spec.map (CommRingCat.ofHom ψ) (closedPoint W)) = x
  have : Spec.map (CommRingCat.ofHom ψ) (closedPoint W) = closedPoint O :=
    IsLocalRing.comap_closedPoint ψ
  rw [this, Scheme.fromSpecStalk_closedPoint]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨i, hi⟩` from `IsMonomial.exists_pos (maximalIdeal.isMaximal T.V).ne_top T.mono hx`. Use `fin_cases i`. Conclude with `hi`.
-/
theorem trait_be_pos (T : UPoinc.UTrait Xo c) {x : T.P.D.toPre.X} (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨i, hi⟩ := IsMonomial.exists_pos (maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases i
  exact hi

/- English proof (translation)
Take `⟨tK, ⟨m⟩, ⟨m'⟩⟩` from `hg`. Set `K` to `AlgebraicClosure (FractionRing R)`. Set `f : R →+* K` to `(algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))`. Establish `hf : Function.Injective f` using `(algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))`. Use `haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩`.

Set `x' : Sp K ⟶ Sp (FractionRing R)` to `spMap (algebraMap (FractionRing R) K)`. Establish `hx : x' ≫ jK R = spMap f`. Rewrite using `[← GlobalTheory.TorRef.DomFine.spMap_comp']`. Take `⟨β₀, hβ₀⟩` from `Spec.map_surjective ((x' ≫ y ≫ pullback.fst _ _) ≫ Xo.s)`. Establish `hdet` using `(Xo.univ.geom K (x' ≫ y ≫ pullback.fst _ _) β₀.hom hβ₀.symm).1`.

Establish `hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K)`. Rewrite using `[← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]`. Establish `bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act (x' ≫ y ≫ pullback.fst _ _) τ N → Module.finrank (𝓞 E) P.D.toPre.X ≤ N`. Introduce `τ N hN`. Establish `h₅` using `(GlobalTheory.lieMult_iff_of_isGrpPullback m'.cart tK.act Xo.univ.t.act m'.act x' τ N).2 hN`.

Establish `h₆` using `(GlobalTheory.lieMult_iff_of_isGrpPullback m.cart tK.act t.act m.act x' τ N).1 h₅`. Rewrite `h₆` using `[hx]`. Take `⟨n, -, hn⟩` from `GlobalTheory.CharRank.lieMult_unif_loc H R t P K f hf τ N h₆`. Use linear arithmetic over natural numbers and integers. Take `⟨τ₁, τ₂, h₁, h₂⟩` from `GlobalTheory.CharRank.exists_chars H K _ hr`.

Conclude with `le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))`.
-/
theorem trait_finrank_le {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R]
    {y : Sp (FractionRing R) ⟶ Xo.XF c} {t : SAB H (Sp R)} (hg : UPoinc.GenOf Xo c y t) (P : PELUnif (maximalIdeal R) t) :
    Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q := by
  obtain ⟨tK, ⟨m⟩, ⟨m'⟩⟩ := hg
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Sp (FractionRing R) := spMap (algebraMap (FractionRing R) K)
  have hx : x' ≫ jK R = spMap f := by
    rw [← GlobalTheory.TorRef.DomFine.spMap_comp']
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective ((x' ≫ y ≫ pullback.fst _ _) ≫ Xo.s)
  have hdet := (Xo.univ.geom K (x' ≫ y ≫ pullback.fst _ _) β₀.hom hβ₀.symm).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act (x' ≫ y ≫ pullback.fst _ _) τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m'.cart tK.act Xo.univ.t.act m'.act x' τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart tK.act t.act m.act x' τ N).1 h₅
    rw [hx] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

/- English proof (translation)
Take `⟨h1, h2⟩` from `hβ`. Establish `h` using `h2 H.w0 y y`. Rewrite `h` using `[GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, sub_smul, one_smul, map_sub, h1 y (H.w0 • y)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bal_diag_eq {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms (H.bar : 𝓞 E → 𝓞 E) X) (y : X) : β y y = 2 * β (H.w0 • y) y := by
  obtain ⟨h1, h2⟩ := hβ
  have h := h2 H.w0 y y
  rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, sub_smul, one_smul, map_sub, h1 y (H.w0 • y)] at h
  linarith

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `a`. Conclude with `h a`.
-/
theorem spMap_sq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] (f : A →+* B) (g : A →+* C)
    (f' : B →+* D) (g' : C →+* D) (h : ∀ a, f' (f a) = g' (g a)) : spMap f' ≫ spMap f = spMap g' ≫ spMap g := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact h a

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c φ hpq hpol hnsi Z zs i OZ N d J S π j _ BD hU hsep x hx`. Take `⟨⟨-, -, -, -, hizs, -, -⟩, -, -, -, ⟨-, hproj, -, hdense, hjπ, -, -, -⟩, -⟩` from `hU`. Use `haveI : LocallyOfFiniteType (π ≫ zs) := GlobalTheory.T.locallyOfFiniteType_of_isProjOver c.F S (π ≫ zs) hproj`. Use `haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)`. Take `⟨W, _, _, _, _, a, y₀, hy₀, hax⟩` from `exists_cdvr_through j hdense x hx`.

Set `b₀ : c.F →+* W` to `(Spec.preimage (a ≫ π ≫ zs)).hom`. Establish `hb₀ : spMap b₀ = a ≫ π ≫ zs` using `Spec.map_preimage _`. Use `haveI : CharZero W := charZero_of_injective_ringHom b₀.injective`. Establish `hW : GlobalTheory.Mum.Base W` using `⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩`. Take `⟨T, f₁, fK₁, -, hloc₁, -, hc₁, hTy⟩` from `GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c W hW inferInstance y₀`.

Use `haveI := hloc₁`. Take `⟨_, _, _⟩` from `T.cdvr`. Use `haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X`. Use `haveI : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _`. Establish `hpolT : IsPolFanOn (H.bar : 𝓞 E → 𝓞 E) φ T.P.D.toPre.X` using `hpol _ (trait_finrank_le T.gen T.P)`.

Establish `hbal : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X` using `(balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev`. Take `⟨r, gm, k, cc, hgm, hk, hcc, hsum⟩` from `GlobalTheory.Poinc.Cover.exists_cone (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) φ T.P.D.toPre.X hpolT T.be hbal (fun y hy => trait_be_pos T hy)`. Establish `hM : 0 < l.M'` using `Nat.lcm_pos (by have := l.three_le; omega) l.A_pos`. Take `⟨T₂, g, gK, e, q, -, hgloc, hgK, hT₂y, hq, hbe⟩` from `GlobalTheory.T.exists_unitaryTrait_ramifiedExtension_form_multiple T (k * l.M') (Nat.mul_pos hk hM)`. Use `haveI := hgloc`.

Take `⟨_, _, _⟩` from `T₂.cdvr`. Establish `hW₁ : spMap fK₁ ≫ jK W = jK T.V ≫ spMap f₁` using `spMap_sq (algebraMap W _) f₁ fK₁ (algebraMap T.V _) hc₁`. Establish `hT₁ : spMap gK ≫ jK T.V = jK T₂.V ≫ spMap g` using `spMap_sq (algebraMap T.V _) g gK (algebraMap T₂.V _) hgK`. Establish `hy0s : y₀ ≫ pullback.snd _ _ = jK W ≫ spMap b₀`. Rewrite using `[hb₀, ← hizs, ← hjπ]`.

Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hy₀]`. Set `bb : c.F →+* T₂.V` to `g.comp (f₁.comp b₀)`. Establish `hover : T₂.y ≫ pullback.snd _ _ = jK T₂.V ≫ spMap bb`. Rewrite using `[hT₂y, hTy]`.

Simplify using `only [Category.assoc]`. Rewrite using `[hy0s, reassoc_of% hW₁, reassoc_of% hT₁]`. Simplify using `only [bb, spMap_comp_, Category.assoc]`. Establish `hev : ∀ i z, gm i z z = 2 * gm i (H.w0 • z) z` using `fun i z => bal_diag_eq (hgm.mem i) z`. Establish `hnn : ∀ i z, 0 ≤ gm i (H.w0 • z) z` using `fun i z => by`.

Use `hgm.nonneg i z` as an intermediate fact. Rewrite `this` using `[hev]`. Use linear arithmetic over natural numbers and integers. Establish `hsumz : ∀ z, (k : ℤ) * T.be z z = ∑ i, (cc i : ℤ) * gm i z z` using `fun z => by`. Use `congrArg (fun β : LinearMap.BilinForm ℤ T.P.D.toPre.X => β z z) hsum` as an intermediate fact.

Simplify `this` using `[LinearMap.sum_apply, nsmul_eq_mul]`. Establish `hmono : IsMonomial T₂.P.D.toPre (fun i => T₂.ϖ ^ (q * cc i)) (fun i => (l.M' : ℤ) • pull e.symm.toLinearMap (gm i))`. Introduce `y`. Take `⟨u, n₀, hn₀, hψ⟩` from `T₂.mono y`. Establish `hy : y = e (e.symm y)` using `(e.apply_symm_apply y).symm`.

Use `set z := e.symm y`. Use `⟨u, fun i => (l.M' * gm i (H.w0 • z) z).toNat, fun i => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, pull_apply, LinearEquiv.coe_coe, smul_eq_mul]`. Rewrite using `[Int.toNat_of_nonneg (mul_nonneg (by positivity) (hnn i z)), hev]`. Expand and normalize the polynomial expressions, which then agree.

Use `hψ using 2` and compare the differences between its conclusion and the goal. Rewrite using `[Fin.prod_univ_one]`. Simplify using `only [Matrix.cons_val_zero, ← pow_mul, Finset.prod_pow_eq_pow_sum]`. Use `congr 1`. Establish `h0 : T₂.be y y = 2 * n₀ 0` using `by simpa using hn₀ 0`.

Rewrite `h0` using `[hy, hbe]`. Establish `hz` using `hsumz z`. Establish `hcast : ((∑ i, q * cc i * (l.M' * gm i (H.w0 • z) z).toNat : ℕ) : ℤ) = ∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z)`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Int.toNat_of_nonneg (mul_nonneg (by positivity) (hnn i z))]`. Establish `hz2 : (k : ℤ) * T.be z z = 2 * ∑ i, (cc i : ℤ) * gm i (H.w0 • z) z`. Rewrite using `[hz, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hev]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hS : ∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z) = (q * l.M') * ∑ i, (cc i : ℤ) * gm i (H.w0 • z) z`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : (2 : ℤ) * (∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z)) = 2 * (n₀ 0 : ℤ)`. Rewrite using `[← h0, hS]`. Use `push_cast`. Take the linear combination `(-((q : ℤ) * l.M')) * hz2`. Establish `h3` using `mul_left_cancel₀ (two_ne_zero) h2`.

Conclude with `hcast.trans h3` after adjusting the coercions. Set `C : MonoFam Xo c φ T₂.V` to `{ b := bb, t := T₂.t, P := T₂.P, y := T₂.y, y_over := hover, gen := T₂.gen, m := r, s := fun i => T₂.ϖ ^ (q * cc i), s_mem := fun i => Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 T₂.irr.not_isUnit) _ (Nat.mul_pos hq (hcc i)), δ := fun i => pull e.symm.toLinearMap (gm i), cone …`. Establish `hcomp : C.y ≫ j = jK T₂.V ≫ (spMap (g.comp f₁) ≫ a)` using `by show T₂.y ≫ j = _`. Rewrite using `[hT₂y, hTy]`. Simplify using `only [Category.assoc]`.

Rewrite using `[hy₀, reassoc_of% hW₁, reassoc_of% hT₁, spMap_comp_]`. Simplify using `only [Category.assoc]`. Establish `hcl : (spMap (g.comp f₁) ≫ a) (closedPoint T₂.V) = x`. Establish `h1 : spMap (g.comp f₁) (closedPoint T₂.V) = closedPoint W` using `IsLocalRing.comap_closedPoint (g.comp f₁)`. Express the relevant statement in the definitionally equal form `a (spMap (g.comp f₁) (closedPoint T₂.V)) = x`.

Rewrite using `[h1, hax]`. Conclude with `⟨T₂.V, inferInstance, inferInstance, inferInstance, C, spMap (g.comp f₁) ≫ a, ⟨⟨inferInstance, inferInstance, inferInstance, ‹_›⟩, ‹_›⟩, hcomp, hcl⟩`.
-/
theorem exists_monoFam_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hnsi Z zs i OZ N d J S π j _ BD hU hsep x hx
  obtain ⟨⟨-, -, -, -, hizs, -, -⟩, -, -, -, ⟨-, hproj, -, hdense, hjπ, -, -, -⟩, -⟩ := hU
  haveI : LocallyOfFiniteType (π ≫ zs) := GlobalTheory.T.locallyOfFiniteType_of_isProjOver c.F S (π ≫ zs) hproj
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  obtain ⟨W, _, _, _, _, a, y₀, hy₀, hax⟩ := exists_cdvr_through j hdense x hx
  let b₀ : c.F →+* W := (Spec.preimage (a ≫ π ≫ zs)).hom
  have hb₀ : spMap b₀ = a ≫ π ≫ zs := Spec.map_preimage _
  haveI : CharZero W := charZero_of_injective_ringHom b₀.injective
  have hW : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨T, f₁, fK₁, -, hloc₁, -, hc₁, hTy⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c W hW inferInstance y₀

  haveI := hloc₁
  obtain ⟨_, _, _⟩ := T.cdvr
  haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X
  haveI : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hpolT : IsPolFanOn (H.bar : 𝓞 E → 𝓞 E) φ T.P.D.toPre.X := hpol _ (trait_finrank_le T.gen T.P)
  have hbal : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X :=
    (balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev
  obtain ⟨r, gm, k, cc, hgm, hk, hcc, hsum⟩ := GlobalTheory.Poinc.Cover.exists_cone (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) φ
    T.P.D.toPre.X hpolT T.be hbal (fun y hy => trait_be_pos T hy)
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨T₂, g, gK, e, q, -, hgloc, hgK, hT₂y, hq, hbe⟩ := GlobalTheory.T.exists_unitaryTrait_ramifiedExtension_form_multiple T (k * l.M') (Nat.mul_pos hk hM)
  haveI := hgloc
  obtain ⟨_, _, _⟩ := T₂.cdvr

  have hW₁ : spMap fK₁ ≫ jK W = jK T.V ≫ spMap f₁ := spMap_sq (algebraMap W _) f₁ fK₁ (algebraMap T.V _) hc₁
  have hT₁ : spMap gK ≫ jK T.V = jK T₂.V ≫ spMap g := spMap_sq (algebraMap T.V _) g gK (algebraMap T₂.V _) hgK
  have hy0s : y₀ ≫ pullback.snd _ _ = jK W ≫ spMap b₀ := by
    rw [hb₀, ← hizs, ← hjπ]
    simp only [Category.assoc]
    rw [reassoc_of% hy₀]
  let bb : c.F →+* T₂.V := g.comp (f₁.comp b₀)
  have hover : T₂.y ≫ pullback.snd _ _ = jK T₂.V ≫ spMap bb := by
    rw [hT₂y, hTy]
    simp only [Category.assoc]
    rw [hy0s, reassoc_of% hW₁, reassoc_of% hT₁]
    simp only [bb, spMap_comp_, Category.assoc]
  have hev : ∀ i z, gm i z z = 2 * gm i (H.w0 • z) z := fun i z => bal_diag_eq (hgm.mem i) z
  have hnn : ∀ i z, 0 ≤ gm i (H.w0 • z) z := fun i z => by
    have := hgm.nonneg i z
    rw [hev] at this
    omega
  have hsumz : ∀ z, (k : ℤ) * T.be z z = ∑ i, (cc i : ℤ) * gm i z z := fun z => by
    have := congrArg (fun β : LinearMap.BilinForm ℤ T.P.D.toPre.X => β z z) hsum
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hmono : IsMonomial T₂.P.D.toPre (fun i => T₂.ϖ ^ (q * cc i))
      (fun i => (l.M' : ℤ) • pull e.symm.toLinearMap (gm i)) := by
    intro y
    obtain ⟨u, n₀, hn₀, hψ⟩ := T₂.mono y
    have hy : y = e (e.symm y) := (e.apply_symm_apply y).symm
    set z := e.symm y
    refine ⟨u, fun i => (l.M' * gm i (H.w0 • z) z).toNat, fun i => ?_, ?_⟩
    · simp only [LinearMap.smul_apply, pull_apply, LinearEquiv.coe_coe, smul_eq_mul]
      rw [Int.toNat_of_nonneg (mul_nonneg (by positivity) (hnn i z)), hev]
      ring
    · convert hψ using 2
      rw [Fin.prod_univ_one]
      simp only [Matrix.cons_val_zero, ← pow_mul, Finset.prod_pow_eq_pow_sum]
      congr 1
      have h0 : T₂.be y y = 2 * n₀ 0 := by simpa using hn₀ 0
      rw [hy, hbe] at h0
      have hz := hsumz z
      have hcast : ((∑ i, q * cc i * (l.M' * gm i (H.w0 • z) z).toNat : ℕ) : ℤ) =
          ∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z) := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Int.toNat_of_nonneg (mul_nonneg (by positivity) (hnn i z))]
      have hz2 : (k : ℤ) * T.be z z = 2 * ∑ i, (cc i : ℤ) * gm i (H.w0 • z) z := by
        rw [hz, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hev]
        ring
      have hS : ∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z) =
          (q * l.M') * ∑ i, (cc i : ℤ) * gm i (H.w0 • z) z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have h2 : (2 : ℤ) * (∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z)) = 2 * (n₀ 0 : ℤ) := by
        rw [← h0, hS]
        push_cast
        linear_combination (-((q : ℤ) * l.M')) * hz2
      have h3 := mul_left_cancel₀ (two_ne_zero) h2
      exact_mod_cast hcast.trans h3
  let C : MonoFam Xo c φ T₂.V :=
    { b := bb, t := T₂.t, P := T₂.P, y := T₂.y, y_over := hover, gen := T₂.gen, m := r,
      s := fun i => T₂.ϖ ^ (q * cc i),
      s_mem := fun i => Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 T₂.irr.not_isUnit) _
        (Nat.mul_pos hq (hcc i)),
      δ := fun i => pull e.symm.toLinearMap (gm i), cone := hgm.pull_equiv e.symm,
      rank := trait_finrank_le T₂.gen T₂.P, mono := hmono }
  have hcomp : C.y ≫ j = jK T₂.V ≫ (spMap (g.comp f₁) ≫ a) := by
    show T₂.y ≫ j = _
    rw [hT₂y, hTy]
    simp only [Category.assoc]
    rw [hy₀, reassoc_of% hW₁, reassoc_of% hT₁, spMap_comp_]
    simp only [Category.assoc]
  have hcl : (spMap (g.comp f₁) ≫ a) (closedPoint T₂.V) = x := by
    have h1 : spMap (g.comp f₁) (closedPoint T₂.V) = closedPoint W := IsLocalRing.comap_closedPoint (g.comp f₁)
    change a (spMap (g.comp f₁) (closedPoint T₂.V)) = x
    rw [h1, hax]
  exact ⟨T₂.V, inferInstance, inferInstance, inferInstance, C, spMap (g.comp f₁) ≫ a,
    ⟨⟨inferInstance, inferInstance, inferInstance, ‹_›⟩, ‹_›⟩, hcomp, hcl⟩

end GlobalTheory.UChartTrait
