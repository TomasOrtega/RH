import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsTangentVectorBasisAtPointBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Spread

/- English proof (translation)
Set `p : PrimeSpectrum S` to `⟨q, inferInstance⟩`. Set `t : Sp (Localization.AtPrime q)` to `(IsLocalRing.closedPoint (Localization.AtPrime q) : PrimeSpectrum _)`. Establish `hcl : (spMap (algebraMap S (Localization.AtPrime q))) t = (p : Sp S)` using `PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal)`. Establish `hmem : w (p : Sp S) ∈ Set.range x`. Use `⟨(spMap θ) t, ?_⟩` and prove the remaining obligations.

Use `congrArg (fun f : Sp (Localization.AtPrime q) ⟶ X => f t) h` as an intermediate fact. Simplify using `only [Scheme.Hom.comp_apply] at this`. Rewrite using `[this, hcl]`. Establish `hopen : IsOpen (w ⁻¹' Set.range x : Set (PrimeSpectrum S))` using `x.opensRange.isOpen.preimage w.continuous`. Take `⟨_, ⟨g₀, rfl⟩, hg, hle⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ (w ⁻¹' Set.range x : Set (PrimeSpectrum S)) from hmem) hopen`.

Establish `hrange : Set.range (spMap (algebraMap S (Localization.Away g₀)) ≫ w) ⊆ Set.range x`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `hy : (spMap (algebraMap S (Localization.Away g₀))) y ∈ ((PrimeSpectrum.basicOpen g₀ : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S))`. Rewrite using `[← PrimeSpectrum.localization_away_comap_range (Localization.Away g₀) g₀]`. Conclude with `⟨y, rfl⟩`.

Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `hle hy`. Set `ℓ` to `IsOpenImmersion.lift x _ hrange`. Establish `hℓ : ℓ ≫ x = _` using `IsOpenImmersion.lift_fac x _ hrange`. Set `θ₀ : R →+* Localization.Away g₀` to `(Spec.preimage ℓ).hom`.

Establish `hθ₀ : spMap θ₀ = ℓ`. Simplify using `only [spMap, θ₀, CommRingCat.ofHom_hom, Spec.map_preimage]`. Use `⟨g₀, θ₀, hg, by rw [hθ₀, hℓ], fun ι hι => ?_⟩` and prove the remaining obligations. Establish `e : spMap (ι.comp θ₀) ≫ x = spMap θ ≫ x`. Rewrite using `[← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, hθ₀, hℓ, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, hι, h]`.

Establish `e'` using `(cancel_mono x).1 e`. Establish `e''` using `Spec.map_injective e'`. Conclude with `congrArg CommRingCat.Hom.hom e''`.
-/
theorem exists_away_lift {X : Scheme.{0}} {S R : Type} [CommRing S] [CommRing R] (x : Sp R ⟶ X) [IsOpenImmersion x]
    (w : Sp S ⟶ X) (q : Ideal S) [q.IsPrime] (θ : R →+* Localization.AtPrime q)
    (h : spMap θ ≫ x = spMap (algebraMap S (Localization.AtPrime q)) ≫ w) :
    ∃ (g₀ : S) (θ₀ : R →+* Localization.Away g₀), g₀ ∉ q ∧
      spMap θ₀ ≫ x = spMap (algebraMap S (Localization.Away g₀)) ≫ w ∧
      ∀ ι : Localization.Away g₀ →+* Localization.AtPrime q,
        ι.comp (algebraMap S _) = algebraMap S _ → ι.comp θ₀ = θ := by
  let p : PrimeSpectrum S := ⟨q, inferInstance⟩
  let t : Sp (Localization.AtPrime q) := (IsLocalRing.closedPoint (Localization.AtPrime q) : PrimeSpectrum _)
  have hcl : (spMap (algebraMap S (Localization.AtPrime q))) t = (p : Sp S) :=
    PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal)
  have hmem : w (p : Sp S) ∈ Set.range x := by
    refine ⟨(spMap θ) t, ?_⟩
    have := congrArg (fun f : Sp (Localization.AtPrime q) ⟶ X => f t) h
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, hcl]
  have hopen : IsOpen (w ⁻¹' Set.range x : Set (PrimeSpectrum S)) :=
    x.opensRange.isOpen.preimage w.continuous
  obtain ⟨_, ⟨g₀, rfl⟩, hg, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (w ⁻¹' Set.range x : Set (PrimeSpectrum S)) from hmem) hopen
  have hrange : Set.range (spMap (algebraMap S (Localization.Away g₀)) ≫ w) ⊆ Set.range x := by
    rintro _ ⟨y, rfl⟩
    have hy : (spMap (algebraMap S (Localization.Away g₀))) y ∈
        ((PrimeSpectrum.basicOpen g₀ : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g₀) g₀]
      exact ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hle hy
  let ℓ := IsOpenImmersion.lift x _ hrange
  have hℓ : ℓ ≫ x = _ := IsOpenImmersion.lift_fac x _ hrange
  let θ₀ : R →+* Localization.Away g₀ := (Spec.preimage ℓ).hom
  have hθ₀ : spMap θ₀ = ℓ := by
    simp only [spMap, θ₀, CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨g₀, θ₀, hg, by rw [hθ₀, hℓ], fun ι hι => ?_⟩
  have e : spMap (ι.comp θ₀) ≫ x = spMap θ ≫ x := by
    rw [← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, hθ₀, hℓ, ← Category.assoc,
      GlobalTheory.Frames.ChgBC.spMap_comp_ring, hι, h]
  have e' := (cancel_mono x).1 e
  have e'' := Spec.map_injective e'
  exact congrArg CommRingCat.Hom.hom e''

/- English proof (translation)
Take `⟨⟨t, m⟩, ht⟩` from `IsLocalization.surj (Submonoid.powers g₀) b`. Establish `h0 : algebraMap S (Localization.AtPrime q) t = 0`. Use `congrArg ι ht` as an intermediate fact. Rewrite `this` using `[map_mul, hb, zero_mul]`. Rewrite using `[← hι]`.

Conclude with `this.symm`. Take `⟨⟨s, hs⟩, hst⟩` from `(IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) t).1 h0`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap S (Localization.Away g₀) s * b * algebraMap S _ (m : S) = 0`. Rewrite using `[_root_.mul_assoc, ht, ← map_mul]`.

Establish `: s * t = 0` using `hst`. Rewrite using `[this, map_zero]`. Conclude with `((IsLocalization.map_units (Localization.Away g₀) m).mul_left_eq_zero).1 h1`.
-/
theorem exists_kill {S : Type} [CommRing S] (q : Ideal S) [q.IsPrime] (g₀ : S)
    (ι : Localization.Away g₀ →+* Localization.AtPrime q)
    (hι : ι.comp (algebraMap S _) = algebraMap S _) (b : Localization.Away g₀) (hb : ι b = 0) :
    ∃ s, s ∉ q ∧ algebraMap S (Localization.Away g₀) s * b = 0 := by
  obtain ⟨⟨t, m⟩, ht⟩ := IsLocalization.surj (Submonoid.powers g₀) b
  have h0 : algebraMap S (Localization.AtPrime q) t = 0 := by
    have := congrArg ι ht
    rw [map_mul, hb, zero_mul] at this
    rw [← hι]
    exact this.symm
  obtain ⟨⟨s, hs⟩, hst⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) t).1 h0
  refine ⟨s, hs, ?_⟩
  have h1 : algebraMap S (Localization.Away g₀) s * b * algebraMap S _ (m : S) = 0 := by
    rw [_root_.mul_assoc, ht, ← map_mul]
    have : s * t = 0 := hst
    rw [this, map_zero]
  exact ((IsLocalization.map_units (Localization.Away g₀) m).mul_left_eq_zero).1 h1

/- English proof (translation)
Establish `hk : ∃ s, s ∉ q ∧ ∀ b ∈ Z, algebraMap S (Localization.Away g₀) s * b = 0`. Proceed by induction on `Z using Finset.induction_on with`. Consider the case `empty => exact ⟨1, fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h), by simp⟩`. Consider the case `insert b Z _ ih`. Take `⟨s, hs, h⟩` from `ih fun c hc => hZ c (Finset.mem_insert_of_mem hc)`.

Take `⟨s', hs', h'⟩` from `exists_kill q g₀ ι hι b (hZ b (Finset.mem_insert_self _ _))`. Use `⟨s * s', fun hm => (hq.mem_or_mem hm).elim hs hs', fun c hc => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hc with rfl | hc` into its components or cases. Rewrite using `[map_mul, mul_comm (algebraMap S _ s), _root_.mul_assoc, mul_comm (algebraMap S _ s), ← _root_.mul_assoc, h', zero_mul]`. Rewrite using `[map_mul, mul_comm (algebraMap S _ s), _root_.mul_assoc, h c hc, mul_zero]`.

Take `⟨s, hs, hsZ⟩` from `hk`. Take `⟨⟨t, m⟩, ht⟩` from `IsLocalization.surj (Submonoid.powers g₀) d`. Establish `hιm : ∀ a : S, ι (algebraMap S _ a) = algebraMap S (Localization.AtPrime q) a` using `fun a => RingHom.congr_fun hι a`. Establish `hm : (m : S) ∉ q`. Take `⟨k, hk⟩` from `m.2`.

Introduce `hmem`. Rewrite `hmem` using `[← hk]`. Conclude with `hg₀ (hq.mem_of_pow_mem k hmem)`. Establish `htq : t ∉ q`. Establish `h1 : IsUnit (algebraMap S (Localization.AtPrime q) t)`.

Rewrite using `[← hιm, ← ht, map_mul, hιm]`. Conclude with `hd.mul ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).2 hm)`. Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q t).1 h1`. Set `g` to `g₀ * s * t`. Establish `hg : g ∉ q` using `fun hmem => (hq.mem_or_mem hmem).elim (fun h => (hq.mem_or_mem h).elim hg₀ hs) htq`.

Establish `hgu : IsUnit (algebraMap S (Localization.Away g) g)` using `IsLocalization.Away.algebraMap_isUnit g`. Establish `hgm : algebraMap S (Localization.Away g) g = algebraMap S _ g₀ * algebraMap S _ s * algebraMap S _ t`. Simplify using `only [g, map_mul]`. Rewrite `hgu` using `[hgm]`. Establish `ht' : IsUnit (algebraMap S (Localization.Away g) t)` using `isUnit_of_mul_isUnit_right hgu`.

Establish `hgs` using `isUnit_of_mul_isUnit_left hgu`. Establish `hg₀' : IsUnit (algebraMap S (Localization.Away g) g₀)` using `isUnit_of_mul_isUnit_left hgs`. Establish `hs' : IsUnit (algebraMap S (Localization.Away g) s)` using `isUnit_of_mul_isUnit_right hgs`. Set `ρ : Localization.Away g₀ →+* Localization.Away g` to `IsLocalization.Away.lift g₀ hg₀'`. Establish `hρ : ρ.comp (algebraMap S _) = algebraMap S _` using `IsLocalization.Away.lift_comp g₀ hg₀'`.

Establish `hρa : ∀ a : S, ρ (algebraMap S _ a) = algebraMap S (Localization.Away g) a` using `fun a => RingHom.congr_fun hρ a`. Use `⟨g, ρ, hg, hρ, fun b hb => ?_, ?_⟩` and prove the remaining obligations. Use `congrArg ρ (hsZ b hb)` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero, hρa]`. Conclude with `(hs'.mul_right_eq_zero).1 this`.

Establish `h1 : IsUnit (ρ d * ρ (algebraMap S _ (m : S)))`. Rewrite using `[← map_mul, ht, hρa]`. Conclude with `ht'`. Conclude with `isUnit_of_mul_isUnit_left h1`.
-/
theorem exists_spread {S : Type} [CommRing S] (q : Ideal S) [hq : q.IsPrime] (g₀ : S) (hg₀ : g₀ ∉ q)
    (ι : Localization.Away g₀ →+* Localization.AtPrime q)
    (hι : ι.comp (algebraMap S _) = algebraMap S _) (Z : Finset (Localization.Away g₀))
    (hZ : ∀ b ∈ Z, ι b = 0) (d : Localization.Away g₀) (hd : IsUnit (ι d)) :
    ∃ (g : S) (ρ : Localization.Away g₀ →+* Localization.Away g), g ∉ q ∧
      ρ.comp (algebraMap S _) = algebraMap S _ ∧ (∀ b ∈ Z, ρ b = 0) ∧ IsUnit (ρ d) := by
  classical
  have hk : ∃ s, s ∉ q ∧ ∀ b ∈ Z, algebraMap S (Localization.Away g₀) s * b = 0 := by
    induction Z using Finset.induction_on with
    | empty => exact ⟨1, fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h), by simp⟩
    | insert b Z _ ih =>
      obtain ⟨s, hs, h⟩ := ih fun c hc => hZ c (Finset.mem_insert_of_mem hc)
      obtain ⟨s', hs', h'⟩ := exists_kill q g₀ ι hι b (hZ b (Finset.mem_insert_self _ _))
      refine ⟨s * s', fun hm => (hq.mem_or_mem hm).elim hs hs', fun c hc => ?_⟩
      rcases Finset.mem_insert.1 hc with rfl | hc
      · rw [map_mul, mul_comm (algebraMap S _ s), _root_.mul_assoc, mul_comm (algebraMap S _ s),
          ← _root_.mul_assoc, h', zero_mul]
      · rw [map_mul, mul_comm (algebraMap S _ s), _root_.mul_assoc, h c hc, mul_zero]
  obtain ⟨s, hs, hsZ⟩ := hk
  obtain ⟨⟨t, m⟩, ht⟩ := IsLocalization.surj (Submonoid.powers g₀) d
  have hιm : ∀ a : S, ι (algebraMap S _ a) = algebraMap S (Localization.AtPrime q) a := fun a =>
    RingHom.congr_fun hι a
  have hm : (m : S) ∉ q := by
    obtain ⟨k, hk⟩ := m.2
    intro hmem
    rw [← hk] at hmem
    exact hg₀ (hq.mem_of_pow_mem k hmem)
  have htq : t ∉ q := by
    have h1 : IsUnit (algebraMap S (Localization.AtPrime q) t) := by
      rw [← hιm, ← ht, map_mul, hιm]
      exact hd.mul ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).2 hm)
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q t).1 h1
  let g := g₀ * s * t
  have hg : g ∉ q := fun hmem =>
    (hq.mem_or_mem hmem).elim (fun h => (hq.mem_or_mem h).elim hg₀ hs) htq
  have hgu : IsUnit (algebraMap S (Localization.Away g) g) := IsLocalization.Away.algebraMap_isUnit g
  have hgm : algebraMap S (Localization.Away g) g =
      algebraMap S _ g₀ * algebraMap S _ s * algebraMap S _ t := by
    simp only [g, map_mul]
  rw [hgm] at hgu
  have ht' : IsUnit (algebraMap S (Localization.Away g) t) := isUnit_of_mul_isUnit_right hgu
  have hgs := isUnit_of_mul_isUnit_left hgu
  have hg₀' : IsUnit (algebraMap S (Localization.Away g) g₀) := isUnit_of_mul_isUnit_left hgs
  have hs' : IsUnit (algebraMap S (Localization.Away g) s) := isUnit_of_mul_isUnit_right hgs
  let ρ : Localization.Away g₀ →+* Localization.Away g := IsLocalization.Away.lift g₀ hg₀'
  have hρ : ρ.comp (algebraMap S _) = algebraMap S _ := IsLocalization.Away.lift_comp g₀ hg₀'
  have hρa : ∀ a : S, ρ (algebraMap S _ a) = algebraMap S (Localization.Away g) a := fun a =>
    RingHom.congr_fun hρ a
  refine ⟨g, ρ, hg, hρ, fun b hb => ?_, ?_⟩
  · have := congrArg ρ (hsZ b hb)
    rw [map_mul, map_zero, hρa] at this
    exact (hs'.mul_right_eq_zero).1 this
  · have h1 : IsUnit (ρ d * ρ (algebraMap S _ (m : S))) := by
      rw [← map_mul, ht, hρa]
      exact ht'
    exact isUnit_of_mul_isUnit_left h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

open MonoidalCategory CartesianMonoidalCategory MonObj in

/- English proof (translation)
Simplify using `[Hom.one_def, Out.PullGtPf.toUnit_left']`.
-/
theorem one_left_eq {X : Scheme.{0}} {A : Type} [CommRing A] (G : Over X) [GrpObj G] (x : Sp A ⟶ X) :
    (1 : Over.mk x ⟶ G).left = x ≫ η[G].left := by
  simp [Hom.one_def, Out.PullGtPf.toUnit_left']

/- English proof (translation)
The claim follows from `RingHom.ext fun a => by simp [Formalism.L2.Pj.dualMap]`.
-/
theorem fst_dualMap {A B : Type} [CommRing A] [CommRing B] (θ : A →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (Formalism.L2.Pj.dualMap θ) =
      θ.comp (TrivSqZeroExt.fstHom A A A).toRingHom :=
  RingHom.ext fun a => by simp [Formalism.L2.Pj.dualMap]

/- English proof (translation)
The claim follows from `RingHom.ext fun a => by ext <;> simp [Formalism.L2.Pj.dualMap]`.
-/
theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    (Formalism.L2.Pj.dualMap f).comp (Formalism.L2.Pj.dualMap g) = Formalism.L2.Pj.dualMap (f.comp g) :=
  RingHom.ext fun a => by
    ext <;> simp [Formalism.L2.Pj.dualMap]

open MonoidalCategory CartesianMonoidalCategory MonObj in

/- English proof (translation)
Establish `hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _)` using `Y.m0.cart.1`. Establish `hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j` using `Y.m.cart.1`. Establish `hv2 : v' ≫ Y.t.G.hom = (spMap (algebraMap B (DualNumber B)) ≫ y) ≫ Y.j`. Rewrite using `[Category.assoc]`. Conclude with `hv`.

Set `u` to `hq.lift v' (spMap (algebraMap B (DualNumber B)) ≫ y) hv2`. Establish `hu1 : u ≫ Y.m.φ = v'` using `hq.lift_fst _ _ _`. Establish `hu2 : u ≫ Y.oF.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ y` using `hq.lift_snd _ _ _`. Establish `e1 : η[Y.oF.t.G].left ≫ Y.m.φ = Y.j ≫ η[Y.t.G].left` using `Out.PullGtPf.IsGrpPullback.one_left Y.m.cart`. Establish `e2 : η[Y.oF.t.G].left ≫ Y.m0.toSABMap.φ = pullback.fst _ _ ≫ η[Xo.univ.t.G].left` using `Out.PullGtPf.IsGrpPullback.one_left Y.m0.cart`.

Establish `e3 : η[Y.oF.t.G].left ≫ Y.oF.t.G.hom = 𝟙 _` using `Over.w η[Y.oF.t.G]`. Establish `hsec : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (algebraMap B (DualNumber B)) = 𝟙 _`. Establish `e : (TrivSqZeroExt.fstHom B B B).toRingHom.comp (algebraMap B (DualNumber B)) = RingHom.id B` using `RingHom.ext fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl]`. Rewrite using `[GlobalTheory.Frames.ChgBC.spMap_comp_ring, e, GlobalTheory.Frames.ChgBC.spMap_id]`. Establish `u0 : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ u = y ≫ η[Y.oF.t.G].left`.

Use `hq.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hu1, h0, Category.assoc, e1]`. Rewrite using `[Category.assoc, hu2, ← Category.assoc, hsec, Category.id_comp, Category.assoc, e3]`. Conclude with `(Category.comp_id y).symm`. Use `⟨u ≫ Y.m0.toSABMap.φ, ⟨u, hu2, rfl, hu1⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, hp.w, ← Category.assoc, hu2, Category.assoc]`. Rewrite using `[← Category.assoc, u0, Category.assoc, e2, one_left_eq, Category.assoc]`.
-/
theorem exists_tied (Y : Model Xo c β) {B : Type} [CommRing B] (y : Sp B ⟶ Xo.XF c)
    (v' : Sp (DualNumber B) ⟶ Y.t.G.left)
    (hv : v' ≫ Y.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ y ≫ Y.j)
    (h0 : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ v' = y ≫ Y.j ≫ η[Y.t.G].left) :
    ∃ V, Tied Y y V v' ∧ Formalism.L2.Pj.IsTanAt (y ≫ pullback.fst _ _) V := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have hv2 : v' ≫ Y.t.G.hom = (spMap (algebraMap B (DualNumber B)) ≫ y) ≫ Y.j := by
    rw [Category.assoc]; exact hv
  let u := hq.lift v' (spMap (algebraMap B (DualNumber B)) ≫ y) hv2
  have hu1 : u ≫ Y.m.φ = v' := hq.lift_fst _ _ _
  have hu2 : u ≫ Y.oF.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ y := hq.lift_snd _ _ _
  have e1 : η[Y.oF.t.G].left ≫ Y.m.φ = Y.j ≫ η[Y.t.G].left :=
    Out.PullGtPf.IsGrpPullback.one_left Y.m.cart
  have e2 : η[Y.oF.t.G].left ≫ Y.m0.toSABMap.φ = pullback.fst _ _ ≫ η[Xo.univ.t.G].left :=
    Out.PullGtPf.IsGrpPullback.one_left Y.m0.cart
  have e3 : η[Y.oF.t.G].left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w η[Y.oF.t.G]
  have hsec : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (algebraMap B (DualNumber B)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom B B B).toRingHom.comp (algebraMap B (DualNumber B)) = RingHom.id B :=
      RingHom.ext fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [GlobalTheory.Frames.ChgBC.spMap_comp_ring, e, GlobalTheory.Frames.ChgBC.spMap_id]
  have u0 : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ u = y ≫ η[Y.oF.t.G].left := by
    refine hq.hom_ext ?_ ?_
    · rw [Category.assoc, hu1, h0, Category.assoc, e1]
    · rw [Category.assoc, hu2, ← Category.assoc, hsec, Category.id_comp, Category.assoc, e3]
      exact (Category.comp_id y).symm
  refine ⟨u ≫ Y.m0.toSABMap.φ, ⟨u, hu2, rfl, hu1⟩, ?_, ?_⟩
  · rw [Category.assoc, hp.w, ← Category.assoc, hu2, Category.assoc]
  · rw [← Category.assoc, u0, Category.assoc, e2, one_left_eq, Category.assoc]

/- English proof (translation)
Establish `hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j` using `Y.m.cart.1`. Take `⟨u₁, a₁, b₁, c₁⟩` from `h₁`. Take `⟨u₂, a₂, b₂, c₂⟩` from `h₂`. Establish `: u₁ = u₂` using `hq.hom_ext (c₁.trans c₂.symm) (a₁.trans a₂.symm)`. Rewrite using `[← b₁, ← b₂, this]`.
-/
theorem Tied.unique_left {Y : Model Xo c β} {B : Type} [CommRing B] {y : Sp B ⟶ Xo.XF c}
    {V₁ V₂ : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {v' : Sp (DualNumber B) ⟶ Y.t.G.left}
    (h₁ : Tied Y y V₁ v') (h₂ : Tied Y y V₂ v') : V₁ = V₂ := by
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  obtain ⟨u₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨u₂, a₂, b₂, c₂⟩ := h₂
  have : u₁ = u₂ := hq.hom_ext (c₁.trans c₂.symm) (a₁.trans a₂.symm)
  rw [← b₁, ← b₂, this]

/- English proof (translation)
Take `⟨u, a, b, c⟩` from `h`. Use `⟨spMap (Formalism.L2.Pj.dualMap ρ) ≫ u, ?_, by rw [Category.assoc, b], by rw [Category.assoc, c]⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, a, ← Category.assoc, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_alg]`.
-/
theorem Tied.pull {Y : Model Xo c β} {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B')
    {y : Sp B ⟶ Xo.XF c} {V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {v' : Sp (DualNumber B) ⟶ Y.t.G.left}
    (h : Tied Y y V v') :
    Tied Y (spMap ρ ≫ y) (spMap (Formalism.L2.Pj.dualMap ρ) ≫ V) (spMap (Formalism.L2.Pj.dualMap ρ) ≫ v') := by
  obtain ⟨u, a, b, c⟩ := h
  refine ⟨spMap (Formalism.L2.Pj.dualMap ρ) ≫ u, ?_, by rw [Category.assoc, b], by rw [Category.assoc, c]⟩
  rw [Category.assoc, a, ← Category.assoc, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring,
    GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_alg]

/- English proof (translation)
Take `⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩` from `GlobalTheory.T.exists_tangent_module_universal_group E H D l Xo B xB`. Use `choose b hb using fun τ i => (htan (uu τ i)).1 (hu τ i)`. Take `rfl : uu = fun τ i => v (b τ i)` from `by funext τ i; exact (hb τ i).symm`. Establish `key : ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2 = ∑ i, a σ i • b σ i`. Rewrite using `[e.sum_comp (fun p : Σ τ : E →+* ℂ, Fin (D.mult τ) => a p.1 p.2 • b p.1 p.2), Fintype.sum_sigma, Finset.sum_eq_single σ]`.

Introduce `τ _ hτ`. Simplify using `[ha τ hτ]`. Simplify using the standard rewrite rules. Conclude with `(hcomb _ (fun j => b (e j).1 (e j).2) _ _).trans (by rw [key]; exact (hcomb _ (b σ) _ _).symm)`.
-/
theorem comb_total_iff {B : Type} [CommRing B] (xB : Sp B ⟶ Xo.X)
    (uu : ∀ τ : E →+* ℂ, Fin (D.mult τ) → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left))
    (hu : ∀ τ i, Formalism.L2.Pj.IsTanAt xB (uu τ i)) {n : ℕ} (e : Fin n ≃ Σ τ : E →+* ℂ, Fin (D.mult τ))
    (a : ∀ τ : E →+* ℂ, Fin (D.mult τ) → B) (σ : E →+* ℂ) (ha : ∀ τ, τ ≠ σ → a τ = 0)
    (w : Sp (DualNumber B) ⟶ Xo.univ.t.G.left) :
    Formalism.L2.Pj.IsCombAt xB (fun j => uu (e j).1 (e j).2) (fun j => a (e j).1 (e j).2) w ↔
      Formalism.L2.Pj.IsCombAt xB (uu σ) (a σ) w := by
  classical
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H D l Xo B xB
  choose b hb using fun τ i => (htan (uu τ i)).1 (hu τ i)
  obtain rfl : uu = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  have key : ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2 = ∑ i, a σ i • b σ i := by
    rw [e.sum_comp (fun p : Σ τ : E →+* ℂ, Fin (D.mult τ) => a p.1 p.2 • b p.1 p.2), Fintype.sum_sigma,
      Finset.sum_eq_single σ]
    · intro τ _ hτ
      simp [ha τ hτ]
    · simp
  exact (hcomb _ (fun j => b (e j).1 (e j).2) _ _).trans
    (by rw [key]; exact (hcomb _ (b σ) _ _).symm)

/- English proof (translation)
Take `⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩` from `GlobalTheory.T.exists_tangent_module_universal_group E H D l Xo B xB`. Use `choose b hb using fun i => (htan (u i)).1 (hu i)`. Take `rfl : u = fun i => v (b i)` from `by funext i; exact (hb i).symm`. Rewrite using `[(hcomb _ b _ _).1 h]`. Conclude with `(htan _).2 ⟨_, rfl⟩`.
-/
theorem isTanAt_of_comb {B : Type} [CommRing B] {xB : Sp B ⟶ Xo.X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left)} (hu : ∀ i, Formalism.L2.Pj.IsTanAt xB (u i))
    {a : Fin m → B} {w : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt xB u a w) :
    Formalism.L2.Pj.IsTanAt xB w := by
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H D l Xo B xB
  choose b hb using fun i => (htan (u i)).1 (hu i)
  obtain rfl : u = fun i => v (b i) := by funext i; exact (hb i).symm
  rw [(hcomb _ b _ _).1 h]
  exact (htan _).2 ⟨_, rfl⟩

open MonoidalCategory CartesianMonoidalCategory MonObj in

/- English proof (translation)
Use `exists_tied Y y _ ?_ ?_` and prove the remaining obligations. Establish `hw : v.left ≫ Y.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x` using `Over.w v`. Rewrite using `[Category.assoc, hw, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_alg, ← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, h]`. Establish `hv' : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = x ≫ η[Y.t.G].left` using `(show _ = _ from hv).trans (one_left_eq Y.t.G x)`. Rewrite using `[← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, fst_dualMap, ← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, hv', ← Category.assoc, h, Category.assoc]`.
-/
theorem tan_pull (Y : Model Xo c β) {R B : Type} [CommRing R] [CommRing B] {x : Sp R ⟶ Y.X} (θ₀ : R →+* B)
    (y : Sp B ⟶ Xo.XF c) (h : spMap θ₀ ≫ x = y ≫ Y.j) (v : epsAt x ⟶ Y.t.G) (hv : IsTanAt Y.t.G x v) :
    ∃ V, Tied Y y V (spMap (Formalism.L2.Pj.dualMap θ₀) ≫ v.left) ∧ Formalism.L2.Pj.IsTanAt (y ≫ pullback.fst _ _) V := by
  refine exists_tied Y y _ ?_ ?_
  · have hw : v.left ≫ Y.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := Over.w v
    rw [Category.assoc, hw, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring,
      GlobalTheory.Frames.ChgBC.dualMap_alg, ← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, h]
  · have hv' : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = x ≫ η[Y.t.G].left :=
      (show _ = _ from hv).trans (one_left_eq Y.t.G x)
    rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, fst_dualMap,
      ← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, hv', ← Category.assoc, h, Category.assoc]

/- English proof (translation)
The claim follows from `(fun p : (Σ τ : E →+* ℂ, Fin (D.mult τ)) => by obtain ⟨j, rfl⟩ := e.surjective p exact h.1 j : ∀ p : (Σ τ : E →+* ℂ, Fin (D.mult τ)), Formalism.L2.Pj.IsTanAt xB (uu p.1 p.2)) ⟨τ, k⟩`.
-/
theorem tan_family {B : Type} [CommRing B] {xB : Sp B ⟶ Xo.X}
    {uu : ∀ τ : E →+* ℂ, Fin (D.mult τ) → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left)}
    {n : ℕ} (e : Fin n ≃ Σ τ : E →+* ℂ, Fin (D.mult τ))
    (h : GlobalTheory.Frames.TanBasis xB (fun j => uu (e j).1 (e j).2)) (τ : E →+* ℂ) (k : Fin (D.mult τ)) :
    Formalism.L2.Pj.IsTanAt xB (uu τ k) :=
  (fun p : (Σ τ : E →+* ℂ, Fin (D.mult τ)) => by
    obtain ⟨j, rfl⟩ := e.surjective p
    exact h.1 j : ∀ p : (Σ τ : E →+* ℂ, Fin (D.mult τ)), Formalism.L2.Pj.IsTanAt xB (uu p.1 p.2)) ⟨τ, k⟩

/- English proof (translation)
Set `φ₀` to `algebraMap S (Localization.Away g₀)`. Set `φT` to `algebraMap S (Localization.AtPrime q)`. Set `n` to `Fintype.card (Σ τ : E →+* ℂ, Fin (D.mult τ))`. Set `ee : Fin n ≃ Σ τ : E →+* ℂ, Fin (D.mult τ)` to `(Fintype.equivFin _).symm`. Establish `hB : GlobalTheory.Frames.TanBasis z.x (fun j => z.u (ee j).1 (ee j).2)` using `(GlobalTheory.Frames.eigBasis_iff_tanBasis E H D l Xo c S z.x z.u n ee z.tan z.eig).1 z.basis`.

Establish `hB₀` using `GlobalTheory.Frames.tanBasis_baseChange E H D l Xo S _ φ₀ z.x n _ hB`. Establish `hBT` using `GlobalTheory.Frames.tanBasis_baseChange E H D l Xo S _ φT z.x n _ hB`. Establish `hv : ∀ i, ∃ V₀, Tied Y (spMap φ₀ ≫ zPt z) V₀ (spMap (Formalism.L2.Pj.dualMap θ₀) ≫ (e i).left) ∧ Formalism.L2.Pj.IsTanAt (spMap φ₀ ≫ z.x) V₀`. Introduce `i`. Take `⟨V, h1, h2⟩` from `tan_pull Y θ₀ (spMap φ₀ ≫ zPt z) (by rw [hθ₀, Category.assoc]) (e i) (ht i)`.

Use `⟨V, h1, ?_⟩` and prove the remaining obligations. Rewrite `h2` using `[Category.assoc, zPt_fst]`. Then use the resulting hypothesis. Use `choose V₀ hV₀ hV₀t using hv`. Use `choose a ha hau using fun i => hB₀.2 (V₀ i) (hV₀t i)`. Establish `hι' : ι.comp φ₀ = φT` using `hι`.

Set `sg : Fin (D.mult σ) → ∀ τ : E →+* ℂ, Fin (D.mult τ) → Localization.AtPrime q` to `fun i => Pi.single (M := fun τ : E →+* ℂ => Fin (D.mult τ) → Localization.AtPrime q) σ (C i)`. Establish `hsgσ : ∀ i, sg i σ = C i` using `fun i => Pi.single_eq_same _ _`. Establish `hsg0 : ∀ i τ, τ ≠ σ → sg i τ = 0` using `fun i τ h => Pi.single_eq_of_ne h _`. Establish `key : ∀ i j, ι (a i j) = sg i (ee j).1 (ee j).2`. Introduce `i j`.

Take `⟨V, hVt, hVc⟩` from `hyp i`. Establish `h1` using `Tied.pull ι (hV₀ i)`. Establish `hy : spMap ι ≫ spMap φ₀ ≫ zPt z = spMap φT ≫ zPt z`. Rewrite using `[← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, hι']`. Establish `hv' : spMap (Formalism.L2.Pj.dualMap ι) ≫ spMap (Formalism.L2.Pj.dualMap θ₀) ≫ (e i).left = spMap (Formalism.L2.Pj.dualMap θ) ≫ (e i).left`.

Rewrite using `[← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp, hιθ]`. Rewrite `h1` using `[hy, hv']`. Establish `hVV` using `Tied.unique_left h1 hVt`. Establish `hxT : spMap φT ≫ z.x = spMap ι ≫ spMap φ₀ ≫ z.x`. Rewrite using `[← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, hι']`.

Establish `c1 : Formalism.L2.Pj.IsCombAt (spMap φT ≫ z.x) (fun j => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u (ee j).1 (ee j).2) (fun j => ι (a i j)) V` using `GlobalTheory.Frames.ChgBC.isCombAt_pull ι hxT (fun j => by rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp, hι']) hVV.symm (ha i)`. Establish `hT` using `tan_family (uu := fun τ k => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u τ k) ee hBT`. Establish `c2 : Formalism.L2.Pj.IsCombAt (spMap φT ≫ z.x) (fun j => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u (ee j).1 (ee j).2) (fun j => sg i (ee j).1 (ee j).2) V` using `(comb_total_iff _ (fun τ k => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u τ k) hT ee (sg i) σ (hsg0 i) V).2 (by rw [hsgσ]; exact hVc)`. Establish `hVtan` using `isTanAt_of_comb hBT.1 c1`. Conclude with `congrFun ((hBT.2 V hVtan).unique c1 c2) j`.

Set `M : Matrix (Fin (D.mult σ)) (Fin (D.mult σ)) (Localization.Away g₀)` to `fun i k => a i (ee.symm ⟨σ, k⟩)`. Establish `hM : ∀ i k, ι (M i k) = C i k`. Introduce `i k`. Establish `h1` using `key i (ee.symm ⟨σ, k⟩)`. Establish `h2 : ∀ p : (Σ τ : E →+* ℂ, Fin (D.mult τ)), p = ⟨σ, k⟩ → sg i p.1 p.2 = C i k`.

Introduce and unpack `_ rfl`. Conclude with `congrFun (hsgσ i) k`. Conclude with `h1.trans (h2 _ (ee.apply_symm_apply _))`. Use `⟨Finset.univ.image (fun p : Fin (D.mult σ) × Fin n => if (ee p.2).1 = σ then 0 else a p.1 p.2), M.det, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb`.

Take `⟨⟨i, j⟩, -, rfl⟩` from `Finset.mem_image.1 hb`. Simplify using `only`. Use `split_ifs with h`. Conclude with `map_zero ι`. Rewrite using `[key, hsg0 i _ h]`.

Both sides reduce to the same expression. Establish `h1 : ι M.det = C.det`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i k`.

Conclude with `hM i k`. Rewrite using `[h1]`. Conclude with `hC`. Introduce `B _ ρ hZ hd`. Establish `hρ0 : ∀ i j, (ee j).1 ≠ σ → ρ (a i j) = 0`.

Introduce `i j h`. Conclude with `hZ (a i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, by simp [h]⟩)`. Establish `hBB` using `GlobalTheory.Frames.tanBasis_baseChange E H D l Xo S B (ρ.comp φ₀) z.x n _ hB`. Use `⟨M.map ρ, ?_, fun i => ⟨spMap (Formalism.L2.Pj.dualMap ρ) ≫ V₀ i, ?_, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : (M.map ρ).det = ρ M.det`.

Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `hd`. Establish `h1` using `Tied.pull ρ (hV₀ i)`.

Establish `hy : spMap ρ ≫ spMap φ₀ ≫ zPt z = spMap (ρ.comp φ₀) ≫ zPt z`. Rewrite using `[← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring]`. Establish `hv' : spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (Formalism.L2.Pj.dualMap θ₀) ≫ (e i).left = spMap (Formalism.L2.Pj.dualMap (ρ.comp θ₀)) ≫ (e i).left`. Rewrite using `[← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp]`. Rewrite `h1` using `[hy, hv']`.

Conclude with `h1`. Set `A : ∀ τ : E →+* ℂ, Fin (D.mult τ) → B` to `fun τ k => ρ (a i (ee.symm ⟨τ, k⟩))`. Establish `hA0 : ∀ τ, τ ≠ σ → A τ = 0`. Introduce `τ h`. Use function extensionality and compare the values at `k`.

Use `hρ0 i _ ?_` and prove the remaining obligations. Rewrite using `[ee.apply_symm_apply]`. Conclude with `h`. Establish `hx : spMap (ρ.comp φ₀) ≫ z.x = spMap ρ ≫ spMap φ₀ ≫ z.x`. Rewrite using `[← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring]`.

Establish `c1 : Formalism.L2.Pj.IsCombAt (spMap (ρ.comp φ₀) ≫ z.x) (fun j => spMap (Formalism.L2.Pj.dualMap (ρ.comp φ₀)) ≫ z.u (ee j).1 (ee j).2) (fun j => ρ (a i j)) (spMap (Formalism.L2.Pj.dualMap ρ) ≫ V₀ i)` using `GlobalTheory.Frames.ChgBC.isCombAt_pull ρ hx (fun j => by rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp]) rfl (ha i)`. Establish `hAe : (fun j => ρ (a i j)) = fun j => A (ee j).1 (ee j).2`. Use function extensionality and compare the values at `j`. Simplify using `[A]`. Rewrite `c1` using `[hAe]`.

Conclude with `(comb_total_iff _ (fun τ k => spMap (Formalism.L2.Pj.dualMap (ρ.comp φ₀)) ≫ z.u τ k) (tan_family (uu := fun τ k => spMap (Formalism.L2.Pj.dualMap (ρ.comp φ₀)) ≫ z.u τ k) ee hBB) ee A σ hA0 _).1 c1`.
-/
theorem spread_family (Y : Model Xo c β) {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S)
    (q : Ideal S) [q.IsPrime] {R : Type} [CommRing R] (x : Sp R ⟶ Y.X) (θ : R →+* Localization.AtPrime q)
    (σ : E →+* ℂ) (e : Fin (D.mult σ) → (epsAt x ⟶ Y.t.G))
    (C : Matrix (Fin (D.mult σ)) (Fin (D.mult σ)) (Localization.AtPrime q)) (g₀ : S)
    (θ₀ : R →+* Localization.Away g₀) (ι : Localization.Away g₀ →+* Localization.AtPrime q)
    (hι : ι.comp (algebraMap S _) = algebraMap S _) (hιθ : ι.comp θ₀ = θ)
    (hθ₀ : spMap θ₀ ≫ x = spMap (algebraMap S (Localization.Away g₀)) ≫ zPt z ≫ Y.j)
    (ht : ∀ i, IsTanAt Y.t.G x (e i)) (hC : IsUnit C.det)
    (hyp : ∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left,
      Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V
        (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e i).left) ∧
      Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x)
        (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u σ k) (C i) V) :
    ∃ (Z : Finset (Localization.Away g₀)) (d : Localization.Away g₀), (∀ b ∈ Z, ι b = 0) ∧ IsUnit (ι d) ∧
      ∀ (B : Type) [CommRing B] (ρ : Localization.Away g₀ →+* B), (∀ b ∈ Z, ρ b = 0) → IsUnit (ρ d) →
        ∃ C' : Matrix (Fin (D.mult σ)) (Fin (D.mult σ)) B, IsUnit C'.det ∧
          ∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left,
            Tied Y (spMap (ρ.comp (algebraMap S _)) ≫ zPt z) V
              (spMap (Formalism.L2.Pj.dualMap (ρ.comp θ₀)) ≫ (e i).left) ∧
            Formalism.L2.Pj.IsCombAt (spMap (ρ.comp (algebraMap S _)) ≫ z.x)
              (fun k => spMap (Formalism.L2.Pj.dualMap (ρ.comp (algebraMap S _))) ≫ z.u σ k) (C' i) V := by
  classical
  let φ₀ := algebraMap S (Localization.Away g₀)
  let φT := algebraMap S (Localization.AtPrime q)
  let n := Fintype.card (Σ τ : E →+* ℂ, Fin (D.mult τ))
  let ee : Fin n ≃ Σ τ : E →+* ℂ, Fin (D.mult τ) := (Fintype.equivFin _).symm
  have hB : GlobalTheory.Frames.TanBasis z.x (fun j => z.u (ee j).1 (ee j).2) :=
    (GlobalTheory.Frames.eigBasis_iff_tanBasis E H D l Xo c S z.x z.u n ee z.tan z.eig).1 z.basis
  have hB₀ := GlobalTheory.Frames.tanBasis_baseChange E H D l Xo S _ φ₀ z.x n _ hB
  have hBT := GlobalTheory.Frames.tanBasis_baseChange E H D l Xo S _ φT z.x n _ hB
  have hv : ∀ i, ∃ V₀, Tied Y (spMap φ₀ ≫ zPt z) V₀ (spMap (Formalism.L2.Pj.dualMap θ₀) ≫ (e i).left) ∧
      Formalism.L2.Pj.IsTanAt (spMap φ₀ ≫ z.x) V₀ := by
    intro i
    obtain ⟨V, h1, h2⟩ := tan_pull Y θ₀ (spMap φ₀ ≫ zPt z) (by rw [hθ₀, Category.assoc]) (e i) (ht i)
    refine ⟨V, h1, ?_⟩
    rwa [Category.assoc, zPt_fst] at h2
  choose V₀ hV₀ hV₀t using hv
  choose a ha hau using fun i => hB₀.2 (V₀ i) (hV₀t i)
  have hι' : ι.comp φ₀ = φT := hι
  let sg : Fin (D.mult σ) → ∀ τ : E →+* ℂ, Fin (D.mult τ) → Localization.AtPrime q := fun i =>
    Pi.single (M := fun τ : E →+* ℂ => Fin (D.mult τ) → Localization.AtPrime q) σ (C i)
  have hsgσ : ∀ i, sg i σ = C i := fun i => Pi.single_eq_same _ _
  have hsg0 : ∀ i τ, τ ≠ σ → sg i τ = 0 := fun i τ h => Pi.single_eq_of_ne h _
  have key : ∀ i j, ι (a i j) = sg i (ee j).1 (ee j).2 := by
    intro i j
    obtain ⟨V, hVt, hVc⟩ := hyp i
    have h1 := Tied.pull ι (hV₀ i)
    have hy : spMap ι ≫ spMap φ₀ ≫ zPt z = spMap φT ≫ zPt z := by
      rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, hι']
    have hv' : spMap (Formalism.L2.Pj.dualMap ι) ≫ spMap (Formalism.L2.Pj.dualMap θ₀) ≫ (e i).left =
        spMap (Formalism.L2.Pj.dualMap θ) ≫ (e i).left := by
      rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp, hιθ]
    rw [hy, hv'] at h1
    have hVV := Tied.unique_left h1 hVt
    have hxT : spMap φT ≫ z.x = spMap ι ≫ spMap φ₀ ≫ z.x := by
      rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, hι']
    have c1 : Formalism.L2.Pj.IsCombAt (spMap φT ≫ z.x)
        (fun j => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u (ee j).1 (ee j).2) (fun j => ι (a i j)) V :=
      GlobalTheory.Frames.ChgBC.isCombAt_pull ι hxT
        (fun j => by rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp, hι']) hVV.symm (ha i)
    have hT := tan_family (uu := fun τ k => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u τ k) ee hBT
    have c2 : Formalism.L2.Pj.IsCombAt (spMap φT ≫ z.x)
        (fun j => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u (ee j).1 (ee j).2)
        (fun j => sg i (ee j).1 (ee j).2) V :=
      (comb_total_iff _ (fun τ k => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u τ k) hT ee (sg i) σ (hsg0 i) V).2
        (by rw [hsgσ]; exact hVc)
    have hVtan := isTanAt_of_comb hBT.1 c1
    exact congrFun ((hBT.2 V hVtan).unique c1 c2) j
  let M : Matrix (Fin (D.mult σ)) (Fin (D.mult σ)) (Localization.Away g₀) :=
    fun i k => a i (ee.symm ⟨σ, k⟩)
  have hM : ∀ i k, ι (M i k) = C i k := by
    intro i k
    have h1 := key i (ee.symm ⟨σ, k⟩)
    have h2 : ∀ p : (Σ τ : E →+* ℂ, Fin (D.mult τ)), p = ⟨σ, k⟩ → sg i p.1 p.2 = C i k := by
      rintro _ rfl
      exact congrFun (hsgσ i) k
    exact h1.trans (h2 _ (ee.apply_symm_apply _))
  refine ⟨Finset.univ.image (fun p : Fin (D.mult σ) × Fin n =>
    if (ee p.2).1 = σ then 0 else a p.1 p.2), M.det, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.1 hb
    dsimp only
    split_ifs with h
    · exact map_zero ι
    · rw [key, hsg0 i _ h]
      rfl
  · have h1 : ι M.det = C.det := by
      rw [RingHom.map_det]
      congr 1
      ext i k
      exact hM i k
    rw [h1]
    exact hC
  · intro B _ ρ hZ hd
    have hρ0 : ∀ i j, (ee j).1 ≠ σ → ρ (a i j) = 0 := by
      intro i j h
      exact hZ (a i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, by simp [h]⟩)
    have hBB := GlobalTheory.Frames.tanBasis_baseChange E H D l Xo S B (ρ.comp φ₀) z.x n _ hB
    refine ⟨M.map ρ, ?_, fun i => ⟨spMap (Formalism.L2.Pj.dualMap ρ) ≫ V₀ i, ?_, ?_⟩⟩
    · have h1 : (M.map ρ).det = ρ M.det := by
        rw [RingHom.map_det]
        rfl
      rw [h1]
      exact hd
    · have h1 := Tied.pull ρ (hV₀ i)
      have hy : spMap ρ ≫ spMap φ₀ ≫ zPt z = spMap (ρ.comp φ₀) ≫ zPt z := by
        rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring]
      have hv' : spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (Formalism.L2.Pj.dualMap θ₀) ≫ (e i).left =
          spMap (Formalism.L2.Pj.dualMap (ρ.comp θ₀)) ≫ (e i).left := by
        rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp]
      rw [hy, hv'] at h1
      exact h1
    · let A : ∀ τ : E →+* ℂ, Fin (D.mult τ) → B := fun τ k => ρ (a i (ee.symm ⟨τ, k⟩))
      have hA0 : ∀ τ, τ ≠ σ → A τ = 0 := by
        intro τ h
        funext k
        refine hρ0 i _ ?_
        rw [ee.apply_symm_apply]
        exact h
      have hx : spMap (ρ.comp φ₀) ≫ z.x = spMap ρ ≫ spMap φ₀ ≫ z.x := by
        rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring]
      have c1 : Formalism.L2.Pj.IsCombAt (spMap (ρ.comp φ₀) ≫ z.x)
          (fun j => spMap (Formalism.L2.Pj.dualMap (ρ.comp φ₀)) ≫ z.u (ee j).1 (ee j).2) (fun j => ρ (a i j))
          (spMap (Formalism.L2.Pj.dualMap ρ) ≫ V₀ i) :=
        GlobalTheory.Frames.ChgBC.isCombAt_pull ρ hx
          (fun j => by rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp]) rfl (ha i)
      have hAe : (fun j => ρ (a i j)) = fun j => A (ee j).1 (ee j).2 := by
        funext j
        simp [A]
      rw [hAe] at c1
      exact (comb_total_iff _ (fun τ k => spMap (Formalism.L2.Pj.dualMap (ρ.comp φ₀)) ≫ z.u τ k)
        (tan_family (uu := fun τ k => spMap (Formalism.L2.Pj.dualMap (ρ.comp φ₀)) ≫ z.u τ k) ee hBB) ee A σ hA0 _).1 c1

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y S _ _ z q _ R _ x _ θ σ₁ σ₂ n₁ n₂ h₁ h₂ e₁ e₂ C₁ C₂ hθ ht₁ ht₂ hC₁ hC₂ hy₁ hy₂`. Substitute `h₁ h₂` using the available equality. Take `⟨g₀, θ₀, hg₀, hθ₀, hι⟩` from `exists_away_lift x (zPt z ≫ Y.j) q θ hθ`. Establish `hu₀ : IsUnit (algebraMap S (Localization.AtPrime q) g₀)` using `(IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q g₀).2 hg₀`. Set `ι : Localization.Away g₀ →+* Localization.AtPrime q` to `IsLocalization.Away.lift g₀ hu₀`.

Establish `hιφ : ι.comp (algebraMap S _) = algebraMap S _` using `IsLocalization.Away.lift_comp g₀ hu₀`. Take `⟨Z₁, d₁, hZ₁, hd₁, F₁⟩` from `spread_family Y z q x θ σ₁ e₁ C₁ g₀ θ₀ ι hιφ (hι ι hιφ) hθ₀ ht₁ hC₁ hy₁`. Take `⟨Z₂, d₂, hZ₂, hd₂, F₂⟩` from `spread_family Y z q x θ σ₂ e₂ C₂ g₀ θ₀ ι hιφ (hι ι hιφ) hθ₀ ht₂ hC₂ hy₂`. Take `⟨g, ρ, hg, hρ, hZ, hd⟩` from `exists_spread q g₀ hg₀ ι hιφ (Z₁ ∪ Z₂) (fun b hb => (Finset.mem_union.1 hb).elim (hZ₁ b) (hZ₂ b)) (d₁ * d₂) (by rw [map_mul]; exact hd₁.mul hd₂)`. Rewrite `hd` using `[map_mul]`.

Take `⟨C₁', u₁, G₁⟩` from `F₁ (Localization.Away g) ρ (fun b hb => hZ b (Finset.mem_union_left _ hb)) (isUnit_of_mul_isUnit_left hd)`. Take `⟨C₂', u₂, G₂⟩` from `F₂ (Localization.Away g) ρ (fun b hb => hZ b (Finset.mem_union_right _ hb)) (isUnit_of_mul_isUnit_right hd)`. Rewrite `G₁`, `G₂` using `[hρ]`. Use `⟨g, ρ.comp θ₀, C₁', C₂', hg, ?_, u₁, u₂, G₁, G₂⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, hθ₀, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, hρ]`.
-/
theorem exists_away_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (q : Ideal S) [q.IsPrime] (R : Type) [CommRing R] (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (θ : R →+* (Localization.AtPrime q)) (σ₁ σ₂ : E →+* ℂ) (n₁ n₂ : ℕ) (h₁ : D.mult σ₁ = n₁) (h₂ : D.mult σ₂ = n₂) (e₁ : Fin n₁ → (epsAt x ⟶ Y.t.G)) (e₂ : Fin n₂ → (epsAt x ⟶ Y.t.G)) (C₁ : Matrix (Fin n₁) (Fin n₁) (Localization.AtPrime q)) (C₂ : Matrix (Fin n₂) (Fin n₂) (Localization.AtPrime q)), spMap θ ≫ x = spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z ≫ Y.j → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) → IsUnit C₁.det → IsUnit C₂.det → (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u σ₁ (k.cast h₁.symm)) (C₁ i) V) → (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u σ₂ (k.cast h₂.symm)) (C₂ i) V) → ∃ (g : S) (θ' : R →+* (Localization.Away g)) (C₁' : Matrix (Fin n₁) (Fin n₁) (Localization.Away g)) (C₂' : Matrix (Fin n₂) (Fin n₂) (Localization.Away g)), g ∉ q ∧ spMap θ' ≫ x = spMap (algebraMap S (Localization.Away g)) ≫ zPt z ≫ Y.j ∧ IsUnit C₁'.det ∧ IsUnit C₂'.det ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.Away g)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.Away g)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ') ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.Away g)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.Away g))) ≫ z.u σ₁ (k.cast h₁.symm)) (C₁' i) V) ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.Away g)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.Away g)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ') ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.Away g)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.Away g))) ≫ z.u σ₂ (k.cast h₂.symm)) (C₂' i) V) := by
  intro E _ _ _ H D l Xo c O _ β Y S _ _ z q _ R _ x _ θ σ₁ σ₂ n₁ n₂ h₁ h₂ e₁ e₂ C₁ C₂ hθ ht₁ ht₂ hC₁ hC₂ hy₁ hy₂
  subst h₁ h₂
  obtain ⟨g₀, θ₀, hg₀, hθ₀, hι⟩ := exists_away_lift x (zPt z ≫ Y.j) q θ hθ
  have hu₀ : IsUnit (algebraMap S (Localization.AtPrime q) g₀) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q g₀).2 hg₀
  let ι : Localization.Away g₀ →+* Localization.AtPrime q := IsLocalization.Away.lift g₀ hu₀
  have hιφ : ι.comp (algebraMap S _) = algebraMap S _ := IsLocalization.Away.lift_comp g₀ hu₀
  obtain ⟨Z₁, d₁, hZ₁, hd₁, F₁⟩ := spread_family Y z q x θ σ₁ e₁ C₁ g₀ θ₀ ι hιφ (hι ι hιφ) hθ₀ ht₁ hC₁ hy₁
  obtain ⟨Z₂, d₂, hZ₂, hd₂, F₂⟩ := spread_family Y z q x θ σ₂ e₂ C₂ g₀ θ₀ ι hιφ (hι ι hιφ) hθ₀ ht₂ hC₂ hy₂
  classical
  obtain ⟨g, ρ, hg, hρ, hZ, hd⟩ := exists_spread q g₀ hg₀ ι hιφ (Z₁ ∪ Z₂)
    (fun b hb => (Finset.mem_union.1 hb).elim (hZ₁ b) (hZ₂ b)) (d₁ * d₂)
    (by rw [map_mul]; exact hd₁.mul hd₂)
  rw [map_mul] at hd
  obtain ⟨C₁', u₁, G₁⟩ := F₁ (Localization.Away g) ρ (fun b hb => hZ b (Finset.mem_union_left _ hb))
    (isUnit_of_mul_isUnit_left hd)
  obtain ⟨C₂', u₂, G₂⟩ := F₂ (Localization.Away g) ρ (fun b hb => hZ b (Finset.mem_union_right _ hb))
    (isUnit_of_mul_isUnit_right hd)
  rw [hρ] at G₁ G₂
  refine ⟨g, ρ.comp θ₀, C₁', C₂', hg, ?_, u₁, u₂, G₁, G₂⟩
  rw [← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, hθ₀, ← Category.assoc,
    GlobalTheory.Frames.ChgBC.spMap_comp_ring, hρ]

end GlobalTheory.CompanionTheory.Ar.LocFn.Spread
