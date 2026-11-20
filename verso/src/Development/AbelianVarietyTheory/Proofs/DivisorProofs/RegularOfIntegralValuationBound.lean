import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.Mean4O.Cover.RegCrit

open GlobalTheory.TrueGeo.HorizPt in

/- English proof (translation)
Use `V.ar.flat` as an intermediate fact. Establish `: IsProper V.p`. Take `⟨n, c, hc, h⟩` from `V.ar.isProjOver`. Use `isProper_str (𝓞 F) n` as an intermediate fact. Rewrite using `[← h]`.

Use `infer_instance`. Take `⟨U, hU, hzU, hUW⟩` from `exists_isAffineOpen_mem_and_subset hz`. Establish `hle : U ≤ W` using `hUW`. Establish `: Nonempty U` using `⟨⟨z, hzU⟩⟩`. Establish `: CharZero Γ(V.X, U)` using `charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU`.

Set `_ : Algebra (𝓞 F) Γ(V.X, U)` to `(GlobalTheory.TrueGeo.HorizPt.strHom V.p U).hom.toAlgebra`. Establish `: Algebra.FiniteType (𝓞 F) Γ(V.X, U)` using `RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top) (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)`. Use `set g' : Γ(V.X, U) := V.X.presheaf.map (homOfLE hle).op g with hg'`. Establish `hg0 : g' ≠ 0` using `fun h => hg (map_injective_of_isIntegral V.X (homOfLE hle) (by rw [← hg', h, map_zero]))`. Establish `hb : ∀ x : PrimeSpectrum Γ(V.X, U), hU.fromSpec x ∈ V.X.basicOpen g ↔ g' ∉ x.asIdeal`.

Introduce `x`. Establish `h₁ : hU.fromSpec x ∈ U`. Use `hU.range_fromSpec` as an intermediate fact. Conclude with `(Set.ext_iff.1 this _).1 ⟨x, rfl⟩`. Establish `h₂ : hU.fromSpec x ∈ V.X.basicOpen g' ↔ g' ∉ x.asIdeal`.

Express the relevant statement in the definitionally equal form `x ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen g' ↔ _`. Rewrite using `[hU.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression. Rewrite using `[← h₂, hg', Scheme.basicOpen_res]`. Conclude with `⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩`.

Establish `hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal`. Assume the negation of the conclusion as `h`. Use `(hb _).2 h` as an intermediate fact. Rewrite `this` using `[hU.fromSpec_primeIdealOf]`. Conclude with `hzg this`.

Take `⟨𝔪, h𝔪, hle'⟩` from `Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top`. Take `⟨v, e, φ, h₁, h₂, h₃⟩` from `GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U) 𝔪 h𝔪 g' hg0`. Set `yt : Sp e.O ⟶ V.X` to `Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec`. Establish `hw : (spMap e.O.subtype ≫ yt) ≫ V.p = spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F)`. Simplify using `only [yt, Category.assoc]`.

Rewrite using `[fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `a`. Conclude with `h₁ a`. Establish `hy` using `V.pb.lift_fst _ _ hw`.

Use `⟨v, e, V.pb.lift _ _ hw, yt, V.pb.lift_snd _ _ hw, hy.symm, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x _`. Conclude with `hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)`. Introduce `h`. Use `(hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_` and prove the remaining obligations.

Use `hle' hp` as an intermediate fact. Rewrite `this` using `[← h₂]`. Conclude with `this`. Express the relevant statement in the definitionally equal form `(V.pb.lift _ _ hw ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _`. Rewrite using `[hy]`.

Use `(hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_` and prove the remaining obligations. Establish `h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F)` using `h`. Rewrite `h'` using `[IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]`. Conclude with `Subtype.ext h'`.
-/
theorem exists_horizPt {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (W : V.X.Opens) (z : V.X)
    (g : Γ(V.X, W)) (hz : z ∈ W) (hg : g ≠ 0) (hzg : z ∉ V.X.basicOpen g) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      y ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = y ≫ V.j ∧
      ⊤ ≤ yt ⁻¹ᵁ W ∧ yt (IsLocalRing.closedPoint e.O) ∉ V.X.basicOpen g ∧ below (y ≫ V.j) ∈ V.X.basicOpen g := by
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (GlobalTheory.TrueGeo.HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  set g' : Γ(V.X, U) := V.X.presheaf.map (homOfLE hle).op g with hg'
  have hg0 : g' ≠ 0 := fun h => hg (map_injective_of_isIntegral V.X (homOfLE hle) (by rw [← hg', h, map_zero]))
  have hb : ∀ x : PrimeSpectrum Γ(V.X, U), hU.fromSpec x ∈ V.X.basicOpen g ↔ g' ∉ x.asIdeal := by
    intro x
    have h₁ : hU.fromSpec x ∈ U := by
      have := hU.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨x, rfl⟩
    have h₂ : hU.fromSpec x ∈ V.X.basicOpen g' ↔ g' ∉ x.asIdeal := by
      change x ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen g' ↔ _
      rw [hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← h₂, hg', Scheme.basicOpen_res]
    exact ⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩
  have hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra h
    have := (hb _).2 h
    rw [hU.fromSpec_primeIdealOf] at this
    exact hzg this
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U) 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  refine ⟨v, e, V.pb.lift _ _ hw, yt, V.pb.lift_snd _ _ hw, hy.symm, ?_, ?_, ?_⟩
  · intro x _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro h
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (V.pb.lift _ _ hw ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
    have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'

open GlobalTheory.TrueGeo.RegCrit in

/- English proof (translation)
Introduce `F _ _ Y V U f hf x hx`. Establish `: IsProper V.p`. Take `⟨n, c, hc, h⟩` from `V.ar.isProjOver`. Use `isProper_str (𝓞 F) n` as an intermediate fact. Rewrite using `[← h]`.

Use `infer_instance`. Establish `: IsLocallyNoetherian V.X` using `LocallyOfFiniteType.isLocallyNoetherian V.p`. Assume the negation of the conclusion as `hreg`. Take `⟨z, hz, hzero⟩` from `GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal V.X V.normal x f hreg`. Establish `hf0 : f ≠ 0` using `fun h => hreg (h ▸ regAt_zero x)`.

Establish `hzU : z ∈ U` using `hz.mem_open U.isOpen hx`. Take `⟨W₀, hzW, g₀, hg₀⟩` from `hzero.regAt.exists_fnOf`. Establish `hzW' : z ∈ W₀ ⊓ U` using `⟨hzW, hzU⟩`. Take `⟨g, hg⟩ : ∃ g : Γ(V.X, W₀ ⊓ U), ∀ h, fnOf _ h g = f⁻¹` from `⟨resG V.X inf_le_left g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩`. Establish `hg0 : g ≠ 0` using `fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzW'), h, map_zero])`.

Establish `hzg : z ∉ V.X.basicOpen g` using `fun h => (zeroAt_iff.1 hzero).2 (hg (gen_mem hzW') ▸ (unitAt_fnOf_iff hzW' _ g).2 h)`. Take `⟨v, e, y, yt, hy, hc, hW, hn, hu⟩` from `exists_horizPt V _ z g hzW' hg0 hzg`. Establish `hle` using `hf v e y yt hy hc fun p hp => (hW hp).2`. Establish `hu' : below (y ≫ V.j) ∈ V.X.basicOpen g` using `hu`. Establish `hb : below (y ≫ V.j) ∈ W₀ ⊓ U` using `V.X.basicOpen_le g hu'`.

Establish `ht : ⊤ ≤ (y ≫ V.j) ⁻¹ᵁ (W₀ ⊓ U)` using `fun p _ => by`. Express the relevant statement in the definitionally equal form `(y ≫ V.j) p ∈ W₀ ⊓ U`. Rewrite using `[← hc]`. Conclude with `hW (x := spMap e.O.subtype p) trivial`. Establish `hunit : UnitAt (below (y ≫ V.j)) f⁻¹` using `hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'`.

Establish `hfu : UnitAt (below (y ≫ V.j)) f` using `inv_inv f ▸ hunit.inv`. Establish `hmul` using `OfModel.valAt_mul (y ≫ V.j) hfu.regAt hunit.regAt`. Establish `hone : valAt (y ≫ V.j) (1 : V.X.functionField) = 1`. Use `OfModel.valAt_algebraMap (y ≫ V.j) 1` as an intermediate fact. Rewrite `this` using `[map_one, map_one]`. Then use the resulting hypothesis.

Establish `hev` using `OfModel.eval_pull e.O.subtype (𝟙 V.X) (y ≫ V.j) yt (hc.trans (Category.comp_id _).symm) (U := W₀ ⊓ U) (W := W₀ ⊓ U) le_rfl ht hW g`. Establish `hid : ((𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl).hom g = g`. Establish `: (𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl = 𝟙 _` using `(Category.id_comp _).trans (V.X.presheaf.map_id _)`. Rewrite using `[this]`. Both sides reduce to the same expression.

Rewrite `hev` using `[hid]`. Rewrite `hmul` using `[mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev]`. Use `hn ((isUnit_eval_iff yt hW g).1 (isUnit_of_one_le e _ ?_))` and prove the remaining obligations. Establish `h₁` using `congrArg e.w hmul`. Rewrite `h₁` using `[map_one, map_mul]`.

Conclude with `h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hle)`.
-/
theorem regAt_of_integral_values : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (U : V.X.Opens) (f : V.X.functionField), (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (z ≫ V.j) f) ≤ 1) → ∀ x ∈ U, RegAt x f := by
  intro F _ _ Y V U f hf x hx
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  have : IsLocallyNoetherian V.X := LocallyOfFiniteType.isLocallyNoetherian V.p
  by_contra hreg
  obtain ⟨z, hz, hzero⟩ := GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal V.X V.normal x f hreg
  have hf0 : f ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have hzU : z ∈ U := hz.mem_open U.isOpen hx
  obtain ⟨W₀, hzW, g₀, hg₀⟩ := hzero.regAt.exists_fnOf
  have hzW' : z ∈ W₀ ⊓ U := ⟨hzW, hzU⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(V.X, W₀ ⊓ U), ∀ h, fnOf _ h g = f⁻¹ :=
    ⟨resG V.X inf_le_left g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩
  have hg0 : g ≠ 0 := fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzW'), h, map_zero])
  have hzg : z ∉ V.X.basicOpen g := fun h =>
    (zeroAt_iff.1 hzero).2 (hg (gen_mem hzW') ▸ (unitAt_fnOf_iff hzW' _ g).2 h)
  obtain ⟨v, e, y, yt, hy, hc, hW, hn, hu⟩ := exists_horizPt V _ z g hzW' hg0 hzg
  have hle := hf v e y yt hy hc fun p hp => (hW hp).2
  have hu' : below (y ≫ V.j) ∈ V.X.basicOpen g := hu
  have hb : below (y ≫ V.j) ∈ W₀ ⊓ U := V.X.basicOpen_le g hu'
  have ht : ⊤ ≤ (y ≫ V.j) ⁻¹ᵁ (W₀ ⊓ U) := fun p _ => by
    change (y ≫ V.j) p ∈ W₀ ⊓ U
    rw [← hc]
    exact hW (x := spMap e.O.subtype p) trivial
  have hunit : UnitAt (below (y ≫ V.j)) f⁻¹ := hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'
  have hfu : UnitAt (below (y ≫ V.j)) f := inv_inv f ▸ hunit.inv
  have hmul := OfModel.valAt_mul (y ≫ V.j) hfu.regAt hunit.regAt
  have hone : valAt (y ≫ V.j) (1 : V.X.functionField) = 1 := by
    have := OfModel.valAt_algebraMap (y ≫ V.j) 1
    rwa [map_one, map_one] at this
  have hev := OfModel.eval_pull e.O.subtype (𝟙 V.X) (y ≫ V.j) yt (hc.trans (Category.comp_id _).symm)
    (U := W₀ ⊓ U) (W := W₀ ⊓ U) le_rfl ht hW g
  have hid : ((𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl).hom g = g := by
    have : (𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl = 𝟙 _ :=
      (Category.id_comp _).trans (V.X.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev] at hmul
  refine hn ((isUnit_eval_iff yt hW g).1 (isUnit_of_one_le e _ ?_))
  have h₁ := congrArg e.w hmul
  rw [map_one, map_mul] at h₁
  exact h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hle)

end GlobalTheory.Mean4O.Cover.RegCrit
