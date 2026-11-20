import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximalStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.HorizPt

def strHom {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (U : X.Opens) : CommRingCat.of R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appLE ⊤ U le_top

/- English proof (translation)
Rewrite using `[← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem fromSpec_str {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map (strHom q U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/- English proof (translation)
Establish `h₁ : (q.appLE ⊤ U le_top).hom.Flat` using `HasRingHomProperty.appLE @Flat q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top`. Establish `h₂ : (strHom q U).hom.Flat` using `RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv)) h₁`. Establish `h₃ : (algebraMap ℤ Γ(X, U)).Flat`. Rewrite using `[Subsingleton.elim (algebraMap ℤ Γ(X, U)) (strHom q U).hom]` and apply the resulting hypothesis. Use `RingHom.flat_algebraMap_iff.1 h₃` as an intermediate fact.

Conclude with `charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ Γ(X, U))`.
-/
theorem charZero {X : Scheme.{0}} (q : X ⟶ Sp ℤ) [Flat q] {U : X.Opens} (hU : IsAffineOpen U)
    [Nontrivial Γ(X, U)] : CharZero Γ(X, U) := by
  have h₁ : (q.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : (strHom q U).hom.Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv)) h₁
  have h₃ : (algebraMap ℤ Γ(X, U)).Flat := by
    rwa [Subsingleton.elim (algebraMap ℤ Γ(X, U)) (strHom q U).hom]
  have := RingHom.flat_algebraMap_iff.1 h₃
  exact charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ Γ(X, U))

/- English proof (translation)
Introduce `F _ _ Y N W z g hz hg hzg`. Use `N.ar.isIntegral` as an intermediate fact. Use `N.ar.flat` as an intermediate fact. Establish `: IsProper N.p`. Take `⟨n, c, hc, h⟩` from `N.ar.isProjOver`.

Use `isProper_str (𝓞 F) n` as an intermediate fact. Rewrite using `[← h]`. Use `infer_instance`. Take `⟨U, hU, hzU, hUW⟩` from `exists_isAffineOpen_mem_and_subset hz`. Establish `hle : U ≤ W` using `hUW`.

Establish `: Nonempty U` using `⟨⟨z, hzU⟩⟩`. Establish `: CharZero Γ(N.X, U)` using `charZero (N.p ≫ spMap (Int.castRingHom (𝓞 F))) hU`. Set `_ : Algebra (𝓞 F) Γ(N.X, U)` to `(strHom N.p U).hom.toAlgebra`. Establish `: Algebra.FiniteType (𝓞 F) Γ(N.X, U)` using `RingHom.FiniteType.comp (N.p.finiteType_appLE (isAffineOpen_top _) hU le_top) (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)`. Use `set g' : Γ(N.X, U) := N.X.presheaf.map (homOfLE hle).op g with hg'`.

Establish `hg0 : g' ≠ 0` using `fun h => hg (map_injective_of_isIntegral N.X (homOfLE hle) (by rw [← hg', h, map_zero]))`. Establish `hb : ∀ x : PrimeSpectrum Γ(N.X, U), hU.fromSpec x ∈ N.X.basicOpen g ↔ g' ∉ x.asIdeal`. Introduce `x`. Establish `h₁ : hU.fromSpec x ∈ U`. Use `hU.range_fromSpec` as an intermediate fact.

Conclude with `(Set.ext_iff.1 this _).1 ⟨x, rfl⟩`. Establish `h₂ : hU.fromSpec x ∈ N.X.basicOpen g' ↔ g' ∉ x.asIdeal`. Express the relevant statement in the definitionally equal form `x ∈ hU.fromSpec ⁻¹ᵁ N.X.basicOpen g' ↔ _`. Rewrite using `[hU.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression.

Rewrite using `[← h₂, hg', Scheme.basicOpen_res]`. Conclude with `⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩`. Establish `hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal`. Assume the negation of the conclusion as `h`. Use `(hb _).2 h` as an intermediate fact.

Rewrite `this` using `[hU.fromSpec_primeIdealOf]`. Conclude with `hzg this`. Take `⟨𝔪, h𝔪, hle'⟩` from `Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top`. Take `⟨v, e, φ, h₁, h₂, h₃⟩` from `GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(N.X, U) 𝔪 h𝔪 g' hg0`. Set `yt : Sp e.O ⟶ N.X` to `Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec`.

Establish `hw : (spMap e.O.subtype ≫ yt) ≫ N.p = spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F)`. Simplify using `only [yt, Category.assoc]`. Rewrite using `[fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `a`.

Conclude with `h₁ a`. Establish `hy` using `N.pb.lift_fst _ _ hw`. Use `⟨v, e, ⟨N.pb.lift _ _ hw, N.pb.lift_snd _ _ hw⟩, yt, hy.symm, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x _`. Conclude with `hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)`.

Introduce `h`. Use `(hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_` and prove the remaining obligations. Use `hle' hp` as an intermediate fact. Rewrite `this` using `[← h₂]`. Conclude with `this`.

Express the relevant statement in the definitionally equal form `(N.pb.lift _ _ hw ≫ N.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _`. Rewrite using `[hy]`. Use `(hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_` and prove the remaining obligations. Establish `h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F)` using `h`. Rewrite `h'` using `[IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]`.

Conclude with `Subtype.ext h'`.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : TrueGeo.Model Y) (W : N.X.Opens) (z : N.X) (g : Γ(N.X, W)), z ∈ W → g ≠ 0 → z ∉ N.X.basicOpen g → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X), spMap e.O.subtype ≫ yt = y.1 ≫ N.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ yt (IsLocalRing.closedPoint e.O) ∉ N.X.basicOpen g ∧ N.j (below y.1) ∈ N.X.basicOpen g := by
  intro F _ _ Y N W z g hz hg hzg
  have := N.ar.isIntegral
  have := N.ar.flat
  have : IsProper N.p := by
    obtain ⟨n, c, hc, h⟩ := N.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(N.X, U) := charZero (N.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(N.X, U) := (strHom N.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(N.X, U) :=
    RingHom.FiniteType.comp (N.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  set g' : Γ(N.X, U) := N.X.presheaf.map (homOfLE hle).op g with hg'
  have hg0 : g' ≠ 0 := fun h => hg (map_injective_of_isIntegral N.X (homOfLE hle) (by rw [← hg', h, map_zero]))
  have hb : ∀ x : PrimeSpectrum Γ(N.X, U), hU.fromSpec x ∈ N.X.basicOpen g ↔ g' ∉ x.asIdeal := by
    intro x
    have h₁ : hU.fromSpec x ∈ U := by
      have := hU.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨x, rfl⟩
    have h₂ : hU.fromSpec x ∈ N.X.basicOpen g' ↔ g' ∉ x.asIdeal := by
      change x ∈ hU.fromSpec ⁻¹ᵁ N.X.basicOpen g' ↔ _
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
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(N.X, U) 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ N.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ N.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := N.pb.lift_fst _ _ hw
  refine ⟨v, e, ⟨N.pb.lift _ _ hw, N.pb.lift_snd _ _ hw⟩, yt, hy.symm, ?_, ?_, ?_⟩
  · intro x _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro h
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (N.pb.lift _ _ hw ≫ N.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
    have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'

end GlobalTheory.TrueGeo.HorizPt
