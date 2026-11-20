import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.SpecialisationPts

open GlobalTheory.AffinePoints GlobalTheory.CxPts

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal B`. Set `_` to `Ideal.Quotient.field m`. Establish `: Module.Finite ℂ (B ⧸ m)` using `finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)`. Conclude with `⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩`.
-/
theorem nonempty_point (B : Type) [CommRing B] [Nontrivial B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ := Ideal.Quotient.field m
  have : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

/- English proof (translation)
Use `⟨fun h f hf => h.mem_open (X.basicOpen f).2 hf, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[specializes_iff_forall_open]`. Introduce `s hs hzs`. Take `⟨g, hg, hzg⟩` from `hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨z, hzs⟩ hz`. Conclude with `hg (h g hzg)`.
-/
theorem specializes_iff_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x z : X}
    (hz : z ∈ U) : x ⤳ z ↔ ∀ f : Γ(X, U), z ∈ X.basicOpen f → x ∈ X.basicOpen f := by
  refine ⟨fun h f hf => h.mem_open (X.basicOpen f).2 hf, fun h => ?_⟩
  rw [specializes_iff_forall_open]
  intro s hs hzs
  obtain ⟨g, hg, hzg⟩ := hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨z, hzs⟩ hz
  exact hg (h g hzg)

/- English proof (translation)
Establish `h : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x ∈ X.basicOpen f`. Express the relevant statement in the definitionally equal form `hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ _`. Rewrite using `[hU.fromSpec_primeIdealOf]`. Rewrite using `[← h, hU.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression.
-/
theorem mem_basicOpen_iff_notMem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (f : Γ(X, U)) :
    x ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x ∈ X.basicOpen f := by
    change hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ _
    rw [hU.fromSpec_primeIdealOf]
  rw [← h, hU.fromSpec_preimage_basicOpen]
  rfl

/- English proof (translation)
Rewrite using `[specializes_iff_basicOpen hU (mem_ptsIn.1 hy)]`. Use `forall_congr' fun f => ?_` and prove the remaining obligations. Rewrite using `[mem_basicOpen_iff_notMem hU hx, ← mem_ptsIn, mem_ptsIn_basicOpen hy]`. Conclude with `not_imp_not`.
-/
theorem specializes_iff_ev {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) {y : GlobalTheory.CxPts p (RingHom.id ℂ)} (hy : y ∈ ptsIn p (RingHom.id ℂ) U) :
    x ⤳ y.1 (IsLocalRing.closedPoint ℂ) ↔
      ∀ f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal, ev p (RingHom.id ℂ) U f y = 0 := by
  rw [specializes_iff_basicOpen hU (mem_ptsIn.1 hy)]
  refine forall_congr' fun f => ?_
  rw [mem_basicOpen_iff_notMem hU hx, ← mem_ptsIn, mem_ptsIn_basicOpen hy]
  exact not_imp_not

/- English proof (translation)
Introduce `X p hp U hU x hx`. Set `: Algebra ℂ Γ(X, U)` to `(algX p U).toAlgebra`. Establish `hft : (algX p U).FiniteType` using `(HasRingHomProperty.appLE @LocallyOfFiniteType p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)`. Establish `: Algebra.FiniteType ℂ Γ(X, U)` using `hft`. Set `P : Ideal Γ(X, U)` to `(hU.primeIdealOf ⟨x, hx⟩).asIdeal`.

Establish `: P.IsPrime` using `(hU.primeIdealOf ⟨x, hx⟩).isPrime`. Set `Φ (φ : (Γ(X, U) ⧸ P) →ₐ[ℂ] ℂ) : GlobalTheory.CxPts p (RingHom.id ℂ)` to `ofHom hU (φ.comp (Ideal.Quotient.mkₐ ℂ P)).toRingHom fun a => (φ.comp (Ideal.Quotient.mkₐ ℂ P)).commutes a`. Establish `hmem (φ) : Φ φ ∈ ptsIn p (RingHom.id ℂ) U` using `ofHom_mem _ _ _`. Establish `hev (φ) (f : Γ(X, U)) : ev p (RingHom.id ℂ) U f (Φ φ) = φ (Ideal.Quotient.mk P f)` using `ev_ofHom _ _ _ f`. Establish `hc : Continuous Φ`.

Use `continuous_iff_continuousAt.2 fun φ => tendsto_subtype_rng.2 (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hmem φ) (Filter.Eventually.of_forall hmem) fun f => ?_)` and prove the remaining obligations. Establish `h` using `(continuous_eval (R := ℂ) (C := ℂ) (Ideal.Quotient.mk P f)).tendsto φ`. Simplify using `only [← hev] at h`. Conclude with `h`. Establish `hr : Set.range Φ = {y : GlobalTheory.CxPts p (RingHom.id ℂ) | y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)}`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ, rfl⟩`. Use `⟨mem_ptsIn.1 (hmem φ), (specializes_iff_ev hU hx (hmem φ)).2 fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[hev, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]`.

Introduce and unpack `⟨hy, hxy⟩`. Establish `hy'` using `mem_ptsIn.2 hy`. Set `ψ : Γ(X, U) →ₐ[ℂ] ℂ` to `{ evHom hy' with commutes' := fun a => (ev_eq hy' _).symm.trans (ev_algX hy' a) }`. Use `⟨Ideal.Quotient.liftₐ P ψ fun f hf => (ev_eq hy' f).symm.trans ((specializes_iff_ev hU hx hy').1 hxy f hf), ?_⟩` and prove the remaining obligations. Use `Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hmem _) hy' fun f => ?_)` and prove the remaining obligations.

Conclude with `(hev _ f).trans (ev_eq hy' f).symm`. Prove the components needed by the constructor for the conclusion. Take `⟨φ⟩` from `nonempty_point (Γ(X, U) ⧸ P)`. Establish `h` using `Set.mem_range_self (f := Φ) φ`. Rewrite `h` using `[hr]`.

Conclude with `⟨_, h⟩`. Use `GlobalTheory.RootConst.preconnectedSpace_algHom (Γ(X, U) ⧸ P)` as an intermediate fact. Rewrite using `[← hr]`. Conclude with `isPreconnected_range hc`.
-/
theorem nonempty_and_isPreconnected : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), LocallyOfFiniteType p →
    ∀ (U : X.Opens), IsAffineOpen U → ∀ x ∈ U,
    (∃ y : GlobalTheory.CxPts p (RingHom.id ℂ), y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧
      x ⤳ y.1 (IsLocalRing.closedPoint ℂ)) ∧
    _root_.IsPreconnected {y : GlobalTheory.CxPts p (RingHom.id ℂ) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)} := by
  intro X p hp U hU x hx
  let : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType ℂ Γ(X, U) := hft
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have : P.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let Φ (φ : (Γ(X, U) ⧸ P) →ₐ[ℂ] ℂ) : GlobalTheory.CxPts p (RingHom.id ℂ) :=
    ofHom hU (φ.comp (Ideal.Quotient.mkₐ ℂ P)).toRingHom
      fun a => (φ.comp (Ideal.Quotient.mkₐ ℂ P)).commutes a
  have hmem (φ) : Φ φ ∈ ptsIn p (RingHom.id ℂ) U := ofHom_mem _ _ _
  have hev (φ) (f : Γ(X, U)) : ev p (RingHom.id ℂ) U f (Φ φ) = φ (Ideal.Quotient.mk P f) :=
    ev_ofHom _ _ _ f
  have hc : Continuous Φ := by
    refine continuous_iff_continuousAt.2 fun φ => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hmem φ) (Filter.Eventually.of_forall hmem)
        fun f => ?_)
    have h := (continuous_eval (R := ℂ) (C := ℂ) (Ideal.Quotient.mk P f)).tendsto φ
    simp only [← hev] at h
    exact h
  have hr : Set.range Φ = {y : GlobalTheory.CxPts p (RingHom.id ℂ) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)} := by
    ext y
    constructor
    · rintro ⟨φ, rfl⟩
      refine ⟨mem_ptsIn.1 (hmem φ), (specializes_iff_ev hU hx (hmem φ)).2 fun f hf => ?_⟩
      rw [hev, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    · rintro ⟨hy, hxy⟩
      have hy' := mem_ptsIn.2 hy
      let ψ : Γ(X, U) →ₐ[ℂ] ℂ :=
        { evHom hy' with commutes' := fun a => (ev_eq hy' _).symm.trans (ev_algX hy' a) }
      refine ⟨Ideal.Quotient.liftₐ P ψ fun f hf =>
        (ev_eq hy' f).symm.trans ((specializes_iff_ev hU hx hy').1 hxy f hf), ?_⟩
      refine Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hmem _) hy' fun f => ?_)
      exact (hev _ f).trans (ev_eq hy' f).symm
  constructor
  · obtain ⟨φ⟩ := nonempty_point (Γ(X, U) ⧸ P)
    have h := Set.mem_range_self (f := Φ) φ
    rw [hr] at h
    exact ⟨_, h⟩
  · have := GlobalTheory.RootConst.preconnectedSpace_algHom (Γ(X, U) ⧸ P)
    rw [← hr]
    exact isPreconnected_range hc

end GlobalTheory.SpecialisationPts
