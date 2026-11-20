import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Discrepancy

namespace GlobalTheory.FieldPair

section SlopeTestRemainingChoices

variable {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U)

include hU in

/- English proof (translation)
Use `letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)`. Use `haveI := hU.isLocalization_stalk ⟨y, hy⟩`. Conclude with `⟨_, IsLocalization.map_units (X.presheaf.stalk y) (⟨s, hs⟩ : (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl), algebraMap_germ hy s⟩`.
-/
theorem unitAt_fnOf_of_not_mem {s : Γ(X, U)} (hs : s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    UnitAt y (fnOf U (gen_mem hy) s) := by
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  exact ⟨_, IsLocalization.map_units (X.presheaf.stalk y)
    (⟨s, hs⟩ : (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl), algebraMap_germ hy s⟩

include hU in

/- English proof (translation)
Use `letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)`. Use `haveI := hU.isLocalization_stalk ⟨y, hy⟩`. Take `⟨a, rfl⟩` from `hf`. Take `⟨⟨c, s⟩, e⟩` from `IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl a`. Use `⟨c, s, s.2, ?_⟩` and prove the remaining obligations.

Establish `e'` using `congrArg (algebraMap _ X.functionField) e`. Rewrite `e'` using `[map_mul]`. Rewrite using `[← algebraMap_germ hy, ← algebraMap_germ hy]`. Conclude with `e'`.
-/
theorem regAt_exists_fraction {f : X.functionField} (hf : RegAt y f) :
    ∃ c s : Γ(X, U), s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      f * fnOf U (gen_mem hy) s = fnOf U (gen_mem hy) c := by
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl a
  refine ⟨c, s, s.2, ?_⟩
  have e' := congrArg (algebraMap _ X.functionField) e
  rw [map_mul] at e'
  rw [← algebraMap_germ hy, ← algebraMap_germ hy]
  exact e'

end SlopeTestRemainingChoices

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, rfl⟩`. Establish `h : ((v : R) : K) * ((v⁻¹ : Rˣ) : R) = 1`. Rewrite using `[← R.coe_mul, Units.mul_inv]`. Both sides reduce to the same expression.

Conclude with `⟨left_ne_zero_of_mul_eq_one h, (inv_eq_of_mul_eq_one_right h) ▸ (v⁻¹ : Rˣ).1.2⟩`. Introduce and unpack `⟨h0, hi⟩`. Conclude with `isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩`.
-/
theorem isUnit_iff_inv_mem {K : Type} [Field K] {R : ValuationSubring K} (u : R) :
    IsUnit u ↔ (u : K) ≠ 0 ∧ (u : K)⁻¹ ∈ R := by
  constructor
  · rintro ⟨v, rfl⟩
    have h : ((v : R) : K) * ((v⁻¹ : Rˣ) : R) = 1 := by
      rw [← R.coe_mul, Units.mul_inv]; rfl
    exact ⟨left_ne_zero_of_mul_eq_one h, (inv_eq_of_mul_eq_one_right h) ▸ (v⁻¹ : Rˣ).1.2⟩
  · rintro ⟨h0, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

/- English proof (translation)
Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial`. Establish `ord0 : ∀ {b : X.functionField}, b ≠ 0 → b ∈ E.ring → b⁻¹ ∈ E.ring → (placeEquiv p E).ord b = 0` using `fun {b} h0 h1 h2 => by`. Establish `a1` using `((placeEquiv p E).ord_nonneg_iff h0).2 h1`. Establish `a2` using `((placeEquiv p E).ord_nonneg_iff (inv_ne_zero h0)).2 h2`. Rewrite `a2` using `[Place.ord_inv]`.

Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hC, hP⟩`. Establish `hT : E.Through x` using `(contains_placeEquiv E x).1 hC`. Set `φ : Γ(X, U) →+* E.ring` to `(fnOf U (gen_mem hx)).codRestrict E.ring fun a => hT _ (regAt_fnOf hx _ a)`.

Set `P : PrimeSpectrum Γ(X, U)` to `⟨(IsLocalRing.maximalIdeal E.ring).comap φ, inferInstance⟩`. Establish `memP (s : Γ(X, U)) : s ∉ P.asIdeal ↔ (fnOf U (gen_mem hx) s ≠ 0 ∧ (fnOf U (gen_mem hx) s)⁻¹ ∈ E.ring)`. Express the relevant statement in the definitionally equal form `φ s ∉ IsLocalRing.maximalIdeal E.ring ↔ _`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`. Conclude with `isUnit_iff_inv_mem (φ s)`.

Establish `hPQ : P ≤ hU.primeIdealOf ⟨x, hx⟩` using `fun s hs => by_contra fun hs' =>`. Establish `h` using `unitAt_fnOf_of_not_mem hU hx hs'`. Use the proof step `(memP s).2 ⟨h.ne_zero, hT _ h.inv.regAt⟩ hs`. Establish `hz : hU.fromSpec P ∈ U`. Establish `: hU.fromSpec P ∈ Set.range hU.fromSpec` using `⟨P, rfl⟩`.

Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Set `z : U` to `⟨hU.fromSpec P, hz⟩`. Establish `hP' : hU.primeIdealOf z = P` using `hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)`. Establish `hzx : (z : X) ⤳ x`. Establish `h` using `((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hPQ).map hU.fromSpec.continuous`.

Rewrite `h` using `[hU.fromSpec_primeIdealOf ⟨x, hx⟩]`. Then use the resulting hypothesis. Use `clear_value z`. Use `⟨z, hzx, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, hb0, hord, e⟩` from `hP f hf`. Take `⟨b', t, ht, e2⟩` from `regAt_exists_fraction hU hx (mem_locRing.1 hb)`.

Establish `hut` using `unitAt_fnOf_of_not_mem hU hx ht`. Establish `htP : t ∉ P.asIdeal` using `(memP t).2 ⟨hut.ne_zero, hT _ hut.inv.regAt⟩`. Establish `hb'0 : fnOf U (gen_mem hx) b' ≠ 0` using `e2 ▸ mul_ne_zero hb0 hut.ne_zero`. Establish `ht0 : (placeEquiv p E).ord (fnOf U (gen_mem hx) t) = 0` using `ord0 hut.ne_zero (hT _ hut.regAt) (hT _ hut.inv.regAt)`. Establish `hob' : (placeEquiv p E).ord (fnOf U (gen_mem hx) b') = 0`.

Rewrite using `[← e2, (placeEquiv p E).ord_mul hb0 hut.ne_zero, hord, ht0, add_zero]`. Establish `hb'i : (fnOf U (gen_mem hx) b')⁻¹ ∈ E.ring` using `((placeEquiv p E).ord_nonneg_iff (inv_ne_zero hb'0)).1 (by rw [Place.ord_inv, hob', neg_zero])`. Establish `hb'P : b' ∉ P.asIdeal` using `(memP b').2 ⟨hb'0, hb'i⟩`. Establish `hub'` using `unitAt_fnOf_of_not_mem hU z.2 (s := b') (by rw [hP']; exact hb'P)`. Establish `hut'` using `unitAt_fnOf_of_not_mem hU z.2 (s := t) (by rw [hP']; exact htP)`.

Establish `hbz : UnitAt (z : X) b`. Establish `eb : b = fnOf U (gen_mem hx) b' * (fnOf U (gen_mem hx) t)⁻¹`. Rewrite using `[← e2, mul_inv_cancel_right₀ hut.ne_zero]`. Rewrite using `[eb]`. Conclude with `hub'.mul hut'.inv`.

Establish `haz : RegAt (z : X) a` using `regAt_of_specializes hzx (mem_locRing.1 ha)`. Establish `ef : f = a * b⁻¹` using `by rw [← e, mul_inv_cancel_right₀ hb0]`. Rewrite using `[ef]`. Conclude with `haz.mul hbz.inv.regAt`. Take `⟨c, s, hs, e⟩` from `regAt_exists_fraction hU z.2 hf`.

Establish `hs' : s ∉ P.asIdeal` using `by rw [← hP']; exact hs`. Take `⟨hs0, hsi⟩` from `(memP s).1 hs'`. Establish `ef : f = fnOf U (gen_mem hx) c * (fnOf U (gen_mem hx) s)⁻¹`. Rewrite using `[← e, mul_inv_cancel_right₀ hs0]`. Rewrite using `[ef]`.

Conclude with `mul_mem (hT _ (regAt_fnOf hx _ c)) hsi`. Introduce and unpack `⟨z, hzx, hz⟩`. Use `⟨(contains_placeEquiv E x).2 (hz.through hzx), fun f hf => ?_⟩` and prove the remaining obligations. Establish `hzU : z ∈ U` using `hzx.mem_open U.isOpen hx`. Take `⟨c, s, hs, e⟩` from `regAt_exists_fraction hU hzU ((hz f).1 hf)`.

Establish `hu` using `unitAt_fnOf_of_not_mem hU hzU hs`. Conclude with `⟨_, mem_locRing.2 (regAt_fnOf hx _ c), _, mem_locRing.2 (regAt_fnOf hx _ s), hu.ne_zero, ord0 hu.ne_zero ((hz _).2 hu.regAt) ((hz _).2 hu.inv.regAt), e⟩`.
-/
theorem isPrimeOf_placeEquiv {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (x : X) :
    (placeEquiv p E).IsPrimeOf (locRing x) ↔ ∃ z, z ⤳ x ∧ E.IsAt z := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have ord0 : ∀ {b : X.functionField}, b ≠ 0 → b ∈ E.ring → b⁻¹ ∈ E.ring →
      (placeEquiv p E).ord b = 0 := fun {b} h0 h1 h2 => by
    have a1 := ((placeEquiv p E).ord_nonneg_iff h0).2 h1
    have a2 := ((placeEquiv p E).ord_nonneg_iff (inv_ne_zero h0)).2 h2
    rw [Place.ord_inv] at a2
    omega
  constructor
  · rintro ⟨hC, hP⟩
    have hT : E.Through x := (contains_placeEquiv E x).1 hC
    let φ : Γ(X, U) →+* E.ring :=
      (fnOf U (gen_mem hx)).codRestrict E.ring fun a => hT _ (regAt_fnOf hx _ a)
    let P : PrimeSpectrum Γ(X, U) := ⟨(IsLocalRing.maximalIdeal E.ring).comap φ, inferInstance⟩
    have memP (s : Γ(X, U)) : s ∉ P.asIdeal ↔
        (fnOf U (gen_mem hx) s ≠ 0 ∧ (fnOf U (gen_mem hx) s)⁻¹ ∈ E.ring) := by
      change φ s ∉ IsLocalRing.maximalIdeal E.ring ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact isUnit_iff_inv_mem (φ s)
    have hPQ : P ≤ hU.primeIdealOf ⟨x, hx⟩ := fun s hs => by_contra fun hs' =>
      have h := unitAt_fnOf_of_not_mem hU hx hs'
      (memP s).2 ⟨h.ne_zero, hT _ h.inv.regAt⟩ hs
    have hz : hU.fromSpec P ∈ U := by
      have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
      rwa [hU.range_fromSpec] at this
    let z : U := ⟨hU.fromSpec P, hz⟩
    have hP' : hU.primeIdealOf z = P :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
    have hzx : (z : X) ⤳ x := by
      have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hPQ).map
        hU.fromSpec.continuous
      rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
    clear_value z
    refine ⟨z, hzx, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
    · obtain ⟨a, ha, b, hb, hb0, hord, e⟩ := hP f hf
      obtain ⟨b', t, ht, e2⟩ := regAt_exists_fraction hU hx (mem_locRing.1 hb)
      have hut := unitAt_fnOf_of_not_mem hU hx ht
      have htP : t ∉ P.asIdeal := (memP t).2 ⟨hut.ne_zero, hT _ hut.inv.regAt⟩
      have hb'0 : fnOf U (gen_mem hx) b' ≠ 0 := e2 ▸ mul_ne_zero hb0 hut.ne_zero
      have ht0 : (placeEquiv p E).ord (fnOf U (gen_mem hx) t) = 0 :=
        ord0 hut.ne_zero (hT _ hut.regAt) (hT _ hut.inv.regAt)
      have hob' : (placeEquiv p E).ord (fnOf U (gen_mem hx) b') = 0 := by
        rw [← e2, (placeEquiv p E).ord_mul hb0 hut.ne_zero, hord, ht0, add_zero]
      have hb'i : (fnOf U (gen_mem hx) b')⁻¹ ∈ E.ring :=
        ((placeEquiv p E).ord_nonneg_iff (inv_ne_zero hb'0)).1
          (by rw [Place.ord_inv, hob', neg_zero])
      have hb'P : b' ∉ P.asIdeal := (memP b').2 ⟨hb'0, hb'i⟩
      have hub' := unitAt_fnOf_of_not_mem hU z.2 (s := b') (by rw [hP']; exact hb'P)
      have hut' := unitAt_fnOf_of_not_mem hU z.2 (s := t) (by rw [hP']; exact htP)
      have hbz : UnitAt (z : X) b := by
        have eb : b = fnOf U (gen_mem hx) b' * (fnOf U (gen_mem hx) t)⁻¹ := by
          rw [← e2, mul_inv_cancel_right₀ hut.ne_zero]
        rw [eb]
        exact hub'.mul hut'.inv
      have haz : RegAt (z : X) a := regAt_of_specializes hzx (mem_locRing.1 ha)
      have ef : f = a * b⁻¹ := by rw [← e, mul_inv_cancel_right₀ hb0]
      rw [ef]
      exact haz.mul hbz.inv.regAt
    · obtain ⟨c, s, hs, e⟩ := regAt_exists_fraction hU z.2 hf
      have hs' : s ∉ P.asIdeal := by rw [← hP']; exact hs
      obtain ⟨hs0, hsi⟩ := (memP s).1 hs'
      have ef : f = fnOf U (gen_mem hx) c * (fnOf U (gen_mem hx) s)⁻¹ := by
        rw [← e, mul_inv_cancel_right₀ hs0]
      rw [ef]
      exact mul_mem (hT _ (regAt_fnOf hx _ c)) hsi
  · rintro ⟨z, hzx, hz⟩
    refine ⟨(contains_placeEquiv E x).2 (hz.through hzx), fun f hf => ?_⟩
    have hzU : z ∈ U := hzx.mem_open U.isOpen hx
    obtain ⟨c, s, hs, e⟩ := regAt_exists_fraction hU hzU ((hz f).1 hf)
    have hu := unitAt_fnOf_of_not_mem hU hzU hs
    exact ⟨_, mem_locRing.2 (regAt_fnOf hx _ c), _, mem_locRing.2 (regAt_fnOf hx _ s), hu.ne_zero,
      ord0 hu.ne_zero ((hz _).2 hu.regAt) ((hz _).2 hu.inv.regAt), e⟩

end GlobalTheory.FieldPair
