import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.LocModelTwo

variable {L : Type} [Field L] {cL : ℂ →+* L}

def primeOf (P : Place cL) (Q : Subring L) (hP : P.Contains Q) : Ideal Q :=
  Ideal.comap ((Q.subtype).codRestrict P.ring fun x => hP x x.2) (IsLocalRing.maximalIdeal P.ring)

instance (P : Place cL) (Q : Subring L) (hP : P.Contains Q) : (primeOf P Q hP).IsPrime :=
  Ideal.comap_isPrime _ _

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_primeOf {P : Place cL} {Q : Subring L} {hP : P.Contains Q} {x : Q} :
    x ∈ primeOf P Q hP ↔ ¬ IsUnit (⟨x, hP x x.2⟩ : P.ring) := Iff.rfl

/- English proof (translation)
Establish `hi : (y : L)⁻¹ ∈ P.ring` using `(P.ord_nonneg_iff (inv_ne_zero hy)).1 (by rw [P.ord_inv, h]; rfl)`. Conclude with `isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ hy)⟩`.
-/
theorem isUnit_of_ord_eq_zero (P : Place cL) {y : P.ring} (hy : (y : L) ≠ 0) (h : P.ord y = 0) :
    IsUnit y := by
  have hi : (y : L)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hy)).1 (by rw [P.ord_inv, h]; rfl)
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ hy)⟩

/- English proof (translation)
Simplify using `[Place.ord]`.
-/
theorem ord_zero (P : Place cL) : P.ord 0 = 0 := by simp [Place.ord]

/- English proof (translation)
Rewrite using `[mem_primeOf]`. Prove the components needed by the constructor for the conclusion. Introduce `h hu`. Use `P.ord_eq_zero hu` as an intermediate fact. Simplify using `only at this`.

Use linear arithmetic over natural numbers and integers. Introduce `h`. Establish `h0 : 0 ≤ P.ord x` using `(P.ord_nonneg_iff hx).2 (hP x x.2)`. Use `lt_of_le_of_ne h0 fun e => h ?_` and prove the remaining obligations. Conclude with `isUnit_of_ord_eq_zero P (y := ⟨x, hP x x.2⟩) hx e.symm`.
-/
theorem pos_ord_iff {P : Place cL} {Q : Subring L} (hP : P.Contains Q) {x : Q} (hx : (x : L) ≠ 0) :
    0 < P.ord x ↔ x ∈ primeOf P Q hP := by
  rw [mem_primeOf]
  constructor
  · intro h hu
    have := P.ord_eq_zero hu
    simp only at this
    omega
  · intro h
    have h0 : 0 ≤ P.ord x := (P.ord_nonneg_iff hx).2 (hP x x.2)
    refine lt_of_le_of_ne h0 fun e => h ?_
    exact isUnit_of_ord_eq_zero P (y := ⟨x, hP x x.2⟩) hx e.symm

/- English proof (translation)
Introduce `f hf`. Take `⟨a, ha, b, hb, hb0, hob, e⟩` from `hP.2 f hf`. Establish `hbP : (⟨b, hb⟩ : Q) ∉ primeOf P Q hP.1`. Rewrite using `[mem_primeOf, not_not]`. Conclude with `isUnit_of_ord_eq_zero P (y := ⟨b, hP.1 b hb⟩) hb0 hob`.

Establish `hbP' : (⟨b, hb⟩ : Q) ∉ primeOf P' Q hP'` using `fun h' => hbP (h h')`. Rewrite `hbP'` using `[mem_primeOf, not_not]`. Take `⟨v, hv⟩` from `hbP'.exists_right_inv`. Establish `hv' : b * (v : L) = 1` using `congrArg Subtype.val hv`. Establish `: f = a * v`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `mul_mem (hP' a ha) v.2`.
-/
theorem ring_le {P P' : Place cL} {Q : Subring L} (hP : P.IsPrimeOf Q) (hP' : P'.Contains Q)
    (h : primeOf P' Q hP' ≤ primeOf P Q hP.1) : P.ring ≤ P'.ring := by
  intro f hf
  obtain ⟨a, ha, b, hb, hb0, hob, e⟩ := hP.2 f hf
  have hbP : (⟨b, hb⟩ : Q) ∉ primeOf P Q hP.1 := by
    rw [mem_primeOf, not_not]
    exact isUnit_of_ord_eq_zero P (y := ⟨b, hP.1 b hb⟩) hb0 hob
  have hbP' : (⟨b, hb⟩ : Q) ∉ primeOf P' Q hP' := fun h' => hbP (h h')
  rw [mem_primeOf, not_not] at hbP'
  obtain ⟨v, hv⟩ := hbP'.exists_right_inv
  have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
  have : f = a * v := by
    calc f = f * (b * v) := by rw [hv', mul_one]
      _ = a * v := by rw [← mul_assoc, e]
  rw [this]
  exact mul_mem (hP' a ha) v.2

/- English proof (translation)
Establish `hle : P.ring.toSubring ≤ Q`. Introduce `f hf`. Take `⟨a, ha, b, hb, hb0, hob, e⟩` from `hP.2 f hf`. Establish `hbP : (⟨b, hb⟩ : Q) ∉ primeOf P Q hP.1`. Rewrite using `[mem_primeOf, not_not]`.

Conclude with `isUnit_of_ord_eq_zero P (y := ⟨b, hP.1 b hb⟩) hb0 hob`. Establish `hbQ : IsUnit (⟨b, hb⟩ : Q)`. Assume the negation of the conclusion as `hn`. Conclude with `hbP (h ((IsLocalRing.mem_maximalIdeal _).2 hn))`. Take `⟨v, hv⟩` from `hbQ.exists_right_inv`.

Establish `hv' : b * (v : L) = 1` using `congrArg Subtype.val hv`. Establish `: f = a * v`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `Q.mul_mem ha v.2`.

Establish `hQ : Q = P.ring.toSubring` using `le_antisymm (fun x hx => hP.1 x hx) hle`. Conclude with `(ringKrullDim_eq_of_ringEquiv (RingEquiv.subringCongr hQ)).trans (IsDiscreteValuationRing.ringKrullDim_eq_one P.ring)`.
-/
theorem ringKrullDim_eq_one {P : Place cL} {Q : Subring L} [IsLocalRing Q] (hP : P.IsPrimeOf Q)
    (h : IsLocalRing.maximalIdeal Q ≤ primeOf P Q hP.1) : ringKrullDim Q = 1 := by
  have hle : P.ring.toSubring ≤ Q := by
    intro f hf
    obtain ⟨a, ha, b, hb, hb0, hob, e⟩ := hP.2 f hf
    have hbP : (⟨b, hb⟩ : Q) ∉ primeOf P Q hP.1 := by
      rw [mem_primeOf, not_not]
      exact isUnit_of_ord_eq_zero P (y := ⟨b, hP.1 b hb⟩) hb0 hob
    have hbQ : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact hbP (h ((IsLocalRing.mem_maximalIdeal _).2 hn))
    obtain ⟨v, hv⟩ := hbQ.exists_right_inv
    have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
    have : f = a * v := by
      calc f = f * (b * v) := by rw [hv', mul_one]
        _ = a * v := by rw [← mul_assoc, e]
    rw [this]
    exact Q.mul_mem ha v.2
  have hQ : Q = P.ring.toSubring := le_antisymm (fun x hx => hP.1 x hx) hle
  exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.subringCongr hQ)).trans
    (IsDiscreteValuationRing.ringKrullDim_eq_one P.ring)

/- English proof (translation)
Use `le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem p).2 ht)` and prove the remaining obligations. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian p) (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hym : y ∈ IsLocalRing.maximalIdeal R` using `IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hy`. Rewrite `hym` using `[← hm, Ideal.mem_span_pair]`.

Take `⟨c, d, e⟩` from `hym`. Establish `hdu : d * u ∈ p`. Establish `: d * u = y - c * t` using `by rw [← e]; ring`. Rewrite using `[this]`. Conclude with `p.sub_mem hy (p.mul_mem_left c ht)`.

Establish `hd : d ∈ p` using `((Ideal.IsPrime.mem_or_mem ‹_› hdu).resolve_right hu)`. Rewrite using `[← e]`. Use `Submodule.add_mem_sup (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self t)) ?_` and prove the remaining obligations. Establish `huM : u ∈ IsLocalRing.maximalIdeal R` using `hm ▸ Ideal.subset_span (by simp)`. Use `Submodule.smul_mem_smul huM hd` as an intermediate fact.

Rewrite using `[mul_comm]`. Conclude with `this`.
-/
theorem eq_span_of_mem_of_not_mem {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {t u : R} (hm : Ideal.span {t, u} = IsLocalRing.maximalIdeal R) (p : Ideal R) [p.IsPrime]
    (ht : t ∈ p) (hu : u ∉ p) : p = Ideal.span {t} := by
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem p).2 ht)
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal R)
    (IsNoetherian.noetherian p) (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
  intro y hy
  have hym : y ∈ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hy
  rw [← hm, Ideal.mem_span_pair] at hym
  obtain ⟨c, d, e⟩ := hym
  have hdu : d * u ∈ p := by
    have : d * u = y - c * t := by rw [← e]; ring
    rw [this]
    exact p.sub_mem hy (p.mul_mem_left c ht)
  have hd : d ∈ p := ((Ideal.IsPrime.mem_or_mem ‹_› hdu).resolve_right hu)
  rw [← e]
  refine Submodule.add_mem_sup (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self t)) ?_
  have huM : u ∈ IsLocalRing.maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have := Submodule.smul_mem_smul huM hd
  rw [mul_comm]
  exact this

end GlobalTheory.FieldPair.LocModelTwo

namespace GlobalTheory.FieldPair.LocModelTwo

/- English proof (translation)
Introduce `L _ cL Q hQ t u hm hd`. Use `letI := hQ.isLocalRing`. Use `haveI : IsNoetherianRing Q := by`. Use `letI := (cL.codRestrict Q hQ.const_mem).toAlgebra`. Use `haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType`.

Conclude with `Algebra.EssFiniteType.isNoetherianRing ℂ Q`. Establish `hA : ∀ P : Place cL, ∀ hP : P.IsPrimeOf Q, ¬ (t ∈ primeOf P Q hP.1 ∧ u ∈ primeOf P Q hP.1)`. Introduce and unpack `P hP ⟨ht, hu⟩`. Establish `h1` using `ringKrullDim_eq_one hP (by`. Rewrite using `[← hm]`.

Conclude with `Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨ht, Set.singleton_subset_iff.2 hu⟩))`. Rewrite `h1` using `[hd]`. Conclude with `absurd h1 (by decide)`. Establish `hB : ∀ P : Place cL, ∀ hP : P.IsPrimeOf Q, 0 < P.ord (t : L) → primeOf P Q hP.1 = Ideal.span {t}`. Introduce `P hP hpos`.

Establish `ht0 : (t : L) ≠ 0` using `fun e => by rw [e, ord_zero] at hpos; exact lt_irrefl _ hpos`. Establish `ht : t ∈ primeOf P Q hP.1` using `(pos_ord_iff hP.1 ht0).1 hpos`. Conclude with `eq_span_of_mem_of_not_mem hm _ ht fun hu => hA P hP ⟨ht, hu⟩`. Use `⟨fun P P' hP hP' hPt hP't => ?_, fun P hP => ?_⟩` and prove the remaining obligations. Establish `e` using `(hB P hP hPt).trans (hB P' hP' hP't).symm`.

Conclude with `le_antisymm (ring_le hP hP'.1 e.ge) (ring_le hP' hP.1 e.le)`. Assume the negation of the conclusion as `h push_neg at h`. Establish `hpos : ∀ x : Q, P.ord (x : L) ≠ 0 → x ∈ primeOf P Q hP.1`. Introduce `x hx`. Establish `hx0 : (x : L) ≠ 0` using `fun e => hx (by rw [e, ord_zero])`.

Conclude with `(pos_ord_iff hP.1 hx0).1 (lt_of_le_of_ne ((P.ord_nonneg_iff hx0).2 (hP.1 x x.2)) (Ne.symm hx))`. Conclude with `hA P hP ⟨hpos t h.1, hpos u h.2⟩`.
-/
theorem ring_eq_and_ord_eq_zero : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  (∀ P P' : Place cL, P.IsPrimeOf Q → P'.IsPrimeOf Q → 0 < P.ord (t : L) → 0 < P'.ord (t : L) →
    P.ring = P'.ring) ∧
  (∀ P : Place cL, P.IsPrimeOf Q → P.ord (t : L) = 0 ∨ P.ord (u : L) = 0) := by
  intro L _ cL Q hQ t u hm hd
  letI := hQ.isLocalRing
  haveI : IsNoetherianRing Q := by
    letI := (cL.codRestrict Q hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing ℂ Q
  have hA : ∀ P : Place cL, ∀ hP : P.IsPrimeOf Q,
      ¬ (t ∈ primeOf P Q hP.1 ∧ u ∈ primeOf P Q hP.1) := by
    rintro P hP ⟨ht, hu⟩
    have h1 := ringKrullDim_eq_one hP (by
      rw [← hm]
      exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨ht, Set.singleton_subset_iff.2 hu⟩))
    rw [hd] at h1
    exact absurd h1 (by decide)
  have hB : ∀ P : Place cL, ∀ hP : P.IsPrimeOf Q, 0 < P.ord (t : L) →
      primeOf P Q hP.1 = Ideal.span {t} := by
    intro P hP hpos
    have ht0 : (t : L) ≠ 0 := fun e => by rw [e, ord_zero] at hpos; exact lt_irrefl _ hpos
    have ht : t ∈ primeOf P Q hP.1 := (pos_ord_iff hP.1 ht0).1 hpos
    exact eq_span_of_mem_of_not_mem hm _ ht fun hu => hA P hP ⟨ht, hu⟩
  refine ⟨fun P P' hP hP' hPt hP't => ?_, fun P hP => ?_⟩
  · have e := (hB P hP hPt).trans (hB P' hP' hP't).symm
    exact le_antisymm (ring_le hP hP'.1 e.ge) (ring_le hP' hP.1 e.le)
  · by_contra h
    push_neg at h
    have hpos : ∀ x : Q, P.ord (x : L) ≠ 0 → x ∈ primeOf P Q hP.1 := by
      intro x hx
      have hx0 : (x : L) ≠ 0 := fun e => hx (by rw [e, ord_zero])
      exact (pos_ord_iff hP.1 hx0).1
        (lt_of_le_of_ne ((P.ord_nonneg_iff hx0).2 (hP.1 x x.2)) (Ne.symm hx))
    exact hA P hP ⟨hpos t h.1, hpos u h.2⟩

end GlobalTheory.FieldPair.LocModelTwo
