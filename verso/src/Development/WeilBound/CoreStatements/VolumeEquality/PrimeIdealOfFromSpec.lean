import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed

noncomputable section

namespace SheetDecomposition.BBase

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def ev (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hg : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ U (genPt ξ) hg).hom

/- English proof (translation)
The claim follows from `RegAtRing.genMap_germ q U hq hg s`.
-/
theorem genMap_germ (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U) (hg : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq s) = ev ξ U hg s := RegAtRing.genMap_germ q U hq hg s

/- English proof (translation)
Introduce `s s' e`. Use `TopCat.Presheaf.section_ext X.sheaf U s s' fun q hq => ?_` and prove the remaining obligations. Apply `hξ.inj ⟨q, hU q hq⟩` to reduce the goal to its premises. Conclude with `(genMap_germ ⟨q, hU q hq⟩ U hq hg s).trans (e.trans (genMap_germ ⟨q, hU q hq⟩ U hq hg s').symm)`.
-/
theorem ev_injective (hξ : IsCptGen ξ) (U : X.Opens) (hg : genPt ξ ∈ U) (hU : ∀ q ∈ U, genPt ξ ⤳ q) :
    Function.Injective (ev ξ U hg) := by
  intro s s' e
  refine TopCat.Presheaf.section_ext X.sheaf U s s' fun q hq => ?_
  apply hξ.inj ⟨q, hU q hq⟩
  exact (genMap_germ ⟨q, hU q hq⟩ U hq hg s).trans (e.trans (genMap_germ ⟨q, hU q hq⟩ U hq hg s').symm)

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, genMap_germ q U hq hg s⟩`.
-/
theorem ev_mem (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U) (hg : genPt ξ ∈ U) (s : Γ(X, U)) :
    ev ξ U hg s ∈ regAt ξ q := ⟨_, genMap_germ q U hq hg s⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, -, t, ht⟩`. Use `IsUnit.of_mul_eq_one t (hξ.inj q ?_)` and prove the remaining obligations. Rewrite using `[map_mul, ht, map_one, mul_inv_cancel₀ h0]`. Introduce and unpack `⟨u, rfl⟩`.

Conclude with `⟨(u.isUnit.map (genMap ξ q)).ne_zero, ⟨_, rfl⟩, ⟨_, map_units_inv (genMap ξ q) u⟩⟩`.
-/
theorem unitAt_iff (hξ : IsCptGen ξ) (q : Cpt ξ) (g : X.presheaf.stalk q.1) :
    unitAt ξ q (genMap ξ q g) ↔ IsUnit g := by
  constructor
  · rintro ⟨h0, -, t, ht⟩
    refine IsUnit.of_mul_eq_one t (hξ.inj q ?_)
    rw [map_mul, ht, map_one, mul_inv_cancel₀ h0]
  · rintro ⟨u, rfl⟩
    exact ⟨(u.isUnit.map (genMap ξ q)).ne_zero, ⟨_, rfl⟩, ⟨_, map_units_inv (genMap ξ q) u⟩⟩

/- English proof (translation)
Rewrite using `[← genMap_germ q U hq hg, unitAt_iff hξ]`. Set `_` to `TopCat.Presheaf.algebra_section_stalk X.presheaf (U := U) ⟨q.1, hq⟩`. Use `hU.isLocalization_stalk ⟨q.1, hq⟩` as an intermediate fact. Conclude with `IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk q.1) (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal s`.
-/
theorem unitAt_ev_iff (hξ : IsCptGen ξ) {U : X.Opens} (hU : IsAffineOpen U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (hg : genPt ξ ∈ U) (s : Γ(X, U)) :
    unitAt ξ q (ev ξ U hg s) ↔ s ∉ (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal := by
  rw [← genMap_germ q U hq hg, unitAt_iff hξ]
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := U) ⟨q.1, hq⟩
  have := hU.isLocalization_stalk ⟨q.1, hq⟩
  exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk q.1) (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal s

/- English proof (translation)
Take `⟨g, rfl⟩` from `ha`. Set `_` to `TopCat.Presheaf.algebra_section_stalk X.presheaf (U := U) ⟨q.1, hq⟩`. Use `hU.isLocalization_stalk ⟨q.1, hq⟩` as an intermediate fact. Take `⟨⟨r, s⟩, hrs⟩` from `IsLocalization.surj (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl (S := X.presheaf.stalk q.1) g`. Use `⟨r, s.1, s.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[← genMap_germ q U hq hg, ← genMap_germ q U hq hg, ← map_mul, mul_comm]`. Conclude with `congrArg _ hrs`.
-/
theorem exists_frac {U : X.Opens} (hU : IsAffineOpen U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (hg : genPt ξ ∈ U) {a : Ω} (ha : a ∈ regAt ξ q) :
    ∃ s t : Γ(X, U), t ∉ (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal ∧ ev ξ U hg t * a = ev ξ U hg s := by
  obtain ⟨g, rfl⟩ := ha
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := U) ⟨q.1, hq⟩
  have := hU.isLocalization_stalk ⟨q.1, hq⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk q.1) g
  refine ⟨r, s.1, s.2, ?_⟩
  rw [← genMap_germ q U hq hg, ← genMap_germ q U hq hg, ← map_mul, mul_comm]
  exact congrArg _ hrs

/- English proof (translation)
Apply `hU.fromSpec.isOpenEmbedding.injective` to reduce the goal to its premises. Conclude with `hU.fromSpec_primeIdealOf _`.
-/
theorem primeIdealOf_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U))
    (hy : hU.fromSpec y ∈ U) : hU.primeIdealOf ⟨hU.fromSpec y, hy⟩ = y := by
  apply hU.fromSpec.isOpenEmbedding.injective
  exact hU.fromSpec_primeIdealOf _

/- English proof (translation)
Establish `: hU.fromSpec y ∈ Set.range hU.fromSpec` using `⟨_, rfl⟩`. Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis.
-/
theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) : hU.fromSpec y ∈ U := by
  have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
  rwa [hU.range_fromSpec] at this

/- English proof (translation)
Set `I : Ideal Γ(X, U)` to `{ carrier := {t | ev ξ U hg t * a ∈ (ev ξ U hg).range} add_mem' := fun {t t'} ht ht' => by show ev ξ U hg (t + t') * a ∈ (ev ξ U hg).range`. Rewrite using `[map_add, add_mul]`. Conclude with `add_mem ht ht'`. Use the proof step `zero_mem' := by show ev ξ U hg 0 * a ∈ (ev ξ U hg).range`. Rewrite using `[map_zero, zero_mul]`.

Conclude with `zero_mem _`. Use the proof step `smul_mem' := fun c t ht => by show ev ξ U hg (c * t) * a ∈ (ev ξ U hg).range`. Rewrite using `[map_mul, mul_assoc]`. Conclude with `mul_mem ⟨c, rfl⟩ ht }`. Distinguish the cases in `hI : I = ⊤`.

Establish `: (1 : Γ(X, U)) ∈ I` using `hI ▸ Submodule.mem_top`. Establish `h1 : ev ξ U hg 1 * a ∈ (ev ξ U hg).range` using `this`. Rewrite `h1` using `[map_one, one_mul]`. Then use the resulting hypothesis. Take `⟨m, hm, hIm⟩` from `Ideal.exists_le_maximal I hI`. Set `y : PrimeSpectrum Γ(X, U)` to `⟨m, hm.isPrime⟩`.

Establish `hy` using `fromSpec_mem hU y`. Take `⟨s, t, ht, e⟩` from `exists_frac hU ⟨_, hs _ hy⟩ hy hg (ha _ hy)`. Rewrite `ht` using `[primeIdealOf_fromSpec hU y hy]`. Conclude with `absurd (hIm (show ev ξ U hg t * a ∈ (ev ξ U hg).range from ⟨s, e.symm⟩)) ht`.
-/
theorem mem_range_ev {U : X.Opens} (hU : IsAffineOpen U) (hg : genPt ξ ∈ U) (hs : ∀ q ∈ U, genPt ξ ⤳ q)
    {a : Ω} (ha : ∀ q (hq : q ∈ U), a ∈ regAt ξ ⟨q, hs q hq⟩) : a ∈ (ev ξ U hg).range := by
  let I : Ideal Γ(X, U) :=
    { carrier := {t | ev ξ U hg t * a ∈ (ev ξ U hg).range}
      add_mem' := fun {t t'} ht ht' => by
        show ev ξ U hg (t + t') * a ∈ (ev ξ U hg).range
        rw [map_add, add_mul]; exact add_mem ht ht'
      zero_mem' := by
        show ev ξ U hg 0 * a ∈ (ev ξ U hg).range
        rw [map_zero, zero_mul]; exact zero_mem _
      smul_mem' := fun c t ht => by
        show ev ξ U hg (c * t) * a ∈ (ev ξ U hg).range
        rw [map_mul, mul_assoc]; exact mul_mem ⟨c, rfl⟩ ht }
  by_cases hI : I = ⊤
  · have : (1 : Γ(X, U)) ∈ I := hI ▸ Submodule.mem_top
    have h1 : ev ξ U hg 1 * a ∈ (ev ξ U hg).range := this
    rwa [map_one, one_mul] at h1
  · obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    let y : PrimeSpectrum Γ(X, U) := ⟨m, hm.isPrime⟩
    have hy := fromSpec_mem hU y
    obtain ⟨s, t, ht, e⟩ := exists_frac hU ⟨_, hs _ hy⟩ hy hg (ha _ hy)
    rw [primeIdealOf_fromSpec hU y hy] at ht
    exact absurd (hIm (show ev ξ U hg t * a ∈ (ev ξ U hg).range from ⟨s, e.symm⟩)) ht

/- English proof (translation)
Introduce and unpack `_ ⟨g, rfl⟩`. Use `⟨X.presheaf.stalkSpecializes h g, ?_⟩` and prove the remaining obligations. Use `congrArg (fun φ => φ.hom g) (X.presheaf.stalkSpecializes_comp q.2 h)` as an intermediate fact. Conclude with `congrArg (Scheme.stalkClosedPointTo ξ).hom this`.
-/
theorem regAt_mono {p q : Cpt ξ} (h : q.1 ⤳ p.1) : regAt ξ p ≤ regAt ξ q := by
  rintro _ ⟨g, rfl⟩
  refine ⟨X.presheaf.stalkSpecializes h g, ?_⟩
  have := congrArg (fun φ => φ.hom g) (X.presheaf.stalkSpecializes_comp q.2 h)
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom this

/- English proof (translation)
Take `⟨g, rfl⟩` from `hξ.bij.2 a`. Use `⟨g, ?_⟩` and prove the remaining obligations. Use `congrArg (fun φ => φ.hom g) (X.presheaf.stalkSpecializes_refl (genPt ξ))` as an intermediate fact. Conclude with `congrArg (Scheme.stalkClosedPointTo ξ).hom this`.
-/
theorem mem_regAt_gen (hξ : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨g, rfl⟩ := hξ.bij.2 a
  refine ⟨g, ?_⟩
  have := congrArg (fun φ => φ.hom g) (X.presheaf.stalkSpecializes_refl (genPt ξ))
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom this

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}

/- English proof (translation)
Take `⟨U, hU, hm⟩` from `h.affine c hc`. Establish `hg : genPt ξ ∈ U` using `(hm _).2 ⟨specializes_rfl, hc, fun _ => mem_regAt_gen h.gen _⟩`. Establish `hs : ∀ q ∈ U, genPt ξ ⤳ q` using `fun q hq => ((hm q).1 hq).1`. Use `⟨U, hU, hg, hm, ev_injective h.gen U hg hs, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[h.ring c hc]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩ p hp`. Conclude with `ev_mem p U ((hm _).2 ⟨p.2, hp⟩) hg s`. Introduce `ha`. Conclude with `mem_range_ev hU hg hs fun q hq => ha _ ((hm q).1 hq).2`.
-/
theorem chart (h : CoordTie o ξ x) (c : κ) (hc : x c ≠ 0) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hg : genPt ξ ∈ U),
      (∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) ∧ Function.Injective (ev ξ U hg) ∧
      ∀ a, a ∈ (ev ξ U hg).range ↔ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  obtain ⟨U, hU, hm⟩ := h.affine c hc
  have hg : genPt ξ ∈ U := (hm _).2 ⟨specializes_rfl, hc, fun _ => mem_regAt_gen h.gen _⟩
  have hs : ∀ q ∈ U, genPt ξ ⤳ q := fun q hq => ((hm q).1 hq).1
  refine ⟨U, hU, hg, hm, ev_injective h.gen U hg hs, fun a => ?_⟩
  rw [h.ring c hc]
  constructor
  · rintro ⟨s, rfl⟩ p hp
    exact ev_mem p U ((hm _).2 ⟨p.2, hp⟩) hg s
  · intro ha
    exact mem_range_ev hU hg hs fun q hq => ha _ ((hm q).1 hq).2

end SheetDecomposition.BBase
