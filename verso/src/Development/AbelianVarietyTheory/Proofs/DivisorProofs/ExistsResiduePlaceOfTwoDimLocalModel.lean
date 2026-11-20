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

namespace GlobalTheory.FieldPair

/- English proof (translation)
Introduce `L K _ _ cL cK Q hQ t u hm hdim S ψ hS ht hψ hc`. Use `letI := hQ.isLocalRing`. Establish `hSQ : ∀ q : Q, (q : L) ∈ S.ring` using `fun q => hS.1 q q.2`. Set `φ₀ : Q →+* S.ring` to `Q.subtype.codRestrict S.ring hSQ`. Set `φ : Q →+* K` to `ψ.comp φ₀`.

Establish `hker : ∀ s : S.ring, ψ s = 0 ↔ ¬ IsUnit s`. Introduce `s`. Establish `hmax` using `RingHom.ker_isMaximal_of_surjective ψ hψ`. Establish `h` using `IsLocalRing.eq_maximalIdeal hmax`. Rewrite using `[← RingHom.mem_ker, h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Establish `hunit : ∀ s : S.ring, (s : L) ≠ 0 → S.ord s = 0 → IsUnit s`. Introduce `s hs h0`. Establish `hinv : (s : L)⁻¹ ∈ S.ring` using `(S.ord_nonneg_iff (inv_ne_zero hs)).1 (by rw [S.ord_inv, h0, neg_zero])`. Conclude with `IsUnit.of_mul_eq_one (⟨_, hinv⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hs))`. Establish `hφt : φ t = 0` using `by show ψ (φ₀ t) = 0`.

Rewrite using `[hker]`. Introduce `hu`. Establish `h` using `S.ord_eq_zero hu`. Express the relevant statement in the definitionally equal form `S.ord (t : L) = 0 at h`. Rewrite `h` using `[ht]`.

Conclude with `one_ne_zero h`. Establish `hφu : φ u ≠ 0`. Introduce `hu0`. Establish `hsp : Ideal.span {t, u} ≤ RingHom.ker φ`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `x (rfl | rfl)`. Conclude with `hφt`. Conclude with `hu0`. Establish `hle : ∀ f ∈ S.ring, f ∈ Q`. Introduce `f hf`.

Take `⟨a, ha, b, hb, hb0, hbo, e⟩` from `hS.2 f hf`. Establish `hbu : IsUnit (⟨b, hb⟩ : Q)`. Assume the negation of the conclusion as `hnu`. Establish `h1 : φ ⟨b, hb⟩ = 0` using `hsp (hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hnu)`. Conclude with `(hker _).1 h1 (hunit (φ₀ ⟨b, hb⟩) hb0 hbo)`.

Take `⟨v, hv⟩` from `hbu.exists_right_inv`. Establish `hv' : b * (v : L) = 1` using `congrArg Subtype.val hv`. Establish `hf' : f = a * (v : L)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hf']`.

Conclude with `Q.mul_mem ha v.2`. Set `e : Q ≃+* S.ring` to `RingEquiv.ofBijective φ₀ ⟨fun x y h => Subtype.ext (congrArg (fun s : S.ring => (s : L)) h), fun s => ⟨⟨s, hle s s.2⟩, rfl⟩⟩`. Establish `h` using `ringKrullDim_eq_of_ringEquiv e`. Rewrite `h` using `[hdim, IsDiscreteValuationRing.ringKrullDim_eq_one]`. Evaluate the numerical expressions using `at h`.

Establish `hmemR : ∀ a : K, a ∈ φ.range ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a`. Introduce `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, rfl⟩`. Conclude with `⟨φ₀ q, q.2, rfl⟩`.

Introduce and unpack `⟨q, hq, rfl⟩`. Conclude with `⟨⟨q, hq⟩, rfl⟩`. Establish `hfrac : ∀ a : K, ∃ x y : Q, φ y ≠ 0 ∧ a * φ y = φ x`. Introduce `a`. Take `⟨s, rfl⟩` from `hψ a`.

Take `⟨x, hx, y, hy, hy0, hyo, e⟩` from `hS.2 s s.2`. Use `⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => (hker _).1 h (hunit (φ₀ ⟨y, hy⟩) hy0 hyo), ?_⟩` and prove the remaining obligations. Use `show ψ s * ψ (φ₀ ⟨y, hy⟩) = ψ (φ₀ ⟨x, hx⟩)`. Rewrite using `[← map_mul]`. Conclude with `congrArg ψ (Subtype.ext e)`.

Use `haveI : IsNoetherianRing Q := by`. Use `letI := (cL.codRestrict Q hQ.const_mem).toAlgebra`. Use `haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType`. Conclude with `Algebra.EssFiniteType.isNoetherianRing ℂ Q`. Set `R` to `φ.range`.

Set `φR : Q →+* R` to `φ.rangeRestrict`. Use `haveI : IsNoetherianRing R := isNoetherianRing_range φ`. Use `haveI : IsLocalRing R := IsLocalRing.of_surjective' φR φ.rangeRestrict_surjective`. Establish `hmR : IsLocalRing.maximalIdeal R = Ideal.span {φR u}`. Rewrite using `[← IsLocalRing.map_maximalIdeal_of_surjective φR φ.rangeRestrict_surjective, ← hm, Ideal.map_span, Set.image_pair]`.

Establish `h0 : φR t = 0` using `Subtype.ext hφt`. Rewrite using `[h0, Ideal.span_insert_zero]`. Establish `hu0R : φR u ≠ 0` using `fun h => hφu (congrArg Subtype.val h)`. Establish `hnf : ¬ IsField R`. Introduce `hf`.

Take `⟨w, hw⟩` from `hf.mul_inv_cancel hu0R`. Establish `hmem : φR u ∈ IsLocalRing.maximalIdeal R` using `hmR ▸ Ideal.subset_span rfl`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hmem (IsUnit.of_mul_eq_one w hw)`. Use `haveI hdvr : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R hnf).out 0 4).2 (show (IsLocalRing.maximalIdeal R).IsPrincipal from ⟨_, hmR⟩)`. Set `V : ValuationSubring K` to `{ R with mem_or_inv_mem' := by`.

Introduce `a`. Take `⟨x, y, hy, e⟩` from `hfrac a`. Take `⟨c, hc | hc⟩` from `ValuationRing.cond (φR x) (φR y)`. Use `right`. Establish `hc' : φ x * (c : K) = φ y` using `congrArg Subtype.val hc`.

Establish `h1 : a * c = 1`. Use `mul_right_cancel₀ hy ?_` and prove the remaining obligations. Take the linear combination `(c : K) * e + hc'`. Rewrite using `[inv_eq_of_mul_eq_one_right h1]`. Conclude with `c.2`.

Use `left`. Establish `hc' : φ y * (c : K) = φ x` using `congrArg Subtype.val hc`. Establish `h1 : a = c`. Use `mul_right_cancel₀ hy ?_` and prove the remaining obligations. Take the linear combination `e - hc'`.

Rewrite using `[h1]`. Conclude with `c.2 }`. Establish `hconst : ∀ a, cK a ∈ V` using `fun a => (hmemR (cK a)).2 ⟨S.const a, hQ.const_mem a, hc a⟩`. Establish `hφV : ∀ q : Q, φ q ∈ V` using `fun q => ⟨q, rfl⟩`. Set `φV : Q →+* V` to `φ.codRestrict V hφV`.

Establish `hφVs : Function.Surjective φV`. Introduce and unpack `⟨v, q, rfl⟩`. Conclude with `⟨q, rfl⟩`. Use `haveI hdvrV : IsDiscreteValuationRing V := hdvr`. Establish `hcomp : cK.codRestrict V hconst = φV.comp (cL.codRestrict Q hQ.const_mem)` using `RingHom.ext fun a => Subtype.ext (hc a).symm`.

Set `F : Place cK` to `⟨V, hconst, hdvrV, hcomp ▸ hQ.essFiniteType.comp (RingHom.FiniteType.of_surjective φV hφVs).essFiniteType⟩`. Use `⟨F, hmemR, fun us hus => ?_⟩` and prove the remaining obligations. Establish `h1 : ψ us = ((φV u : V) : K)` using `by show ψ us = ψ (φ₀ u)`. Conclude with `congrArg ψ (Subtype.ext hus)`. Establish `hmV : IsLocalRing.maximalIdeal V = Ideal.span {φV u}` using `hmR`.

Establish `hirr : Irreducible (φV u)` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmV`. Rewrite using `[h1]`. Conclude with `F.ord_irreducible hirr`.
-/
theorem residuePlace_of_locModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ (S : Place cL) (ψ : S.ring →+* K), S.IsPrimeOf Q → S.ord (t : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1 := by
  intro L K _ _ cL cK Q hQ t u hm hdim S ψ hS ht hψ hc
  letI := hQ.isLocalRing
  have hSQ : ∀ q : Q, (q : L) ∈ S.ring := fun q => hS.1 q q.2
  let φ₀ : Q →+* S.ring := Q.subtype.codRestrict S.ring hSQ
  let φ : Q →+* K := ψ.comp φ₀
  have hker : ∀ s : S.ring, ψ s = 0 ↔ ¬ IsUnit s := by
    intro s
    have hmax := RingHom.ker_isMaximal_of_surjective ψ hψ
    have h := IsLocalRing.eq_maximalIdeal hmax
    rw [← RingHom.mem_ker, h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hunit : ∀ s : S.ring, (s : L) ≠ 0 → S.ord s = 0 → IsUnit s := by
    intro s hs h0
    have hinv : (s : L)⁻¹ ∈ S.ring :=
      (S.ord_nonneg_iff (inv_ne_zero hs)).1 (by rw [S.ord_inv, h0, neg_zero])
    exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hs))
  have hφt : φ t = 0 := by
    show ψ (φ₀ t) = 0
    rw [hker]
    intro hu
    have h := S.ord_eq_zero hu
    change S.ord (t : L) = 0 at h
    rw [ht] at h
    exact one_ne_zero h
  have hφu : φ u ≠ 0 := by
    intro hu0
    have hsp : Ideal.span {t, u} ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact hφt
      · exact hu0
    have hle : ∀ f ∈ S.ring, f ∈ Q := by
      intro f hf
      obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f hf
      have hbu : IsUnit (⟨b, hb⟩ : Q) := by
        by_contra hnu
        have h1 : φ ⟨b, hb⟩ = 0 := hsp (hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hnu)
        exact (hker _).1 h1 (hunit (φ₀ ⟨b, hb⟩) hb0 hbo)
      obtain ⟨v, hv⟩ := hbu.exists_right_inv
      have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
      have hf' : f = a * (v : L) := by
        calc f = f * (b * v) := by rw [hv', mul_one]
          _ = a * v := by rw [← mul_assoc, e]
      rw [hf']
      exact Q.mul_mem ha v.2
    let e : Q ≃+* S.ring := RingEquiv.ofBijective φ₀
      ⟨fun x y h => Subtype.ext (congrArg (fun s : S.ring => (s : L)) h), fun s => ⟨⟨s, hle s s.2⟩, rfl⟩⟩
    have h := ringKrullDim_eq_of_ringEquiv e
    rw [hdim, IsDiscreteValuationRing.ringKrullDim_eq_one] at h
    norm_num at h
  have hmemR : ∀ a : K, a ∈ φ.range ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a := by
    intro a
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨φ₀ q, q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  have hfrac : ∀ a : K, ∃ x y : Q, φ y ≠ 0 ∧ a * φ y = φ x := by
    intro a
    obtain ⟨s, rfl⟩ := hψ a
    obtain ⟨x, hx, y, hy, hy0, hyo, e⟩ := hS.2 s s.2
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => (hker _).1 h (hunit (φ₀ ⟨y, hy⟩) hy0 hyo), ?_⟩
    show ψ s * ψ (φ₀ ⟨y, hy⟩) = ψ (φ₀ ⟨x, hx⟩)
    rw [← map_mul]
    exact congrArg ψ (Subtype.ext e)
  haveI : IsNoetherianRing Q := by
    letI := (cL.codRestrict Q hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing ℂ Q
  let R := φ.range
  let φR : Q →+* R := φ.rangeRestrict
  haveI : IsNoetherianRing R := isNoetherianRing_range φ
  haveI : IsLocalRing R := IsLocalRing.of_surjective' φR φ.rangeRestrict_surjective
  have hmR : IsLocalRing.maximalIdeal R = Ideal.span {φR u} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective φR φ.rangeRestrict_surjective, ← hm,
      Ideal.map_span, Set.image_pair]
    have h0 : φR t = 0 := Subtype.ext hφt
    rw [h0, Ideal.span_insert_zero]
  have hu0R : φR u ≠ 0 := fun h => hφu (congrArg Subtype.val h)
  have hnf : ¬ IsField R := by
    intro hf
    obtain ⟨w, hw⟩ := hf.mul_inv_cancel hu0R
    have hmem : φR u ∈ IsLocalRing.maximalIdeal R := hmR ▸ Ideal.subset_span rfl
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem (IsUnit.of_mul_eq_one w hw)
  haveI hdvr : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 0 4).2
      (show (IsLocalRing.maximalIdeal R).IsPrincipal from ⟨_, hmR⟩)
  let V : ValuationSubring K :=
    { R with
      mem_or_inv_mem' := by
        intro a
        obtain ⟨x, y, hy, e⟩ := hfrac a
        obtain ⟨c, hc | hc⟩ := ValuationRing.cond (φR x) (φR y)
        · right
          have hc' : φ x * (c : K) = φ y := congrArg Subtype.val hc
          have h1 : a * c = 1 := by
            refine mul_right_cancel₀ hy ?_
            linear_combination (c : K) * e + hc'
          rw [inv_eq_of_mul_eq_one_right h1]
          exact c.2
        · left
          have hc' : φ y * (c : K) = φ x := congrArg Subtype.val hc
          have h1 : a = c := by
            refine mul_right_cancel₀ hy ?_
            linear_combination e - hc'
          rw [h1]
          exact c.2 }
  have hconst : ∀ a, cK a ∈ V := fun a => (hmemR (cK a)).2 ⟨S.const a, hQ.const_mem a, hc a⟩
  have hφV : ∀ q : Q, φ q ∈ V := fun q => ⟨q, rfl⟩
  let φV : Q →+* V := φ.codRestrict V hφV
  have hφVs : Function.Surjective φV := by
    rintro ⟨v, q, rfl⟩
    exact ⟨q, rfl⟩
  haveI hdvrV : IsDiscreteValuationRing V := hdvr
  have hcomp : cK.codRestrict V hconst = φV.comp (cL.codRestrict Q hQ.const_mem) :=
    RingHom.ext fun a => Subtype.ext (hc a).symm
  let F : Place cK :=
    ⟨V, hconst, hdvrV, hcomp ▸ hQ.essFiniteType.comp (RingHom.FiniteType.of_surjective φV hφVs).essFiniteType⟩
  refine ⟨F, hmemR, fun us hus => ?_⟩
  have h1 : ψ us = ((φV u : V) : K) := by
    show ψ us = ψ (φ₀ u)
    exact congrArg ψ (Subtype.ext hus)
  have hmV : IsLocalRing.maximalIdeal V = Ideal.span {φV u} := hmR
  have hirr : Irreducible (φV u) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmV
  rw [h1]
  exact F.ord_irreducible hirr

end GlobalTheory.FieldPair
