import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceDominatingLocalDomainComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothFiniteTypeSubalgebraInRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointLocalRingClosedPointCentreOfPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLocalRingOfVarietyPointResidueCStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmoothNormalise

/- English proof (translation)
Take `⟨y, hy⟩` from `hF.mul_inv_cancel (a := (⟨f, hf⟩ : O)) (fun e => h0 (congrArg Subtype.val e))`. Establish `: f * (y : κ') = 1` using `congrArg Subtype.val hy`. Rewrite using `[inv_eq_of_mul_eq_one_right this]`. Conclude with `y.2`.
-/
theorem inv_mem_of_isField {κ' : Type} [Field κ'] {O : Subring κ'} (hF : IsField O) {f : κ'}
    (hf : f ∈ O) (h0 : f ≠ 0) : f⁻¹ ∈ O := by
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel (a := (⟨f, hf⟩ : O)) (fun e => h0 (congrArg Subtype.val e))
  have : f * (y : κ') = 1 := congrArg Subtype.val hy
  rw [inv_eq_of_mul_eq_one_right this]; exact y.2

/- English proof (translation)
Establish `hc : ∀ f ∈ O, ∃ α : ℂ, f = algebraMap ℂ κ' α`. Introduce `f hf`. Take `⟨α, hα, h⟩` from `hR f hf`. Use `⟨α, ?_⟩` and prove the remaining obligations. Break down `h with h | h` into its components or cases.

Conclude with `sub_eq_zero.1 h`. Assume the negation of the conclusion as `hne`. Conclude with `h (inv_mem_of_isField hF hα (sub_ne_zero.2 hne))`. Introduce `x`. Take `⟨a, ha, b, hb, hb0, e⟩` from `hO.frac x`.

Take `⟨α, rfl⟩` from `hc a ha`. Take `⟨β, rfl⟩` from `hc b hb`. Use `⟨α / β, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, eq_div_iff hb0, e]`.
-/
theorem const_of_isField {κ' : Type} [Field κ'] [Algebra ℂ κ'] {O : Subring κ'}
    (hO : IsLocModel (algebraMap ℂ κ') O) (hR : RatRes (algebraMap ℂ κ') O) (hF : IsField O) :
    ∀ x : κ', ∃ α : ℂ, x = algebraMap ℂ κ' α := by
  have hc : ∀ f ∈ O, ∃ α : ℂ, f = algebraMap ℂ κ' α := by
    intro f hf
    obtain ⟨α, hα, h⟩ := hR f hf
    refine ⟨α, ?_⟩
    rcases h with h | h
    · exact sub_eq_zero.1 h
    · by_contra hne
      exact h (inv_mem_of_isField hF hα (sub_ne_zero.2 hne))
  intro x
  obtain ⟨a, ha, b, hb, hb0, e⟩ := hO.frac x
  obtain ⟨α, rfl⟩ := hc a ha
  obtain ⟨β, rfl⟩ := hc b hb
  refine ⟨α / β, ?_⟩
  rw [map_div₀, eq_div_iff hb0, e]

/- English proof (translation)
Establish `hsurj : Function.Surjective ((algebraMap ℂ κ').codRestrict (⊤ : Subring κ') (fun _ => trivial))` using `fun x => by obtain ⟨α, hα⟩ := hc x; exact ⟨α, Subtype.ext hα.symm⟩`. Set `hB : IsLocModel (algebraMap ℂ κ') ⊤` to `{ const_mem := fun _ => trivial isLocalRing := (Subring.topEquiv (R := κ')).symm.isLocalRing essFiniteType := (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType frac := fun f => ⟨f, trivial, 1, trivial, one_ne_zero, mul_one f⟩ }`. Use `⟨hB, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r _`. Take `⟨α, hα⟩` from `hc r`.

Conclude with `⟨α, by rw [hα, sub_self]; exact nonUnit_zero _⟩`. Use `letI := hB.isLocalRing`. Establish `hfield : IsField (⊤ : Subring κ')`. Use `⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩` and prove the remaining obligations. Establish `ha' : (a : κ') ≠ 0` using `fun e => ha (Subtype.ext e)`.

Conclude with `⟨⟨(a : κ')⁻¹, trivial⟩, Subtype.ext (mul_inv_cancel₀ ha')⟩`. Rewrite using `[Set.range_eq_empty, Ideal.span_empty]`. Conclude with `IsLocalRing.isField_iff_maximalIdeal_eq.1 hfield`. Establish `hb : Function.Bijective (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ')))`. Use `⟨fun P Q e => ?_, fun x => ?_⟩` and prove the remaining obligations.

Rewrite `e`, the goal using `[MvPolynomial.eq_C_of_isEmpty P, MvPolynomial.eq_C_of_isEmpty Q]`. Simplify using `only [MvPolynomial.eval₂Hom_C] at e`. Conclude with `congrArg _ (((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem).injective e)`. Take `⟨α, hα⟩` from `hsurj x`. Conclude with `⟨MvPolynomial.C α, by simpa using hα⟩`.

Use `letI := (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))).toAlgebra`. Conclude with `Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hb)`. Establish `e : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ')` using `Algebra.algebra_ext _ _ fun _ => rfl`. Unfold `TrBasis`. Rewrite using `[e, isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]`.

Use `⟨algebraicIndependent_empty_type, ⟨fun x => ?_⟩⟩` and prove the remaining obligations. Take `⟨α, rfl⟩` from `hc x`. Conclude with `isAlgebraic_algebraMap (algebraMap ℂ (Algebra.adjoin ℂ (Set.range (fun i : Fin 0 => ((Fin.elim0 i : (⊤ : Subring κ')) : κ')))) α)`.
-/
theorem top_model_of_const {κ' : Type} [Field κ'] [Algebra ℂ κ']
    (hc : ∀ x : κ', ∃ α : ℂ, x = algebraMap ℂ κ' α) :
    ∃ (hB : IsLocModel (algebraMap ℂ κ') ⊤), RatRes (algebraMap ℂ κ') ⊤ ∧
    (letI := hB.isLocalRing; IsLocalRing.maximalIdeal (⊤ : Subring κ') = Ideal.span (Set.range (Fin.elim0 : Fin 0 → (⊤ : Subring κ')))) ∧
    (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))).FormallyEtale ∧
    TrBasis (algebraMap ℂ κ') (fun i => ((Fin.elim0 i : (⊤ : Subring κ')) : κ')) := by
  have hsurj : Function.Surjective ((algebraMap ℂ κ').codRestrict (⊤ : Subring κ') (fun _ => trivial)) :=
    fun x => by obtain ⟨α, hα⟩ := hc x; exact ⟨α, Subtype.ext hα.symm⟩
  let hB : IsLocModel (algebraMap ℂ κ') ⊤ :=
    { const_mem := fun _ => trivial
      isLocalRing := (Subring.topEquiv (R := κ')).symm.isLocalRing
      essFiniteType := (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
      frac := fun f => ⟨f, trivial, 1, trivial, one_ne_zero, mul_one f⟩ }
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · intro r _
    obtain ⟨α, hα⟩ := hc r
    exact ⟨α, by rw [hα, sub_self]; exact nonUnit_zero _⟩
  · letI := hB.isLocalRing
    have hfield : IsField (⊤ : Subring κ') := by
      refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
      have ha' : (a : κ') ≠ 0 := fun e => ha (Subtype.ext e)
      exact ⟨⟨(a : κ')⁻¹, trivial⟩, Subtype.ext (mul_inv_cancel₀ ha')⟩
    rw [Set.range_eq_empty, Ideal.span_empty]
    exact IsLocalRing.isField_iff_maximalIdeal_eq.1 hfield
  · have hb : Function.Bijective (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))) := by
      refine ⟨fun P Q e => ?_, fun x => ?_⟩
      · rw [MvPolynomial.eq_C_of_isEmpty P, MvPolynomial.eq_C_of_isEmpty Q] at e ⊢
        simp only [MvPolynomial.eval₂Hom_C] at e
        exact congrArg _ (((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem).injective e)
      · obtain ⟨α, hα⟩ := hsurj x
        exact ⟨MvPolynomial.C α, by simpa using hα⟩
    letI := (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))).toAlgebra
    exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hb)
  · have e : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
      Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e, isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_empty_type, ⟨fun x => ?_⟩⟩
    obtain ⟨α, rfl⟩ := hc x
    exact isAlgebraic_algebraMap (algebraMap ℂ (Algebra.adjoin ℂ (Set.range (fun i : Fin 0 => ((Fin.elim0 i : (⊤ : Subring κ')) : κ')))) α)

/- English proof (translation)
Introduce `h`. Use `(F.ord_nonneg_iff (inv_ne_zero hf)).2 (hBF h)` as an intermediate fact. Rewrite `this` using `[F.ord_inv]`. Use linear arithmetic over natural numbers and integers.
-/
theorem inv_not_mem {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ'))
    {B : Subring κ'} (hBF : B ≤ F.ring.toSubring) {f : κ'} (hf : f ≠ 0) (hp : 0 < F.ord f) :
    f⁻¹ ∉ B := by
  intro h
  have := (F.ord_nonneg_iff (inv_ne_zero hf)).2 (hBF h)
  rw [F.ord_inv] at this
  omega

/- English proof (translation)
Establish `hx'` using `(nonUnit_iff (R := B) ⟨x, hx.1⟩).1 hx`. Establish `hy'` using `(nonUnit_iff (R := B) ⟨y, hy.1⟩).1 hy`. Establish `h` using `(nonUnit_iff (R := B) (⟨x, hx.1⟩ - ⟨y, hy.1⟩)).2`. Conclude with `h ((IsLocalRing.mem_maximalIdeal _).1 (Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hx') ((IsLocalRing.mem_maximalIdeal _).2 hy')))`.
-/
theorem nonUnit_sub {κ' : Type} [Field κ'] {B : Subring κ'} [IsLocalRing B] {x y : κ'}
    (hx : NonUnit B x) (hy : NonUnit B y) : NonUnit B (x - y) := by
  have hx' := (nonUnit_iff (R := B) ⟨x, hx.1⟩).1 hx
  have hy' := (nonUnit_iff (R := B) ⟨y, hy.1⟩).1 hy
  have h := (nonUnit_iff (R := B) (⟨x, hx.1⟩ - ⟨y, hy.1⟩)).2
  exact h ((IsLocalRing.mem_maximalIdeal _).1 (Ideal.sub_mem _
    ((IsLocalRing.mem_maximalIdeal _).2 hx') ((IsLocalRing.mem_maximalIdeal _).2 hy')))

/- English proof (translation)
Introduce `κ' _ _ O l a hO hR ha`. Take `⟨j, hj⟩` from `Function.ne_iff.1 ha`. Distinguish the cases in `hF : IsField O`. Establish `hc` using `const_of_isField hO hR hF`. Take `⟨hB, h1, h2, h3, h4⟩` from `top_model_of_const hc`.

Use `⟨⊤, hB, 0, Fin.elim0, h1, fun f hf => ⟨trivial, fun hn => ?_⟩, h2, h3, h4, j, hj, fun _ => trivial⟩` and prove the remaining obligations. Use `⟨trivial, Or.inl ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Break down `hn.2 with h | h` into its components or cases. Conclude with `h0 h`.

Conclude with `h (inv_mem_of_isField hF hf h0)`. Take `⟨F, hFO, hpos⟩` from `GlobalTheory.T.exists_place_dominating_local_domain_complex O hO hF`. Choose the witnesses or unpack the hypotheses as in `⟨j₀, hj₀, hdiv⟩ : ∃ j₀, a j₀ ≠ 0 ∧ ∀ i, a i / a j₀ ∈ F.ring := by`. Take `⟨j₀, hj₀s, hmin⟩` from `(Finset.univ.filter (fun i => a i ≠ 0)).exists_min_image (fun i => F.ord (a i)) ⟨j, by simpa using hj⟩`. Establish `hj₀ : a j₀ ≠ 0` using `(Finset.mem_filter.1 hj₀s).2`.

Use `⟨j₀, hj₀, fun i => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi : a i = 0`. Rewrite using `[hi, zero_div]`. Conclude with `zero_mem _`. Establish `hne : a i / a j₀ ≠ 0` using `div_ne_zero hi hj₀`.

Rewrite using `[← F.ord_nonneg_iff hne, div_eq_mul_inv, F.ord_mul hi (inv_ne_zero hj₀), F.ord_inv]`. Use `hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `letI : Algebra ℂ O := ((algebraMap ℂ κ').codRestrict O hO.const_mem).toAlgebra`. Use `haveI : Algebra.EssFiniteType ℂ O := hO.essFiniteType`.

Take `⟨σ, hσ⟩` from `(Algebra.essFiniteType_iff ℂ O).1 inferInstance`. Set `S : Finset κ'` to `σ.image (fun x : O => (x : κ')) ∪ Finset.univ.image (fun i => a i / a j₀)`. Establish `hS : ∀ x ∈ S, x ∈ F.ring`. Introduce `x hx`. Break down `Finset.mem_union.1 hx with hx | hx` into its components or cases.

Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `hFO _ y.2`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `hdiv i`. Take `⟨A, hAs, hAF, hSA, hAfrac⟩` from `GlobalTheory.T.exists_smooth_finiteType_subalgebra_in_ring F S hS`.

Take `⟨B, hB, hRB, hAB, hBF, hsm⟩` from `GlobalTheory.T.exists_pointLocalRing_closedPoint_centre_of_place F A hAs hAF hAfrac`. Take `⟨r, τ, hm, het, htr⟩` from `GlobalTheory.T.exists_etaleCoords_localRingOfVarietyPoint_residueComplex B hB hRB hsm`. Establish `hSB : ∀ x ∈ S, x ∈ B` using `fun x hx => hAB (hSA x hx)`. Use `letI := hB.isLocalRing`. Use `letI := hO.isLocalRing`.

Establish `hadj : ∀ t : O, t ∈ Algebra.adjoin ℂ (σ : Set O) → (t : κ') ∈ B`. Introduce `t ht`. Proceed by induction on `ht using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hSB _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))`. Consider the case `algebraMap α => exact hB.const_mem α`.

Consider the case `add x y _ _ hx hy => exact B.add_mem hx hy`. Consider the case `mul x y _ _ hx hy => exact B.mul_mem hx hy`. Establish `hnon : ∀ f ∈ B, NonUnit O f → NonUnit B f`. Introduce `f hfB hn`. Use `⟨hfB, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h0 : f = 0`. Conclude with `Or.inl h0`. Use `Or.inr (inv_not_mem F hBF h0 (hpos ⟨f, hn.1⟩ ?_ h0))` and prove the remaining obligations. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 ((nonUnit_iff (R := O) ⟨f, hn.1⟩).1 hn)`. Establish `hunit : ∀ t : O, IsUnit t → (t : κ') ∈ B → (t : κ')⁻¹ ∈ B`.

Introduce `t ht htB`. Assume the negation of the conclusion as `hinv`. Establish `htn : NonUnit B (t : κ')` using `⟨htB, Or.inr hinv⟩`. Take `⟨α, hα⟩` from `hR t t.2`. Establish `hαB : algebraMap ℂ κ' α ∈ B` using `hB.const_mem α`.

Establish `hu : NonUnit B ((t : κ') - algebraMap ℂ κ' α)` using `hnon _ (B.sub_mem htB hαB) hα`. Establish `hc : NonUnit B (algebraMap ℂ κ' α)`. Simplify using `using nonUnit_sub htn hu`. Distinguish the cases in `hα0 : α = 0`. Substitute `hα0` using the available equality.

Simplify using `only [map_zero, sub_zero] at hα`. Conclude with `(nonUnit_iff (R := O) t).1 hα ht`. Break down `hc.2 with h | h` into its components or cases. Conclude with `hα0 ((map_eq_zero_iff _ (algebraMap ℂ κ').injective).1 h)`. Conclude with `h (by rw [← map_inv₀]; exact hB.const_mem _)`.

Use `⟨B, hB, r, τ, hRB, fun f hf => ?_, hm, het, htr, j₀, hj₀, fun i => hSB _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩` and prove the remaining obligations. Take `⟨t, htA, htu, hft⟩` from `hσ ⟨f, hf⟩`. Establish `htB` using `hadj t htA`. Establish `hfB : f ∈ B`. Establish `h1` using `hadj _ hft`.

Establish `h2` using `hunit t htu htB`. Establish `ht0 : (t : κ') ≠ 0` using `fun e => htu.ne_zero (Subtype.ext e)`. Establish `: f = (f * (t : κ')) * (t : κ')⁻¹` using `by field_simp`. Rewrite using `[this]`. Conclude with `B.mul_mem h1 h2`.

Conclude with `⟨hfB, hnon f hfB⟩`.
-/
theorem normalise_at_smooth_point : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (O : Subring κ') (l : ℕ) (a : Fin l → κ'),
  IsLocModel (algebraMap ℂ κ') O → RatRes (algebraMap ℂ κ') O → a ≠ 0 →
  ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B) (r : ℕ) (τ : Fin r → B),
    RatRes (algebraMap ℂ κ') B ∧ Dominates (RingHom.id κ') B O ∧
    (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
    (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
    TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) ∧ ∃ j₀, a j₀ ≠ 0 ∧ ∀ i, a i / a j₀ ∈ B := by
  classical
  intro κ' _ _ O l a hO hR ha
  obtain ⟨j, hj⟩ := Function.ne_iff.1 ha
  by_cases hF : IsField O
  · have hc := const_of_isField hO hR hF
    obtain ⟨hB, h1, h2, h3, h4⟩ := top_model_of_const hc
    refine ⟨⊤, hB, 0, Fin.elim0, h1, fun f hf => ⟨trivial, fun hn => ?_⟩, h2, h3, h4, j, hj,
      fun _ => trivial⟩
    refine ⟨trivial, Or.inl ?_⟩
    by_contra h0
    rcases hn.2 with h | h
    · exact h0 h
    · exact h (inv_mem_of_isField hF hf h0)
  · obtain ⟨F, hFO, hpos⟩ := GlobalTheory.T.exists_place_dominating_local_domain_complex O hO hF
    obtain ⟨j₀, hj₀, hdiv⟩ : ∃ j₀, a j₀ ≠ 0 ∧ ∀ i, a i / a j₀ ∈ F.ring := by
      obtain ⟨j₀, hj₀s, hmin⟩ := (Finset.univ.filter (fun i => a i ≠ 0)).exists_min_image
        (fun i => F.ord (a i)) ⟨j, by simpa using hj⟩
      have hj₀ : a j₀ ≠ 0 := (Finset.mem_filter.1 hj₀s).2
      refine ⟨j₀, hj₀, fun i => ?_⟩
      by_cases hi : a i = 0
      · rw [hi, zero_div]; exact zero_mem _
      · have hne : a i / a j₀ ≠ 0 := div_ne_zero hi hj₀
        rw [← F.ord_nonneg_iff hne, div_eq_mul_inv, F.ord_mul hi (inv_ne_zero hj₀), F.ord_inv]
        have := hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        omega
    letI : Algebra ℂ O := ((algebraMap ℂ κ').codRestrict O hO.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ O := hO.essFiniteType
    obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ O).1 inferInstance
    let S : Finset κ' := σ.image (fun x : O => (x : κ')) ∪ Finset.univ.image (fun i => a i / a j₀)
    have hS : ∀ x ∈ S, x ∈ F.ring := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
        exact hFO _ y.2
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hdiv i
    obtain ⟨A, hAs, hAF, hSA, hAfrac⟩ := GlobalTheory.T.exists_smooth_finiteType_subalgebra_in_ring F S hS
    obtain ⟨B, hB, hRB, hAB, hBF, hsm⟩ := GlobalTheory.T.exists_pointLocalRing_closedPoint_centre_of_place F A hAs hAF hAfrac
    obtain ⟨r, τ, hm, het, htr⟩ := GlobalTheory.T.exists_etaleCoords_localRingOfVarietyPoint_residueComplex B hB hRB hsm
    have hSB : ∀ x ∈ S, x ∈ B := fun x hx => hAB (hSA x hx)
    letI := hB.isLocalRing
    letI := hO.isLocalRing

    have hadj : ∀ t : O, t ∈ Algebra.adjoin ℂ (σ : Set O) → (t : κ') ∈ B := by
      intro t ht
      induction ht using Algebra.adjoin_induction with
      | mem x hx => exact hSB _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
      | algebraMap α => exact hB.const_mem α
      | add x y _ _ hx hy => exact B.add_mem hx hy
      | mul x y _ _ hx hy => exact B.mul_mem hx hy

    have hnon : ∀ f ∈ B, NonUnit O f → NonUnit B f := by
      intro f hfB hn
      refine ⟨hfB, ?_⟩
      by_cases h0 : f = 0
      · exact Or.inl h0
      · refine Or.inr (inv_not_mem F hBF h0 (hpos ⟨f, hn.1⟩ ?_ h0))
        exact (IsLocalRing.mem_maximalIdeal _).2 ((nonUnit_iff (R := O) ⟨f, hn.1⟩).1 hn)

    have hunit : ∀ t : O, IsUnit t → (t : κ') ∈ B → (t : κ')⁻¹ ∈ B := by
      intro t ht htB
      by_contra hinv
      have htn : NonUnit B (t : κ') := ⟨htB, Or.inr hinv⟩
      obtain ⟨α, hα⟩ := hR t t.2
      have hαB : algebraMap ℂ κ' α ∈ B := hB.const_mem α
      have hu : NonUnit B ((t : κ') - algebraMap ℂ κ' α) := hnon _ (B.sub_mem htB hαB) hα
      have hc : NonUnit B (algebraMap ℂ κ' α) := by
        simpa using nonUnit_sub htn hu
      by_cases hα0 : α = 0
      · subst hα0
        simp only [map_zero, sub_zero] at hα
        exact (nonUnit_iff (R := O) t).1 hα ht
      · rcases hc.2 with h | h
        · exact hα0 ((map_eq_zero_iff _ (algebraMap ℂ κ').injective).1 h)
        · exact h (by rw [← map_inv₀]; exact hB.const_mem _)
    refine ⟨B, hB, r, τ, hRB, fun f hf => ?_, hm, het, htr, j₀, hj₀,
      fun i => hSB _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩
    obtain ⟨t, htA, htu, hft⟩ := hσ ⟨f, hf⟩
    have htB := hadj t htA
    have hfB : f ∈ B := by
      have h1 := hadj _ hft
      have h2 := hunit t htu htB
      have ht0 : (t : κ') ≠ 0 := fun e => htu.ne_zero (Subtype.ext e)
      have : f = (f * (t : κ')) * (t : κ')⁻¹ := by field_simp
      rw [this]
      exact B.mul_mem h1 h2
    exact ⟨hfB, hnon f hfB⟩

end GlobalTheory.SmoothNormalise
