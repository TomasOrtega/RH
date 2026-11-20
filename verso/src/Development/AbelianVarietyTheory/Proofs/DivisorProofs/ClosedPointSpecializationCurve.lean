import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

open CategoryTheory AlgebraicGeometry Topology

namespace GlobalTheory.CurveThrough

/- English proof (translation)
Introduce `κ _ V _ q _ x U hx hU hxU`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, -⟩` from `V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Use `replace hW : IsAffineOpen W := hW`. Establish `: Nonempty W` using `⟨⟨x, hxW⟩⟩`. Set `φ` to `Spec.preimage (hW.fromSpec ≫ q)`.

Establish `hφ : Spec.map φ = hW.fromSpec ≫ q` using `Spec.map_preimage _`. Use `letI : Algebra κ Γ(V, W) := φ.hom.toAlgebra`. Use `haveI hft : Algebra.FiniteType κ Γ(V, W) := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)`. Use `haveI : IsNoetherianRing Γ(V, W) := Algebra.FiniteType.isNoetherianRing κ _`. Take `⟨f, hemb, hfr⟩ : ∃ f : PrimeSpectrum Γ(V, W) → V, IsOpenEmbedding f ∧ Set.range f = W` from `⟨hW.fromSpec, hW.fromSpec.isOpenEmbedding, hW.range_fromSpec⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨pt, hpt⟩ : ∃ pt : PrimeSpectrum Γ(V, W), f pt = x := by`. Rewrite using `[← Set.mem_range, hfr]`. Conclude with `hxW`. Establish `hmax : pt.asIdeal.IsMaximal`. Rewrite using `[← PrimeSpectrum.isClosed_singleton_iff_isMaximal]`.

Establish `e : ({pt} : Set (PrimeSpectrum Γ(V, W))) = f ⁻¹' {x}`. Use extensionality with `z`. Simplify using `only [Set.mem_singleton_iff, Set.mem_preimage, ← hpt]`. Conclude with `hemb.injective.eq_iff.symm`. Rewrite using `[e]`.

Conclude with `hx.preimage hemb.continuous`. Establish `hgen` using `genericPoint_spec V`. Establish `hηU : genericPoint V ∈ U` using `(hgen.mem_open_set_iff U.isOpen).mpr (by obtain ⟨v, hv⟩ := hU; exact ⟨v, trivial, hv⟩)`. Establish `hηW : genericPoint V ∈ W` using `(hgen.mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hxW⟩`. Choose the witnesses or unpack the hypotheses as in `⟨p₀, hp₀⟩ : ∃ p₀ : PrimeSpectrum Γ(V, W), f p₀ = genericPoint V := by`.

Rewrite using `[← Set.mem_range, hfr]`. Conclude with `hηW`. Establish `hp₀le : p₀.asIdeal ≤ pt.asIdeal` using `by show p₀ ≤ pt`. Rewrite using `[PrimeSpectrum.le_iff_specializes, ← hemb.isInducing.specializes_iff, hp₀, hpt]`. Conclude with `hgen.specializes (Set.mem_univ x)`.

Take `⟨q', hq'U, hqm, h1⟩` from `GlobalTheory.exists_mem_height_map_le_one pt.asIdeal (U := f ⁻¹' (U : Set V)) (U.isOpen.preimage hemb.continuous) ⟨p₀, by rw [Set.mem_preimage, hp₀]; exact hηU, hp₀le⟩`. Establish `hsurj` using `Ideal.Quotient.mk_surjective (I := q'.asIdeal)`. Establish `hmax' : (pt.asIdeal.map (Ideal.Quotient.mk q'.asIdeal)).IsMaximal` using `Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)`. Establish `h2 : (pt.asIdeal.map (Ideal.Quotient.mk q'.asIdeal)).height ≠ 0`. Rewrite using `[Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]`.

Introduce `e`. Establish `hle : pt.asIdeal ≤ q'.asIdeal` using `fun a ha => by`. Use `Ideal.mem_map_of_mem (Ideal.Quotient.mk q'.asIdeal) ha` as an intermediate fact. Rewrite `this` using `[e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Then use the resulting hypothesis. Establish `hq : q' = pt` using `PrimeSpectrum.ext (le_antisymm hqm hle)`.

Apply `hxU` to reduce the goal to its premises. Rewrite using `[← hpt, ← hq]`. Conclude with `hq'U`. Establish `h3` using `le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)`. Take `⟨s, hs1, hs2⟩` from `ReciprocityTheory.CA.exists_dim_trdeg_field (K := κ) (A := Γ(V, W) ⧸ q'.asIdeal)`.

Establish `h4` using `ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field s hs2 (pt.asIdeal.map (Ideal.Quotient.mk q'.asIdeal))`. Rewrite `h4` using `[h3]`. Establish `h5 : s = 1` using `by exact_mod_cast h4.symm`. Establish `hdim : ringKrullDim (Γ(V, W) ⧸ q'.asIdeal) = 1` using `by rw [hs1, h5]; rfl`. Use `⟨f q', hq'U, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hpt]`. Conclude with `((PrimeSpectrum.le_iff_specializes _ _).mp hqm).map hemb.continuous`. Use `set y := f q' with hy`. Take `⟨Z, i, hi, hZ, hgenZ⟩` from `GlobalTheory.exists_isClosedImmersion_genericPoint y`. Establish `hrange : Set.range i = closure ({y} : Set V)`.

Establish `h₁` using `(genericPoint_spec Z).image i.continuous`. Rewrite `h₁` using `[Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hgenZ]`. Conclude with `(isGenericPoint_def.mp h₁).symm`. Establish `hyW : y ∈ W` using `by show y ∈ (W : Set V)`. Rewrite using `[← hfr]`.

Conclude with `⟨q', rfl⟩`. Establish `hηZ : genericPoint Z ∈ (i ⁻¹ᵁ W : Z.Opens)` using `by show i (genericPoint Z) ∈ W`. Rewrite using `[hgenZ]`. Conclude with `hyW`. Establish `d1 : topologicalKrullDim (closure ({y} : Set V)) = topologicalKrullDim Z` using `GlobalTheory.topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange`.

Establish `d2 : topologicalKrullDim ((i ⁻¹ᵁ W : Z.Opens) : Set Z) = topologicalKrullDim Z` using `GlobalTheory.OpenDim.topologicalKrullDim_open κ (i ≫ q) (i ⁻¹ᵁ W) ⟨_, hηZ⟩`. Establish `d3 : topologicalKrullDim (closure ({y} : Set V) ∩ W : Set V) = topologicalKrullDim ((i ⁻¹ᵁ W : Z.Opens) : Set Z)`. Use `GlobalTheory.topologicalKrullDim_eq_of_isEmbedding (i.isClosedEmbedding.isEmbedding.comp IsEmbedding.subtypeVal) ?_` and prove the remaining obligations. Rewrite using `[Set.range_comp, Subtype.range_coe, ← hrange]`. Use extensionality with `v`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨⟨z, rfl⟩, hz⟩`. Introduce and unpack `⟨⟨z, rfl⟩, hz⟩`. Conclude with `⟨z, hz, rfl⟩`.

Establish `d4 : topologicalKrullDim (closure ({y} : Set V) ∩ W : Set V) = topologicalKrullDim (PrimeSpectrum (Γ(V, W) ⧸ q'.asIdeal))`. Use `GlobalTheory.topologicalKrullDim_eq_of_isEmbedding (hemb.isEmbedding.comp (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (Ideal.Quotient.mk q'.asIdeal) hsurj).isEmbedding) ?_` and prove the remaining obligations. Rewrite using `[Set.range_comp, range_comap_of_surjective (f := Ideal.Quotient.mk q'.asIdeal) (hf := hsurj), Ideal.mk_ker]`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨p, hp, rfl⟩`. Establish `hle : q' ≤ p` using `(PrimeSpectrum.mem_zeroLocus _ _).mp hp`. Use `⟨specializes_iff_mem_closure.mp (((PrimeSpectrum.le_iff_specializes q' p).mp hle).map hemb.continuous), ?_⟩` and prove the remaining obligations. Rewrite using `[← hfr]`. Conclude with `⟨p, rfl⟩`.

Introduce and unpack `⟨hv, hvW⟩`. Rewrite `hvW` using `[← hfr]`. Take `⟨p, rfl⟩` from `hvW`. Use `⟨p, ?_, rfl⟩` and prove the remaining obligations. Establish `h` using `hemb.isInducing.specializes_iff.mp (specializes_iff_mem_closure.mpr hv)`.

Conclude with `(PrimeSpectrum.mem_zeroLocus _ _).mpr ((PrimeSpectrum.le_iff_specializes _ _).mpr h)`. Rewrite using `[d1, ← d2, ← d3, d4, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]`.
-/
theorem exists_curve_through_closedPoint :
    ∀ (κ : Type) [Field κ] (V : Scheme.{0}) [IsIntegral V] (q : V ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType q] (x : V) (U : V.Opens), IsClosed ({x} : Set V) → (∃ v, v ∈ U) →
    x ∉ U → ∃ y : V, y ∈ U ∧ y ⤳ x ∧ topologicalKrullDim (closure ({y} : Set V)) = 1 := by
  intro κ _ V _ q _ x U hx hU hxU
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hW : IsAffineOpen W := hW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  let φ := Spec.preimage (hW.fromSpec ≫ q)
  have hφ : Spec.map φ = hW.fromSpec ≫ q := Spec.map_preimage _
  letI : Algebra κ Γ(V, W) := φ.hom.toAlgebra
  haveI hft : Algebra.FiniteType κ Γ(V, W) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  haveI : IsNoetherianRing Γ(V, W) := Algebra.FiniteType.isNoetherianRing κ _
  obtain ⟨f, hemb, hfr⟩ : ∃ f : PrimeSpectrum Γ(V, W) → V, IsOpenEmbedding f ∧ Set.range f = W :=
    ⟨hW.fromSpec, hW.fromSpec.isOpenEmbedding, hW.range_fromSpec⟩
  obtain ⟨pt, hpt⟩ : ∃ pt : PrimeSpectrum Γ(V, W), f pt = x := by
    rw [← Set.mem_range, hfr]; exact hxW
  have hmax : pt.asIdeal.IsMaximal := by
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    have e : ({pt} : Set (PrimeSpectrum Γ(V, W))) = f ⁻¹' {x} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage, ← hpt]
      exact hemb.injective.eq_iff.symm
    rw [e]
    exact hx.preimage hemb.continuous
  have hgen := genericPoint_spec V
  have hηU : genericPoint V ∈ U := (hgen.mem_open_set_iff U.isOpen).mpr
    (by obtain ⟨v, hv⟩ := hU; exact ⟨v, trivial, hv⟩)
  have hηW : genericPoint V ∈ W := (hgen.mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hxW⟩
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : PrimeSpectrum Γ(V, W), f p₀ = genericPoint V := by
    rw [← Set.mem_range, hfr]; exact hηW
  have hp₀le : p₀.asIdeal ≤ pt.asIdeal := by
    show p₀ ≤ pt
    rw [PrimeSpectrum.le_iff_specializes, ← hemb.isInducing.specializes_iff, hp₀, hpt]
    exact hgen.specializes (Set.mem_univ x)
  obtain ⟨q', hq'U, hqm, h1⟩ := GlobalTheory.exists_mem_height_map_le_one pt.asIdeal
    (U := f ⁻¹' (U : Set V)) (U.isOpen.preimage hemb.continuous)
    ⟨p₀, by rw [Set.mem_preimage, hp₀]; exact hηU, hp₀le⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q'.asIdeal)
  have hmax' : (pt.asIdeal.map (Ideal.Quotient.mk q'.asIdeal)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have h2 : (pt.asIdeal.map (Ideal.Quotient.mk q'.asIdeal)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro e
    have hle : pt.asIdeal ≤ q'.asIdeal := fun a ha => by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk q'.asIdeal) ha
      rwa [e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    have hq : q' = pt := PrimeSpectrum.ext (le_antisymm hqm hle)
    apply hxU
    rw [← hpt, ← hq]
    exact hq'U
  have h3 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := κ) (A := Γ(V, W) ⧸ q'.asIdeal)
  have h4 := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field s hs2
    (pt.asIdeal.map (Ideal.Quotient.mk q'.asIdeal))
  rw [h3] at h4
  have h5 : s = 1 := by exact_mod_cast h4.symm
  have hdim : ringKrullDim (Γ(V, W) ⧸ q'.asIdeal) = 1 := by rw [hs1, h5]; rfl
  refine ⟨f q', hq'U, ?_, ?_⟩
  · rw [← hpt]
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hqm).map hemb.continuous
  set y := f q' with hy
  obtain ⟨Z, i, hi, hZ, hgenZ⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint y
  have hrange : Set.range i = closure ({y} : Set V) := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hgenZ] at h₁
    exact (isGenericPoint_def.mp h₁).symm
  have hyW : y ∈ W := by
    show y ∈ (W : Set V)
    rw [← hfr]; exact ⟨q', rfl⟩
  have hηZ : genericPoint Z ∈ (i ⁻¹ᵁ W : Z.Opens) := by
    show i (genericPoint Z) ∈ W
    rw [hgenZ]; exact hyW
  have d1 : topologicalKrullDim (closure ({y} : Set V)) = topologicalKrullDim Z :=
    GlobalTheory.topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange
  have d2 : topologicalKrullDim ((i ⁻¹ᵁ W : Z.Opens) : Set Z) = topologicalKrullDim Z :=
    GlobalTheory.OpenDim.topologicalKrullDim_open κ (i ≫ q) (i ⁻¹ᵁ W) ⟨_, hηZ⟩
  have d3 : topologicalKrullDim (closure ({y} : Set V) ∩ W : Set V) =
      topologicalKrullDim ((i ⁻¹ᵁ W : Z.Opens) : Set Z) := by
    refine GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
      (i.isClosedEmbedding.isEmbedding.comp IsEmbedding.subtypeVal) ?_
    rw [Set.range_comp, Subtype.range_coe, ← hrange]
    ext v; constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, rfl⟩, hz⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩; exact ⟨z, hz, rfl⟩
  have d4 : topologicalKrullDim (closure ({y} : Set V) ∩ W : Set V) =
      topologicalKrullDim (PrimeSpectrum (Γ(V, W) ⧸ q'.asIdeal)) := by
    refine GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
      (hemb.isEmbedding.comp (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _
        (Ideal.Quotient.mk q'.asIdeal) hsurj).isEmbedding) ?_
    rw [Set.range_comp, range_comap_of_surjective (f := Ideal.Quotient.mk q'.asIdeal) (hf := hsurj), Ideal.mk_ker]
    ext v; constructor
    · rintro ⟨p, hp, rfl⟩
      have hle : q' ≤ p := (PrimeSpectrum.mem_zeroLocus _ _).mp hp
      refine ⟨specializes_iff_mem_closure.mp
        (((PrimeSpectrum.le_iff_specializes q' p).mp hle).map hemb.continuous), ?_⟩
      rw [← hfr]; exact ⟨p, rfl⟩
    · rintro ⟨hv, hvW⟩
      rw [← hfr] at hvW
      obtain ⟨p, rfl⟩ := hvW
      refine ⟨p, ?_, rfl⟩
      have h := hemb.isInducing.specializes_iff.mp (specializes_iff_mem_closure.mpr hv)
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr ((PrimeSpectrum.le_iff_specializes _ _).mpr h)
  rw [d1, ← d2, ← d3, d4, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]

end GlobalTheory.CurveThrough
