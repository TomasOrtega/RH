import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.ratFibre

/- English proof (translation)
Establish `hred (y : Y) : _root_.IsReduced (Y.presheaf.stalk y)`. Establish `h1` using `Flat.stalkMap j y`. Establish `h2` using `j.stalkMap_surjective y`. Use `algebraize [(j.stalkMap y).hom]`. Establish `: IsLocalHom (algebraMap (X.presheaf.stalk (j y)) (Y.presheaf.stalk y))` using `inferInstanceAs (IsLocalHom (j.stalkMap y).hom)`.

Use `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j y)) (B := Y.presheaf.stalk y)` as an intermediate fact. Conclude with `isReduced_of_injective (RingEquiv.ofBijective (j.stalkMap y).hom ⟨FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j y)) (Y.presheaf.stalk y), h2⟩).symm (RingEquiv.injective _)`. Establish `: IsReduced Y` using `isReduced_of_isReduced_stalk Y`. Take `⟨y₀⟩` from `‹Nonempty Y›`. Take `⟨η, -, hη⟩` from `Flat.generalizingMap j (genericPoint_specializes (j y₀))`.

Establish `hg : IsGenericPoint η (Set.univ : Set Y)`. Use `Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1 ?_` and prove the remaining obligations. Rewrite using `[← j.isEmbedding.isInducing.specializes_iff, hη]`. Conclude with `genericPoint_specializes _`. Establish `: IrreducibleSpace Y` using `(irreducibleSpace_def Y).2 hg.isIrreducible`.

Conclude with `isIntegral_of_irreducibleSpace_of_isReduced Y`.
-/
theorem isIntegral_of_flat_preimmersion {X Y : Scheme.{0}} [IsIntegral X] [Nonempty Y] (j : Y ⟶ X)
    [Flat j] [IsPreimmersion j] : IsIntegral Y := by
  have hred (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    have h1 := Flat.stalkMap j y
    have h2 := j.stalkMap_surjective y
    algebraize [(j.stalkMap y).hom]
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j y)) (Y.presheaf.stalk y)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap y).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j y))
      (B := Y.presheaf.stalk y)
    exact isReduced_of_injective (RingEquiv.ofBijective (j.stalkMap y).hom
      ⟨FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j y)) (Y.presheaf.stalk y), h2⟩).symm
      (RingEquiv.injective _)
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  obtain ⟨η, -, hη⟩ := Flat.generalizingMap j (genericPoint_specializes (j y₀))
  have hg : IsGenericPoint η (Set.univ : Set Y) := by
    refine Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1 ?_
    rw [← j.isEmbedding.isInducing.specializes_iff, hη]
    exact genericPoint_specializes _
  have : IrreducibleSpace Y := (irreducibleSpace_def Y).2 hg.isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/- English proof (translation)
Take `⟨A, _, _, _, _, _, i, _, -, -, hA⟩` from `exists_affine_chart_trdeg_eq f (genericPoint X)`. Take `⟨d, hd⟩` from `exists_trdeg_eq_natCast ℤ (A := A)`. Rewrite `hd` using `[hA]`. Establish `h₁` using `topologicalKrullDim_preimage_genericPoint_eq f hd`. Use `IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)` as an intermediate fact.

Take `⟨e₁, r₁⟩` from `isEmbedding_and_range_eq_of_isPullback f H`. Establish `hr₁ : Set.range (spMap (algebraMap ℤ ℚ)) = {genericPoint (Spec (.of ℤ))}`. Use `Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[genericPoint_eq_bot_of_affine]`.

Use `PrimeSpectrum.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap ℤ ℚ) x.asIdeal = ⊥`. Use `x.isPrime` as an intermediate fact. Rewrite using `[Ideal.eq_bot_of_prime x.asIdeal]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective ℤ ℚ)`.

Rewrite `r₁` using `[hr₁]`. Establish `h₂` using `(topologicalKrullDim_eq_of_isEmbedding e₁ r₁).symm.trans h₁`. Establish `h₃` using `IntModel.topologicalKrullDim_eq_succ Int.not_isField H h₂`. Establish `h₄ : D + 1 = d + 1` using `by exact_mod_cast hD.symm.trans h₃`. Take `rfl : D = d` from `by omega`.

Conclude with `h₂`.
-/
theorem dim_eq_of_isPullback {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp ℤ) [IsProper f] [Flat f]
    {j : Y ⟶ X} {q : Y ⟶ Sp ℚ} (H : IsPullback j q f (spMap (algebraMap ℤ ℚ))) {D : ℕ}
    (hD : topologicalKrullDim X = (D + 1 : ℕ)) : topologicalKrullDim Y = D := by
  obtain ⟨A, _, _, _, _, _, i, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq f (genericPoint X)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  rw [hA] at hd
  have h₁ := topologicalKrullDim_preimage_genericPoint_eq f hd
  have := IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  obtain ⟨e₁, r₁⟩ := isEmbedding_and_range_eq_of_isPullback f H
  have hr₁ : Set.range (spMap (algebraMap ℤ ℚ)) = {genericPoint (Spec (.of ℤ))} := by
    refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap ℤ ℚ) x.asIdeal = ⊥
    have := x.isPrime
    rw [Ideal.eq_bot_of_prime x.asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective ℤ ℚ)
  rw [hr₁] at r₁
  have h₂ := (topologicalKrullDim_eq_of_isEmbedding e₁ r₁).symm.trans h₁
  have h₃ := IntModel.topologicalKrullDim_eq_succ Int.not_isField H h₂
  have h₄ : D + 1 = d + 1 := by exact_mod_cast hD.symm.trans h₃
  obtain rfl : D = d := by omega
  exact h₂

/- English proof (translation)
Use `h.finite` as an intermediate fact. Use `h.isIntegral` as an intermediate fact. Use `h.flat` as an intermediate fact. Establish `: IsFinite (spMap (Int.castRingHom k))`. Rewrite using `[IsFinite.SpecMap_iff]`.

Conclude with `RingHom.finite_algebraMap.2 h.finite`. Take `⟨_, L, hL⟩` from `(isProjOver_iff_isProper_and_exists_isAmpleLB p).1 h.isProjOver`. Establish `hP : IsProjOver (p ≫ spMap (Int.castRingHom k))` using `hL.isProjOver _`. Establish `H : IsPullback (fst p) (snd p) (p ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℤ ℚ))` using `isPullback p`. Establish `hd : topologicalKrullDim (ratFibre p) = (1 : ℕ)` using `dim_eq_of_isPullback _ H h.dim_eq`.

Establish `: Nonempty (ratFibre p)`. Assume the negation of the conclusion as `hn`. Establish `: IsEmpty (ratFibre p)` using `not_nonempty_iff.1 hn`. Establish `: IsEmpty (IrreducibleCloseds (ratFibre p))` using `⟨fun Z => Z.isIrreducible.nonempty.elim fun x _ => isEmptyElim x⟩`. Rewrite `hd` using `[topologicalKrullDim, Order.krullDim_eq_bot]`.

Conclude with `absurd hd (by decide)`. Establish `h₁ : IsPreimmersion (spMap (algebraMap ℤ ℚ))` using `IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)`. Establish `h₂ : Flat (spMap (algebraMap ℤ ℚ))` using `(flat_int_iff_charZero _).2 (((Scheme.ΓSpecIso (.of ℚ)).commRingCatIsoToRingEquiv.toRingHom.charZero_iff (Scheme.ΓSpecIso (.of ℚ)).commRingCatIsoToRingEquiv.injective).2 (inferInstanceAs (CharZero ℚ)))`. Establish `: IsPreimmersion (fst p)` using `MorphismProperty.of_isPullback H.flip h₁`. Establish `: Flat (fst p)` using `MorphismProperty.of_isPullback H.flip h₂`.

Use `⟨isIntegral_of_flat_preimmersion (fst p), hd.trans Nat.cast_one, ?_⟩` and prove the remaining obligations. Rewrite using `[strHom_eq]`. Conclude with `ProjSpace.isProjOver_of_isPullback_spMap _ H hP`.
-/
theorem isProjCurve (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsArithVar p 1) :
    IsProjCurve ℚ (ratFibre p) := by
  have := h.finite
  have := h.isIntegral
  have := h.flat
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 h.finite
  obtain ⟨_, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 h.isProjOver
  have hP : IsProjOver (p ≫ spMap (Int.castRingHom k)) := hL.isProjOver _
  have H : IsPullback (fst p) (snd p) (p ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℤ ℚ)) :=
    isPullback p
  have hd : topologicalKrullDim (ratFibre p) = (1 : ℕ) := dim_eq_of_isPullback _ H h.dim_eq
  have : Nonempty (ratFibre p) := by
    by_contra hn
    have : IsEmpty (ratFibre p) := not_nonempty_iff.1 hn
    have : IsEmpty (IrreducibleCloseds (ratFibre p)) :=
      ⟨fun Z => Z.isIrreducible.nonempty.elim fun x _ => isEmptyElim x⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot] at hd
    exact absurd hd (by decide)
  have h₁ : IsPreimmersion (spMap (algebraMap ℤ ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  have h₂ : Flat (spMap (algebraMap ℤ ℚ)) :=
    (flat_int_iff_charZero _).2 (((Scheme.ΓSpecIso (.of ℚ)).commRingCatIsoToRingEquiv.toRingHom.charZero_iff
      (Scheme.ΓSpecIso (.of ℚ)).commRingCatIsoToRingEquiv.injective).2 (inferInstanceAs (CharZero ℚ)))
  have : IsPreimmersion (fst p) := MorphismProperty.of_isPullback H.flip h₁
  have : Flat (fst p) := MorphismProperty.of_isPullback H.flip h₂
  refine ⟨isIntegral_of_flat_preimmersion (fst p), hd.trans Nat.cast_one, ?_⟩
  rw [strHom_eq]
  exact ProjSpace.isProjOver_of_isPullback_spMap _ H hP

end GlobalTheory.ratFibre
