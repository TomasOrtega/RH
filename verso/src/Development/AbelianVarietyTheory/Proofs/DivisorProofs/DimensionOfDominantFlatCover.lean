import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DimCover

/- English proof (translation)
Take `⟨A, _, _, _, _, _, j, _, -, -, hA⟩` from `exists_affine_chart_trdeg_eq f (genericPoint X)`. Take `⟨d, hd⟩` from `exists_trdeg_eq_natCast ℤ (A := A)`. Rewrite `hd` using `[hA]`. Establish `h₁` using `topologicalKrullDim_preimage_genericPoint_eq f hd`. Establish `H` using `IsPullback.of_hasPullback f (spMap (algebraMap ℤ ℚ))`.

Use `IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)` as an intermediate fact. Take `⟨e₁, r₁⟩` from `isEmbedding_and_range_eq_of_isPullback f H`. Establish `hr₁ : Set.range (spMap (algebraMap ℤ ℚ)) = {genericPoint (Spec (.of ℤ))}`. Use `Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[genericPoint_eq_bot_of_affine]`. Use `PrimeSpectrum.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap ℤ ℚ) x.asIdeal = ⊥`. Use `x.isPrime` as an intermediate fact. Rewrite using `[Ideal.eq_bot_of_prime x.asIdeal]`.

Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective ℤ ℚ)`. Rewrite `r₁` using `[hr₁]`. Use `⟨d, ?_, IntModel.topologicalKrullDim_eq_succ Int.not_isField H ((topologicalKrullDim_eq_of_isEmbedding e₁ r₁).symm.trans h₁)⟩` and prove the remaining obligations. Establish `hb : Function.Bijective (IsLocalRing.residue X.functionField)` using `⟨RingHom.injective _, IsLocalRing.residue_surjective⟩`. Establish `e` using `((RingEquiv.ofBijective _ hb).toIntAlgEquiv).trdeg_eq`.

Conclude with `e.symm.trans ((congrArg (@Algebra.trdeg ℤ X.functionField _ _) (Subsingleton.elim _ _)).trans hd)`.
-/
theorem exists_trdeg_eq_and_dim_eq {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp ℤ) [IsProper f]
    [Flat f] : ∃ d : ℕ, Algebra.trdeg ℤ (X.residueField (genericPoint X)) = d ∧
      topologicalKrullDim X = (d + 1 : ℕ) := by
  obtain ⟨A, _, _, _, _, _, j, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq f (genericPoint X)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  rw [hA] at hd
  have h₁ := topologicalKrullDim_preimage_genericPoint_eq f hd
  have H := IsPullback.of_hasPullback f (spMap (algebraMap ℤ ℚ))
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
  refine ⟨d, ?_, IntModel.topologicalKrullDim_eq_succ Int.not_isField H
    ((topologicalKrullDim_eq_of_isEmbedding e₁ r₁).symm.trans h₁)⟩
  have hb : Function.Bijective (IsLocalRing.residue X.functionField) :=
    ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩
  have e := ((RingEquiv.ofBijective _ hb).toIntAlgEquiv).trdeg_eq
  exact e.symm.trans
    ((congrArg (@Algebra.trdeg ℤ X.functionField _ _) (Subsingleton.elim _ _)).trans hd)

/- English proof (translation)
Use `(flat_int_iff_charZero f).1 inferInstance` as an intermediate fact. Establish `: CharZero X.functionField` using `((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.charZero_iff (germ_injective_of_isIntegral X _ _)).1 this`. Conclude with `((IsLocalRing.residue X.functionField).charZero_iff (RingHom.injective _)).1 this`.
-/
theorem charZero_residueField {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp ℤ) [Flat f] :
    CharZero (X.residueField (genericPoint X)) := by
  have := (flat_int_iff_charZero f).1 inferInstance
  have : CharZero X.functionField :=
    ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.charZero_iff
      (germ_injective_of_isIntegral X _ _)).1 this
  exact ((IsLocalRing.residue X.functionField).charZero_iff (RingHom.injective _)).1 this

/- English proof (translation)
Use `h.finite` as an intermediate fact. Establish `: IsFinite (spMap (Int.castRingHom k))`. Rewrite using `[IsFinite.SpecMap_iff]`. Conclude with `RingHom.finite_algebraMap.2 this`. Use `CommonModel.isProper_of_isProjOver hq` as an intermediate fact.

Use `CommonModel.isProper_of_isProjOver h.isProjOver` as an intermediate fact. Use `h.flat` as an intermediate fact. Take `⟨a, ha, ha'⟩` from `exists_trdeg_eq_and_dim_eq (p ≫ spMap (Int.castRingHom k))`. Take `⟨b, hb, hb'⟩` from `exists_trdeg_eq_and_dim_eq (q ≫ spMap (Int.castRingHom k))`. Rewrite `ha` using `[← hη]`.

Set `` to `(g.residueFieldMap (genericPoint Z)).hom.toAlgebra`. Establish `: Module.Finite (Y.residueField (g (genericPoint Z))) (Z.residueField (genericPoint Z))` using `Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hd)`. Establish `: CharZero (Y.residueField (g (genericPoint Z)))` using `hη ▸ charZero_residueField (p ≫ spMap (Int.castRingHom k))`. Establish `e` using `trdeg_eq_of_isAlgebraic_top ℤ (Y.residueField (g (genericPoint Z))) (Z.residueField (genericPoint Z))`. Take `rfl : b = a` from `by exact_mod_cast hb.symm.trans (e.trans ha)`.

Rewrite using `[hb', ← ha', h.dim_eq]`.
-/
theorem topologicalKrullDim_eq (k : Type) [CommRing k] (Y Z : Scheme.{0}) [IsIntegral Y]
    [IsIntegral Z] (p : Y ⟶ Sp k) (q : Z ⟶ Sp k) (D : ℕ) (h : IsArithVar p D) (hq : IsProjOver q)
    (hf : Flat (q ≫ spMap (Int.castRingHom k))) (g : Z ⟶ Y) (_ : g ≫ p = q)
    (hη : g (genericPoint Z) = genericPoint Y) (hd : g.residueDegree (genericPoint Z) ≠ 0) :
    topologicalKrullDim Z = (D + 1 : ℕ) := by
  have := h.finite
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 this
  have := CommonModel.isProper_of_isProjOver hq
  have := CommonModel.isProper_of_isProjOver h.isProjOver
  have := h.flat
  obtain ⟨a, ha, ha'⟩ := exists_trdeg_eq_and_dim_eq (p ≫ spMap (Int.castRingHom k))
  obtain ⟨b, hb, hb'⟩ := exists_trdeg_eq_and_dim_eq (q ≫ spMap (Int.castRingHom k))
  rw [← hη] at ha
  let := (g.residueFieldMap (genericPoint Z)).hom.toAlgebra
  have : Module.Finite (Y.residueField (g (genericPoint Z))) (Z.residueField (genericPoint Z)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hd)
  have : CharZero (Y.residueField (g (genericPoint Z))) :=
    hη ▸ charZero_residueField (p ≫ spMap (Int.castRingHom k))
  have e := trdeg_eq_of_isAlgebraic_top ℤ (Y.residueField (g (genericPoint Z)))
    (Z.residueField (genericPoint Z))
  obtain rfl : b = a := by exact_mod_cast hb.symm.trans (e.trans ha)
  rw [hb', ← ha', h.dim_eq]

end GlobalTheory.DimCover
