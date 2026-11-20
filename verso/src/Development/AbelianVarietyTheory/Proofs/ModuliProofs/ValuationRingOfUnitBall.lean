import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReductionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.GoodRedUnitBall

/- English proof (translation)
Establish `h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s)` using `Algebra.FiniteType.adjoin_of_finite hs`. Rewrite using `[RingHom.finiteType_algebraMap]`. Establish `e : (Algebra.adjoin ℤ s).toSubring = Subring.closure s`. Rewrite using `[Algebra.adjoin_int]`. Both sides reduce to the same expression.

Use `Algebra.FiniteType.of_surjective (R := ℤ) (A := Algebra.adjoin ℤ s) (RingEquiv.subringCongr e).toRingHom.toIntAlgHom (RingEquiv.subringCongr e).surjective` and prove the remaining obligations.
-/
theorem finiteType_closure (s : Set ℂ) (hs : s.Finite) :
    (algebraMap ℤ (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) := Algebra.FiniteType.adjoin_of_finite hs
  rw [RingHom.finiteType_algebraMap]
  have e : (Algebra.adjoin ℤ s).toSubring = Subring.closure s := by
    rw [Algebra.adjoin_int]; rfl
  refine Algebra.FiniteType.of_surjective (R := ℤ) (A := Algebra.adjoin ℤ s)
    (RingEquiv.subringCongr e).toRingHom.toIntAlgHom (RingEquiv.subringCongr e).surjective

/- English proof (translation)
Establish `hd : IsDomain V` using `h.1.isDomain _`. Use `⟨hd, ?_⟩` and prove the remaining obligations. Establish `key : ∀ x : C, IsLocalization.IsInteger V x ∨ IsLocalization.IsInteger V x⁻¹`. Introduce `x`. Break down `le_total ‖x‖ 1 with hx | hx` into its components or cases.

Conclude with `Or.inl ((h.2 x).2 hx)`. Conclude with `Or.inr ((h.2 x⁻¹).2 (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx))`. Establish `: FaithfulSMul V C` using `(faithfulSMul_iff_algebraMap_injective V C).2 h.1`. Establish `hf : IsFractionRing V C`. Use `IsFractionRing.of_field V C fun x => ?_` and prove the remaining obligations.

Break down `key x with ⟨a, ha⟩ | ⟨a, ha⟩` into its components or cases. Conclude with `⟨a, 1, by simp [ha]⟩`. Conclude with `⟨1, a, by simp [ha]⟩`. Conclude with `⟨(ValuationRing.iff_isInteger_or_isInteger V C).2 key, hf⟩`.
-/
theorem valuationRing_of_unitBall {V C : Type} [CommRing V] [NormedField C] [Algebra V C] (h : IsUnitBall V C) :
    ∃ _ : IsDomain V, ValuationRing V ∧ IsFractionRing V C := by
  have hd : IsDomain V := h.1.isDomain _
  refine ⟨hd, ?_⟩
  have key : ∀ x : C, IsLocalization.IsInteger V x ∨ IsLocalization.IsInteger V x⁻¹ := by
    intro x
    rcases le_total ‖x‖ 1 with hx | hx
    · exact Or.inl ((h.2 x).2 hx)
    · exact Or.inr ((h.2 x⁻¹).2 (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx))
  have : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 h.1
  have hf : IsFractionRing V C := by
    refine IsFractionRing.of_field V C fun x => ?_
    rcases key x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, 1, by simp [ha]⟩
    · exact ⟨1, a, by simp [ha]⟩
  exact ⟨(ValuationRing.iff_isInteger_or_isInteger V C).2 key, hf⟩

/- English proof (translation)
Introduce `hext E _ _ _ H D Xo n N T l₀ B l c O _ β Y hR V C _ _ _ _ hV b y hy ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, hab, _, _, h₁, h₂, _⟩`. Take `⟨_, _, _⟩` from `valuationRing_of_unitBall hV`. Take `⟨b₀, r, ν, -, -, ⟨ab⟩⟩` from `hR`. Establish `hp : IsProper Y.s` using `projProper _ _ _ Y.proj`. Establish `hp' : IsProper B.C.s` using `projProper _ _ _ B.C.proj`.

Establish `hE : ValuativeCriterion.Existence Y.s` using `(UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Y.s) : (ValuativeCriterion.Existence ⊓ @QuasiCompact) Y.s).1`. Take `⟨⟨q⟩⟩` from `hE { R := V K := C i₁ := y ≫ Y.j i₂ := spMap b commSq := ⟨by rw [Category.assoc]; exact hy⟩ }`. Take `⟨y', hs, hl⟩ : ∃ y' : Sp V ⟶ Y.X, y' ≫ Y.s = spMap b ∧ spMap (algebraMap V C) ≫ y' = y ≫ Y.j` from `⟨q.l, q.fac_right, q.fac_left⟩`. Take `⟨π, hπ⟩ : ∃ π : Y.X ⟶ B.C.X, π = ab.π` from `⟨_, rfl⟩`. Use `⟨y', hs, hl, ?_⟩` and prove the remaining obligations.

Establish `hz : LocallyOfFiniteType (spMap (algebraMap ℤ (RZ H (n * l₀.M) 1)))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`. Conclude with `finiteType_closure _ (Set.toFinite _)`. Establish `hc : IsGrpPullback Y.t.G B.C.t.G π ab.mu.φ` using `hπ ▸ ab.mu.cart`. Establish `h₃` using `(h₂.comp Y.m.cart).comp hc`.

Establish `h₄ : IsGrpPullback A B.C.t.G (spMap (algebraMap V C) ≫ (y' ≫ π)) ((φ₂ ≫ Y.m.φ) ≫ ab.mu.φ)`. Rewrite using `[← Category.assoc, hl]`. Conclude with `h₃`. Establish `h₅` using `GlobalTheory.T.range_subset_abelianLocus_of_goodReduction hext B.C.X (B.C.s ≫ spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) B.C.t.G V C (y' ≫ π) 𝒜 A φ₁ _ inferInstance B.C.t.semi hab h₁ h₄`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `(abLocus_pullback abLocusOne B.C.t.semi hc.1 _).1 (h₅ ⟨x, rfl⟩)`.
-/
theorem goodRedExt_unitBall : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), Raises B Y → ∀ (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra V C], IsUnitBall V C → Y.GoodRedExt V C := by
  intro hext E _ _ _ H D Xo n N T l₀ B l c O _ β Y hR V C _ _ _ _ hV b y hy ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, hab, _, _, h₁, h₂, _⟩
  obtain ⟨_, _, _⟩ := valuationRing_of_unitBall hV
  obtain ⟨b₀, r, ν, -, -, ⟨ab⟩⟩ := hR
  have hp : IsProper Y.s := projProper _ _ _ Y.proj
  have hp' : IsProper B.C.s := projProper _ _ _ B.C.proj
  have hE : ValuativeCriterion.Existence Y.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Y.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) Y.s).1
  obtain ⟨⟨q⟩⟩ := hE
    { R := V
      K := C
      i₁ := y ≫ Y.j
      i₂ := spMap b
      commSq := ⟨by rw [Category.assoc]; exact hy⟩ }
  obtain ⟨y', hs, hl⟩ : ∃ y' : Sp V ⟶ Y.X, y' ≫ Y.s = spMap b ∧ spMap (algebraMap V C) ≫ y' = y ≫ Y.j :=
    ⟨q.l, q.fac_right, q.fac_left⟩
  obtain ⟨π, hπ⟩ : ∃ π : Y.X ⟶ B.C.X, π = ab.π := ⟨_, rfl⟩
  refine ⟨y', hs, hl, ?_⟩
  have hz : LocallyOfFiniteType (spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact finiteType_closure _ (Set.toFinite _)
  have hc : IsGrpPullback Y.t.G B.C.t.G π ab.mu.φ := hπ ▸ ab.mu.cart
  have h₃ := (h₂.comp Y.m.cart).comp hc
  have h₄ : IsGrpPullback A B.C.t.G (spMap (algebraMap V C) ≫ (y' ≫ π)) ((φ₂ ≫ Y.m.φ) ≫ ab.mu.φ) := by
    rw [← Category.assoc, hl]
    exact h₃
  have h₅ := GlobalTheory.T.range_subset_abelianLocus_of_goodReduction hext B.C.X (B.C.s ≫ spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) B.C.t.G V C (y' ≫ π) 𝒜 A φ₁ _
    inferInstance B.C.t.semi hab h₁ h₄
  rintro _ ⟨x, rfl⟩
  exact (abLocus_pullback abLocusOne B.C.t.semi hc.1 _).1 (h₅ ⟨x, rfl⟩)

end GlobalTheory.GoodRedUnitBall
