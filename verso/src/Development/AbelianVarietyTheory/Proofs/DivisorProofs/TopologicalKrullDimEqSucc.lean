import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfAffineOpens
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped TensorProduct

namespace GlobalTheory.RegGenSmooth

/- English proof (translation)
Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Use `Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]`. Conclude with `RingHom.injective_int _`.
-/
theorem injective_of_charZero {k A : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    [CommRing A] [CharZero A] (f : k →+* A) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

/- English proof (translation)
Establish `: Algebra.FinitePresentation K B` using `Algebra.FinitePresentation.of_finiteType.mp ‹_›`. Establish `key (m : Ideal B) (hm : m.IsMaximal) : ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away f)`. Take `⟨h₁, h₂⟩` from `h m`. Establish `h₃` using `formallySmooth_of_isRegularLocalRing_of_perfectField K (Localization.AtPrime m)`. Use `formallyEtale_residueField_of_isMaximal K K m (Localization.AtPrime m)` as an intermediate fact.

Take `⟨-, h₄⟩` from `free_and_finrank_kaehler_eq_finrank_cotangentSpace K (Localization.AtPrime m)`. Establish `h₅` using `(IsRegularLocalRing.iff_finrank_cotangentSpace (Localization.AtPrime m)).1 h₁`. Rewrite `h₅` using `[h₂, ← h₄]`. Establish `: Algebra.IsSmoothAt K m` using `h₃`. Conclude with `exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt K m (by exact_mod_cast h₅)`.

Use `(HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_` and prove the remaining obligations. Use `⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away f)}, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ h`. Take `⟨f, hf, hs⟩` from `key m hm`.

Conclude with `hf (hle (Ideal.subset_span hs))`. Introduce `f hf`. Use `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf` as an intermediate fact. Rewrite `this` using `[IsScalarTower.algebraMap_eq K B]`. Then use the resulting hypothesis.
-/
theorem smooth_of_regular (K : Type) [Field K] [PerfectField K] (B : Type) [CommRing B]
    [Algebra K B] [Algebra.FiniteType K B] (d : ℕ)
    (h : ∀ (m : Ideal B) [m.IsMaximal], IsRegularLocalRing (Localization.AtPrime m) ∧
      ringKrullDim (Localization.AtPrime m) = d) :
    SmoothOfRelativeDimension d (spMap (algebraMap K B)) := by
  have : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal B) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away f) := by
    obtain ⟨h₁, h₂⟩ := h m
    have h₃ := formallySmooth_of_isRegularLocalRing_of_perfectField K (Localization.AtPrime m)
    have := formallyEtale_residueField_of_isMaximal K K m (Localization.AtPrime m)
    obtain ⟨-, h₄⟩ := free_and_finrank_kaehler_eq_finrank_cotangentSpace K (Localization.AtPrime m)
    have h₅ := (IsRegularLocalRing.iff_finrank_cotangentSpace (Localization.AtPrime m)).1 h₁
    rw [h₂, ← h₄] at h₅
    have : Algebra.IsSmoothAt K m := h₃
    exact exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt K m (by exact_mod_cast h₅)
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away f)}, ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := key m hm
    exact hf (hle (Ideal.subset_span hs))
  · intro f hf
    have := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf
    rwa [IsScalarTower.algebraMap_eq K B] at this

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

/- English proof (translation)
Use `h.isDomain` as an intermediate fact. Use `h.finite` as an intermediate fact. Use `h.charZero_base` as an intermediate fact. Rewrite using `[ringKrullDim_eq_of_isIntegral ℤ k]`. Conclude with `IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField`.
-/
theorem ringKrullDim_base (h : IsArithVar p D) : ringKrullDim k = 1 := by
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  rw [ringKrullDim_eq_of_isIntegral ℤ k]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

/- English proof (translation)
Use `h.isDomain` as an intermediate fact. Use `h.finite` as an intermediate fact. Use `h.isIntegral` as an intermediate fact. Use `h.flat` as an intermediate fact. Establish `: IsProper p` using `CommonModel.isProper_of_isProjOver h.isProjOver`.

Establish `: IsIntegral (Spec (.of A))` using `isIntegral_of_isOpenImmersion i`. Establish `: IsDomain A` using `(affine_isIntegral_iff (.of A)).1 this`. Establish `hft : LocallyOfFiniteType (spMap (algebraMap k A))` using `by rw [← hi]; infer_instance`. Rewrite `hft` using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`. Establish `hfl : Flat (i ≫ p ≫ spMap (Int.castRingHom k))` using `inferInstance`.

Establish `h₁` using `(flat_int_iff_charZero _).1 hfl`. Establish `: CharZero A` using `(Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.toRingHom.charZero_iff (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.injective |>.1 h₁`. Conclude with `⟨‹_›, RingHom.finiteType_algebraMap.mp hft, (faithfulSMul_iff_algebraMap_injective _ _).2 (injective_of_charZero _)⟩`.
-/
theorem chart_props (h : IsArithVar p D) {A : Type} [CommRing A] [Algebra k A] (i : Sp A ⟶ X)
    [IsOpenImmersion i] (hi : i ≫ p = spMap (algebraMap k A)) [Nontrivial A] :
    IsDomain A ∧ Algebra.FiniteType k A ∧ FaithfulSMul k A := by
  have := h.isDomain
  have := h.finite
  have := h.isIntegral
  have := h.flat
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion i
  have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
  have hft : LocallyOfFiniteType (spMap (algebraMap k A)) := by rw [← hi]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have hfl : Flat (i ≫ p ≫ spMap (Int.castRingHom k)) := inferInstance
  have h₁ := (flat_int_iff_charZero _).1 hfl
  have : CharZero A := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.toRingHom.charZero_iff
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.injective |>.1 h₁
  exact ⟨‹_›, RingHom.finiteType_algebraMap.mp hft,
    (faithfulSMul_iff_algebraMap_injective _ _).2 (injective_of_charZero _)⟩

/- English proof (translation)
Use `h.isDomain` as an intermediate fact. Use `h.isNoetherianRing` as an intermediate fact. Establish `: IsProper p` using `CommonModel.isProper_of_isProjOver h.isProjOver`. Establish `hO1` using `ringKrullDim_base h`. Establish `hO : ¬ IsField k` using `fun e => by`.

Rewrite `hO1` using `[ringKrullDim_eq_zero_of_isField e]`. Conclude with `absurd hO1 (by decide)`. Use `le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_` and prove the remaining obligations. Take `⟨A, _, _, i, _, a, rfl, hi⟩` from `exists_affine_chart_over p x`. Take `⟨i₀, _, -⟩` from `exists_affine_chart_of_isPullback H i hi`.

Use `⟨Set.range i, i.isOpenEmbedding.isOpen_range, ⟨a, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[topologicalKrullDim_eq_of_isEmbedding i.isOpenEmbedding.isEmbedding rfl]`. Establish `: Nontrivial A` using `PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩`. Take `⟨_, _, _⟩` from `chart_props h i hi`. Establish `h₁ : ringKrullDim (K ⊗[k] A) ≤ d` using `(PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).ge.trans (i₀.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hd.le)`.

Use `(PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).le.trans ((IntModel.ringKrullDim_le_add (O := k) K).trans ?_)` and prove the remaining obligations. Use `(add_le_add hO1.le h₁).trans_eq ?_` and prove the remaining obligations. Use `push_cast`. Conclude with `add_comm _ _`. Use `IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)` as an intermediate fact.

Establish `: IsPreimmersion j` using `MorphismProperty.of_isPullback H.flip this`. Establish `hj` using `j.isEmbedding`. Establish `eX : topologicalKrullDim X = Order.krullDim X` using `Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))`. Establish `eY : topologicalKrullDim Y = Order.krullDim Y` using `Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))`. Rewrite `hd` using `[eY]`.

Rewrite using `[eX]`. Take `⟨l, hl⟩` from `Order.le_krullDim_iff.1 hd.ge`. Establish `hm : StrictMono (j : Y → X)` using `fun a b h => ⟨hj.isInducing.specializes_iff.2 h.1, fun h' => h.2 (hj.isInducing.specializes_iff.1 h')⟩`. Take `⟨m, hm0, hmp⟩` from `Ring.not_isField_iff_exists_prime.1 hO`. Establish `hp (y : Y) : (p (j y)).asIdeal = ⊥`.

Rewrite using `[← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]`. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap k K) (q y).asIdeal = ⊥`. Rewrite using `[(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective k K)`. Establish `hs : p (j l.head) ⤳ (⟨m, hmp⟩ : PrimeSpectrum k)` using `(PrimeSpectrum.le_iff_specializes _ _).1 ((hp _).le.trans bot_le)`.

Take `⟨x, hx, hxm⟩` from `p.isClosedMap.specializingMap hs`. Establish `hlt : x < (l.map _ hm).head`. Use `⟨hx, fun h' => hm0 ?_⟩` and prove the remaining obligations. Establish `h₁ : p x ⤳ p (j l.head)` using `Specializes.map h' p.continuous`. Rewrite `h₁` using `[hxm]`.

Establish `h₂ : m ≤ (p (j l.head)).asIdeal` using `(PrimeSpectrum.le_iff_specializes _ _).2 h₁`. Conclude with `le_bot_iff.1 (h₂.trans (hp _).le)`. Use `Order.le_krullDim_iff.2 ⟨(l.map _ hm).cons x hlt, ?_⟩` and prove the remaining obligations. Simplify using `[hl]`.
-/
theorem topologicalKrullDim_eq_succ (h : IsArithVar p D) {K : Type} [Field K] [Algebra k K]
    [IsFractionRing k K] {Y : Scheme.{0}} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap k K))) {d : ℕ} (hd : topologicalKrullDim Y = d) :
    topologicalKrullDim X = (d + 1 : ℕ) := by
  have := h.isDomain
  have := h.isNoetherianRing
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have hO1 := ringKrullDim_base h
  have hO : ¬ IsField k := fun e => by
    rw [ringKrullDim_eq_zero_of_isField e] at hO1
    exact absurd hO1 (by decide)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨A, _, _, i, _, a, rfl, hi⟩ := exists_affine_chart_over p x
    obtain ⟨i₀, _, -⟩ := exists_affine_chart_of_isPullback H i hi
    refine ⟨Set.range i, i.isOpenEmbedding.isOpen_range, ⟨a, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding i.isOpenEmbedding.isEmbedding rfl]
    have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
    obtain ⟨_, _, _⟩ := chart_props h i hi
    have h₁ : ringKrullDim (K ⊗[k] A) ≤ d :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).ge.trans
        (i₀.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hd.le)
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).le.trans
      ((IntModel.ringKrullDim_le_add (O := k) K).trans ?_)
    refine (add_le_add hO1.le h₁).trans_eq ?_
    push_cast
    exact add_comm _ _
  · have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
    have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
    have hj := j.isEmbedding
    have eX : topologicalKrullDim X = Order.krullDim X :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    have eY : topologicalKrullDim Y = Order.krullDim Y :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
    rw [eY] at hd
    rw [eX]
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hd.ge
    have hm : StrictMono (j : Y → X) := fun a b h =>
      ⟨hj.isInducing.specializes_iff.2 h.1, fun h' => h.2 (hj.isInducing.specializes_iff.1 h')⟩
    obtain ⟨m, hm0, hmp⟩ := Ring.not_isField_iff_exists_prime.1 hO
    have hp (y : Y) : (p (j y)).asIdeal = ⊥ := by
      rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
      change Ideal.comap (algebraMap k K) (q y).asIdeal = ⊥
      rw [(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective k K)
    have hs : p (j l.head) ⤳ (⟨m, hmp⟩ : PrimeSpectrum k) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 ((hp _).le.trans bot_le)
    obtain ⟨x, hx, hxm⟩ := p.isClosedMap.specializingMap hs
    have hlt : x < (l.map _ hm).head := by
      refine ⟨hx, fun h' => hm0 ?_⟩
      have h₁ : p x ⤳ p (j l.head) := Specializes.map h' p.continuous
      rw [hxm] at h₁
      have h₂ : m ≤ (p (j l.head)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
      exact le_bot_iff.1 (h₂.trans (hp _).le)
    refine Order.le_krullDim_iff.2 ⟨(l.map _ hm).cons x hlt, ?_⟩
    simp [hl]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

/- English proof (translation)
Use `h.isDomain` as an intermediate fact. Use `h.isIntegral` as an intermediate fact. Establish `: IsProper p` using `CommonModel.isProper_of_isProjOver h.isProjOver`. Take `⟨_, _, _⟩` from `chart_props h i hi`. Use `IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)` as an intermediate fact.

Establish `hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A` using `Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero (by simpa using nonZeroDivisors.ne_zero hx)`. Establish `: IsDomain (K ⊗[k] A)` using `IsLocalization.isDomain_of_le_nonZeroDivisors _ hle`. Establish `hinj : Function.Injective (algebraMap A (K ⊗[k] A))` using `IsLocalization.injective _ hle`. Use `⟨this, ?_⟩` and prove the remaining obligations. Take `⟨i₀, _, H₀⟩` from `exists_affine_chart_of_isPullback H i hi`.

Take `⟨d, hd, -⟩` from `exists_ringKrullDim_eq_and_trdeg_eq K (K ⊗[k] A)`. Establish `: LocallyOfFiniteType q` using `MorphismProperty.of_isPullback H inferInstance`. Use `IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)` as an intermediate fact. Establish `: IsPreimmersion j` using `MorphismProperty.of_isPullback H.flip this`. Set `η : Spec (.of (K ⊗[k] A))` to `(⟨⊥, inferInstance⟩ : PrimeSpectrum _)`.

Establish `e₁ : topologicalKrullDim (closure {i₀ η} : Set Y) = d` using `(topologicalKrullDim_closure_eq_ringKrullDim_quotient q i₀ η).trans ((ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).trans hd)`. Establish `e₂ : j (i₀ η) = genericPoint X`. Rewrite using `[← Scheme.Hom.comp_apply, H₀.w, Scheme.Hom.comp_apply, ← genericPoint_eq_of_isOpenImmersion i]`. Use `congr 1`. Rewrite using `[genericPoint_eq_bot_of_affine]`.

Conclude with `PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hinj)`. Establish `e₃ : closure {i₀ η} = Set.univ` using `Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1 (j.isEmbedding.isInducing.specializes_iff.1 (e₂ ▸ genericPoint_specializes _))`. Rewrite `e₁` using `[e₃, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq]`. Establish `e₄` using `(topologicalKrullDim_eq_succ h H e₁).symm.trans h.dim_eq`. Rewrite using `[hd]`.

Establish `e₅ : d + 1 = D + 1` using `by exact_mod_cast e₄`. Rewrite using `[Nat.succ_injective e₅]`.
-/
theorem ringKrullDim_chart (h : IsArithVar p D) {K : Type} [Field K] [Algebra k K]
    [IsFractionRing k K] {Y : Scheme.{0}} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap k K))) {A : Type} [CommRing A] [Algebra k A]
    (i : Sp A ⟶ X) [IsOpenImmersion i] (hi : i ≫ p = spMap (algebraMap k A)) [Nontrivial A] :
    IsDomain (K ⊗[k] A) ∧ ringKrullDim (K ⊗[k] A) = D := by
  have := h.isDomain
  have := h.isIntegral
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  obtain ⟨_, _, _⟩ := chart_props h i hi
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : IsDomain (K ⊗[k] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hinj : Function.Injective (algebraMap A (K ⊗[k] A)) := IsLocalization.injective _ hle
  refine ⟨this, ?_⟩
  obtain ⟨i₀, _, H₀⟩ := exists_affine_chart_of_isPullback H i hi
  obtain ⟨d, hd, -⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (K ⊗[k] A)
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback H inferInstance
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
  let η : Spec (.of (K ⊗[k] A)) := (⟨⊥, inferInstance⟩ : PrimeSpectrum _)
  have e₁ : topologicalKrullDim (closure {i₀ η} : Set Y) = d :=
    (topologicalKrullDim_closure_eq_ringKrullDim_quotient q i₀ η).trans
      ((ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).trans hd)
  have e₂ : j (i₀ η) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, H₀.w, Scheme.Hom.comp_apply, ← genericPoint_eq_of_isOpenImmersion i]
    congr 1
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hinj)
  have e₃ : closure {i₀ η} = Set.univ :=
    Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1
      (j.isEmbedding.isInducing.specializes_iff.1 (e₂ ▸ genericPoint_specializes _))
  rw [e₃, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq] at e₁
  have e₄ := (topologicalKrullDim_eq_succ h H e₁).symm.trans h.dim_eq
  rw [hd]
  have e₅ : d + 1 = D + 1 := by exact_mod_cast e₄
  rw [Nat.succ_injective e₅]

/- English proof (translation)
Use `h.isDomain` as an intermediate fact. Use `h.charZero_base` as an intermediate fact. Establish `H` using `IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))`. Use `smoothOfRelativeDimension_genericFibre_of_affine k X p D fun A _ _ i _ hi => ?_` and prove the remaining obligations. Establish `: IsProper p` using `CommonModel.isProper_of_isProjOver h.isProjOver`.

Establish `hft : LocallyOfFiniteType (spMap (algebraMap k A))` using `by rw [← hi]; infer_instance`. Rewrite `hft` using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`. Establish `: Algebra.FiniteType k A` using `RingHom.finiteType_algebraMap.mp hft`. Use `smooth_of_regular _ _ D fun m hm => ⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨i₀, _, -⟩` from `exists_affine_chart_of_isPullback H i hi`.

Establish `: Flat (spMap (algebraMap k (FractionRing k)))` using `flat_specMap_localization (nonZeroDivisors k) _`. Establish `: IsPreimmersion (spMap (algebraMap k (FractionRing k)))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors k)`. Set `y : Spec (.of (FractionRing k ⊗[k] A))` to `(⟨m, inferInstance⟩ : PrimeSpectrum _)`. Use `GenSpread.isIso_stalkMap_of_flat (pullback.fst p (spMap (algebraMap k (FractionRing k)))) (i₀ y)` as an intermediate fact. Use `hr (pullback.fst p (spMap (algebraMap k (FractionRing k))) (i₀ y))` as an intermediate fact.

Conclude with `IsRegularLocalRing.of_ringEquiv (asIso ((pullback.fst p (spMap (algebraMap k (FractionRing k)))).stalkMap (i₀ y)) ≪≫ asIso (i₀.stalkMap y) ≪≫ Spec.stalkIso (.of _) y).commRingCatIsoToRingEquiv`. Establish `: Nontrivial (FractionRing k ⊗[k] A)` using `Ideal.Quotient.nontrivial_iff.2 hm.ne_top |> fun _ => (Ideal.Quotient.mk m).domain_nontrivial`. Establish `: Nontrivial A`. Assume the negation of the conclusion as `hA`. Rewrite `hA` using `[not_nontrivial_iff_subsingleton]`.

Conclude with `false_of_nontrivial_of_subsingleton (FractionRing k ⊗[k] A)`. Take `⟨_, hd⟩` from `ringKrullDim_chart h H i hi`. Establish `e` using `height_add_ringKrullDim_quotient_of_finiteType (FractionRing k) m`. Rewrite `e` using `[hd, ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hm), add_zero]`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), e]`.
-/
theorem smooth_genericFibre (h : IsArithVar p D) (hr : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)) :
    SmoothOfRelativeDimension D (pullback.snd p (spMap (algebraMap k (FractionRing k)))) := by
  have := h.isDomain
  have := h.charZero_base
  have H := IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))
  refine smoothOfRelativeDimension_genericFibre_of_affine k X p D fun A _ _ i _ hi => ?_
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have hft : LocallyOfFiniteType (spMap (algebraMap k A)) := by rw [← hi]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType k A := RingHom.finiteType_algebraMap.mp hft
  refine smooth_of_regular _ _ D fun m hm => ⟨?_, ?_⟩
  · obtain ⟨i₀, _, -⟩ := exists_affine_chart_of_isPullback H i hi
    have : Flat (spMap (algebraMap k (FractionRing k))) :=
      flat_specMap_localization (nonZeroDivisors k) _
    have : IsPreimmersion (spMap (algebraMap k (FractionRing k))) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors k)
    let y : Spec (.of (FractionRing k ⊗[k] A)) := (⟨m, inferInstance⟩ : PrimeSpectrum _)
    have := GenSpread.isIso_stalkMap_of_flat
      (pullback.fst p (spMap (algebraMap k (FractionRing k)))) (i₀ y)
    have := hr (pullback.fst p (spMap (algebraMap k (FractionRing k))) (i₀ y))
    exact IsRegularLocalRing.of_ringEquiv
      (asIso ((pullback.fst p (spMap (algebraMap k (FractionRing k)))).stalkMap (i₀ y)) ≪≫
        asIso (i₀.stalkMap y) ≪≫ Spec.stalkIso (.of _) y).commRingCatIsoToRingEquiv
  · have : Nontrivial (FractionRing k ⊗[k] A) := Ideal.Quotient.nontrivial_iff.2 hm.ne_top |>
      fun _ => (Ideal.Quotient.mk m).domain_nontrivial
    have : Nontrivial A := by
      by_contra hA
      rw [not_nontrivial_iff_subsingleton] at hA
      exact false_of_nontrivial_of_subsingleton (FractionRing k ⊗[k] A)
    obtain ⟨_, hd⟩ := ringKrullDim_chart h H i hi
    have e := height_add_ringKrullDim_quotient_of_finiteType (FractionRing k) m
    rw [hd, ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hm),
      add_zero] at e
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), e]

/- English proof (translation)
Use `h.isDomain` as an intermediate fact. Use `h.finite` as an intermediate fact. Use `h.isNoetherianRing` as an intermediate fact. Establish `: IsProper p` using `CommonModel.isProper_of_isProjOver h.isProjOver`. Establish `: LocallyOfFinitePresentation p` using `inferInstance`.

Use `smooth_genericFibre h hr` as an intermediate fact. Establish `H` using `IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))`. Establish `: Flat (spMap (algebraMap k (FractionRing k)))` using `flat_specMap_localization (nonZeroDivisors k) _`. Establish `: IsPreimmersion (spMap (algebraMap k (FractionRing k)))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors k)`. Take `⟨τ, hτ⟩ : ∃ τ : FractionRing k →+* ℂ, τ.comp (algebraMap k _) = σ` from `⟨IsFractionRing.lift (K := FractionRing k) (injective_of_charZero σ), RingHom.ext fun a => by`.

Rewrite using `[RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩`. Establish `hτ' : spMap τ ≫ spMap (algebraMap k _) = spMap σ`. Rewrite using `[← hτ, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨y', hy'⟩ : ∃ y' : Sp ℂ ⟶ pullback p (spMap (algebraMap k (FractionRing k))), y' ≫ pullback.fst _ _ = y.1` from `⟨H.lift y.1 (spMap τ) (y.2.trans hτ'.symm), H.lift_fst _ _ _⟩`.

Take `⟨W, hW, hs⟩` from `GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback H D (y' (IsLocalRing.closedPoint ℂ))`. Use `⟨W, mem_ptsIn.2 ?_, hs⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y.1 (IsLocalRing.closedPoint ℂ) ∈ W`. Rewrite using `[← hy']`. Conclude with `hW`.
-/
theorem exists_opens_smooth (h : IsArithVar p D) (hr : ∀ x, IsRegularLocalRing (X.presheaf.stalk x))
    (σ : k →+* ℂ) (y : CxPts p σ) :
    ∃ U : X.Opens, y ∈ ptsIn p σ U ∧ SmoothOfRelativeDimension D (U.ι ≫ p) := by
  have := h.isDomain
  have := h.finite
  have := h.isNoetherianRing
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have : LocallyOfFinitePresentation p := inferInstance
  have := smooth_genericFibre h hr
  have H := IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))
  have : Flat (spMap (algebraMap k (FractionRing k))) :=
    flat_specMap_localization (nonZeroDivisors k) _
  have : IsPreimmersion (spMap (algebraMap k (FractionRing k))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors k)
  obtain ⟨τ, hτ⟩ : ∃ τ : FractionRing k →+* ℂ, τ.comp (algebraMap k _) = σ :=
    ⟨IsFractionRing.lift (K := FractionRing k) (injective_of_charZero σ), RingHom.ext fun a => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  have hτ' : spMap τ ≫ spMap (algebraMap k _) = spMap σ := by
    rw [← hτ, ← Spec.map_comp]
    rfl
  obtain ⟨y', hy'⟩ : ∃ y' : Sp ℂ ⟶ pullback p (spMap (algebraMap k (FractionRing k))),
      y' ≫ pullback.fst _ _ = y.1 :=
    ⟨H.lift y.1 (spMap τ) (y.2.trans hτ'.symm), H.lift_fst _ _ _⟩
  obtain ⟨W, hW, hs⟩ := GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback H D
    (y' (IsLocalRing.closedPoint ℂ))
  refine ⟨W, mem_ptsIn.2 ?_, hs⟩
  change y.1 (IsLocalRing.closedPoint ℂ) ∈ W
  rw [← hy']
  exact hW

/- English proof (translation)
Introduce `σ` and use `by refine ⟨⟨AlgChart p σ D, id, fun y => ?_⟩⟩ obtain ⟨W, hW, _⟩ := exists_opens_smooth h hr σ y obtain ⟨U, x, hU, hz, hx⟩ := ModelCharts.exists_etale_coords_of_opens p D W (mem_ptsIn.1 hW) obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx (mem_ptsIn.2 hz) exact ⟨c, hc⟩`.
-/
theorem genSmooth (h : IsArithVar p D) (hr : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)) :
    GenSmooth p D := fun σ => by
  refine ⟨⟨AlgChart p σ D, id, fun y => ?_⟩⟩
  obtain ⟨W, hW, _⟩ := exists_opens_smooth h hr σ y
  obtain ⟨U, x, hU, hz, hx⟩ := ModelCharts.exists_etale_coords_of_opens p D W (mem_ptsIn.1 hW)
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx (mem_ptsIn.2 hz)
  exact ⟨c, hc⟩

/- English proof (translation)
Introduce `_ _ _ _ h` and use `⟨genSmooth h.toIsArithVar h.regular, exists_opens_smooth h.toIsArithVar h.regular⟩`.
-/
theorem genSmooth_of_isRegSurf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k),
    IsRegSurf p → GenSmooth p 1 ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      ∃ U : X.Opens, y ∈ ptsIn p σ U ∧ SmoothOfRelativeDimension 1 (U.ι ≫ p) :=
  fun _ _ _ _ h => ⟨genSmooth h.toIsArithVar h.regular,
    exists_opens_smooth h.toIsArithVar h.regular⟩

end GlobalTheory.RegGenSmooth
