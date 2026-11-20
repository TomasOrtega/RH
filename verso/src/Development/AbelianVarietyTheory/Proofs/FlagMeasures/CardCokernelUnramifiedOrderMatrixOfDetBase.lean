import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramOrder

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Ideal in
/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Establish `hm : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`. Establish `hspan : Ideal.span {(u : R) * ϖ ^ n} = IsLocalRing.maximalIdeal R ^ n`. Rewrite using `[Ideal.span_singleton_mul_left_unit u.isUnit, hm, Ideal.span_singleton_pow]`.

Establish `hv : IsDiscreteValuationRing.addVal R ((u : R) * ϖ ^ n) = n`. Rewrite using `[IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit u]`. Simplify using the standard rewrite rules. Establish `hne : IsLocalRing.maximalIdeal R ≠ ⊥`. Rewrite using `[hm, Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `hϖ.ne_zero`. Rewrite using `[hv, hspan, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hne, Submodule.cardQuot_apply]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private lemma card_quotient_span_eq_card_residueField_pow_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a : R} (ha : a ≠ 0) :
    Nat.card (R ⧸ Ideal.span {a}) = Nat.card (IsLocalRing.ResidueField R) ^
      (IsDiscreteValuationRing.addVal R a).toNat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan : Ideal.span {(u : R) * ϖ ^ n} = IsLocalRing.maximalIdeal R ^ n := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, hm, Ideal.span_singleton_pow]
  have hv : IsDiscreteValuationRing.addVal R ((u : R) * ϖ ^ n) = n := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit u]
    simp
  have hne : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    rw [hm, Ne, Ideal.span_singleton_eq_bot]
    exact hϖ.ne_zero
  rw [hv, hspan, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hne, Submodule.cardQuot_apply]
  simp
  rfl

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Establish `hinj : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Assume the negation of the conclusion as `hx0`.

Apply `hf` to reduce the goal to its premises. Rewrite using `[← LinearMap.det_toMatrix b]`. Use `Matrix.exists_mulVec_eq_zero_iff.mp ⟨b.repr x, fun h => hx0 ?_, ?_⟩` and prove the remaining obligations. Establish `h' : b.repr x = 0`. Use extensionality with `i`.

Conclude with `congrFun h i`. Simplify using `using h'`. Rewrite using `[LinearMap.toMatrix_mulVec_repr, hx, map_zero]`. Both sides reduce to the same expression. Establish `hrank : Module.finrank R (LinearMap.range f) = Module.finrank R M` using `LinearMap.finrank_range_of_inj hinj`.

Set `T` to `Submodule.smithNormalFormTopBasis b hrank`. Set `B` to `Submodule.smithNormalFormBotBasis b hrank`. Set `a` to `Submodule.smithNormalFormCoeffs b hrank`. Set `e : M ≃ₗ[R] LinearMap.range f` to `T.equiv B (Equiv.refl _)`. Set `g : M →ₗ[R] M` to `(LinearMap.range f).subtype ∘ₗ e.toLinearMap`.

Establish `hgT : ∀ i, g (T i) = a i • T i`. Introduce `i`. Simplify using `[g, e, Module.Basis.equiv_apply, B, T, a, Submodule.smithNormalFormBotBasis_def]`. Establish `hdetg : LinearMap.det g = ∏ i, a i`. Rewrite using `[← LinearMap.det_toMatrix T]`.

Establish `hmat : LinearMap.toMatrix T T g = Matrix.diagonal a`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, hgT, map_smul, T.repr_self, Matrix.diagonal_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hij, Finsupp.single_apply, Ne.symm hij]`. Rewrite using `[hmat, Matrix.det_diagonal]`. Set `h : M →ₗ[R] M` to `e.symm.toLinearMap ∘ₗ f.rangeRestrict`. Establish `hfgh : f = g ∘ₗ h`.

Use extensionality with `x`. Simplify using `[g, h]`. Establish `hsurj : Function.Surjective h` using `e.symm.surjective.comp f.surjective_rangeRestrict`. Establish `hbij : Function.Bijective h` using `⟨OrzechProperty.injective_of_surjective_endomorphism h hsurj, hsurj⟩`. Establish `hdeth : IsUnit (LinearMap.det h)`.

Establish `h1` using `LinearEquiv.isUnit_det' (LinearEquiv.ofBijective h hbij)`. Establish `h2 : ((LinearEquiv.ofBijective h hbij : M ≃ₗ[R] M) : M →ₗ[R] M) = h` using `LinearMap.ext fun _ => rfl`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Establish `hdet : LinearMap.det f = (∏ i, a i) * LinearMap.det h`. Rewrite using `[hfgh, LinearMap.det_comp, hdetg]`.

Establish `ha : ∀ i, a i ≠ 0` using `Submodule.smithNormalFormCoeffs_ne_zero b hrank`. Establish `key : ∀ s : Finset (Module.Free.ChooseBasisIndex R M), (IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i)).toNat = ∑ i ∈ s, (IsDiscreteValuationRing.addVal R (a i)).toNat`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi, IsDiscreteValuationRing.addVal_mul, ENat.toNat_add, ih]`. Conclude with `IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (ha i)`. Conclude with `IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => ha j)`. Rewrite using `[Nat.card_congr (Submodule.quotientEquivPiSpan (LinearMap.range f) b hrank).toEquiv, Nat.card_pi]`.

Rewrite using `[Finset.prod_congr rfl fun i _ => card_quotient_span_eq_card_residueField_pow_addVal (Submodule.smithNormalFormCoeffs_ne_zero b hrank i)]`. Establish `hu : IsDiscreteValuationRing.addVal R (LinearMap.det h) = 0`. Establish `h3` using `IsDiscreteValuationRing.addVal_eq_zero_of_unit hdeth.unit`. Rewrite `h3` using `[IsUnit.unit_spec]`. Then use the resulting hypothesis. Rewrite using `[Finset.prod_pow_eq_pow_sum, hdet, IsDiscreteValuationRing.addVal_mul, hu, add_zero]`.

Conclude with `congrArg _ (key Finset.univ).symm`.
-/
theorem _root_.GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (f : M →ₗ[R] M) (hf : LinearMap.det f ≠ 0) :
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (IsLocalRing.ResidueField R) ^
      (IsDiscreteValuationRing.addVal R (LinearMap.det f)).toNat := by
  classical
  let b := Module.Free.chooseBasis R M
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    apply hf
    rw [← LinearMap.det_toMatrix b]
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨b.repr x, fun h => hx0 ?_, ?_⟩
    · have h' : b.repr x = 0 := by
        ext i
        exact congrFun h i
      simpa using h'
    · rw [LinearMap.toMatrix_mulVec_repr, hx, map_zero]
      rfl
  have hrank : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hinj
  let T := Submodule.smithNormalFormTopBasis b hrank
  let B := Submodule.smithNormalFormBotBasis b hrank
  let a := Submodule.smithNormalFormCoeffs b hrank
  let e : M ≃ₗ[R] LinearMap.range f := T.equiv B (Equiv.refl _)
  let g : M →ₗ[R] M := (LinearMap.range f).subtype ∘ₗ e.toLinearMap
  have hgT : ∀ i, g (T i) = a i • T i := by
    intro i
    simp [g, e, Module.Basis.equiv_apply, B, T, a, Submodule.smithNormalFormBotBasis_def]
  have hdetg : LinearMap.det g = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix T]
    have hmat : LinearMap.toMatrix T T g = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hgT, map_smul, T.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Finsupp.single_apply, Ne.symm hij]
    rw [hmat, Matrix.det_diagonal]
  let h : M →ₗ[R] M := e.symm.toLinearMap ∘ₗ f.rangeRestrict
  have hfgh : f = g ∘ₗ h := by
    ext x
    simp [g, h]
  have hsurj : Function.Surjective h := e.symm.surjective.comp f.surjective_rangeRestrict
  have hbij : Function.Bijective h :=
    ⟨OrzechProperty.injective_of_surjective_endomorphism h hsurj, hsurj⟩
  have hdeth : IsUnit (LinearMap.det h) := by
    have h1 := LinearEquiv.isUnit_det' (LinearEquiv.ofBijective h hbij)
    have h2 : ((LinearEquiv.ofBijective h hbij : M ≃ₗ[R] M) : M →ₗ[R] M) = h :=
      LinearMap.ext fun _ => rfl
    rwa [h2] at h1
  have hdet : LinearMap.det f = (∏ i, a i) * LinearMap.det h := by
    rw [hfgh, LinearMap.det_comp, hdetg]
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank
  have key : ∀ s : Finset (Module.Free.ChooseBasisIndex R M),
      (IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i)).toNat =
        ∑ i ∈ s, (IsDiscreteValuationRing.addVal R (a i)).toNat := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, IsDiscreteValuationRing.addVal_mul,
        ENat.toNat_add, ih]
      · exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (ha i)
      · exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr
          (Finset.prod_ne_zero_iff.mpr fun j _ => ha j)
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan (LinearMap.range f) b hrank).toEquiv,
    Nat.card_pi]
  rw [Finset.prod_congr rfl fun i _ =>
    card_quotient_span_eq_card_residueField_pow_addVal (Submodule.smithNormalFormCoeffs_ne_zero b hrank i)]
  have hu : IsDiscreteValuationRing.addVal R (LinearMap.det h) = 0 := by
    have h3 := IsDiscreteValuationRing.addVal_eq_zero_of_unit hdeth.unit
    rwa [IsUnit.unit_spec] at h3
  rw [Finset.prod_pow_eq_pow_sum, hdet, IsDiscreteValuationRing.addVal_mul, hu, add_zero]
  exact congrArg _ (key Finset.univ).symm

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ ι _ _ A j u hA`. Take `⟨-, hO, -, -, hmem, -⟩` from `_root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Set `φ : 𝒪[F] →+* L.O` to `{ toFun := fun r => ⟨algebraMap F E r, (hmem r).mpr r.2⟩ map_one' := by ext; simp map_mul' := by intro x y; ext; simp map_zero' := by ext; simp map_add' := by intro x y; ext; simp }`. Use `letI : Algebra 𝒪[F] L.O := φ.toAlgebra`. Establish `hφ : ∀ r : 𝒪[F], ((algebraMap 𝒪[F] L.O r : L.O) : E) = algebraMap F E r` using `fun r => rfl`.

Set `c : L.O →+* L.O` to `{ toFun := fun x => ⟨L.cj x, (hO x.1 x.2).1⟩ map_one' := by ext; simp map_mul' := by intro x y; ext; simp map_zero' := by ext; simp map_add' := by intro x y; ext; simp }`. Establish `hc : ∀ x : L.O, ((c x : L.O) : E) = L.cj x` using `fun x => rfl`. Take `⟨ω, hω, e, he, hωe⟩` from `_root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L`. Set `ω' : L.O` to `⟨ω, hω⟩`. Establish `hunit : IsUnit (ω' - c ω')` using `isUnit_iff_exists_inv.mpr ⟨⟨e, he⟩, Subtype.ext (by simpa [ω', hc] using hωe)⟩`.

Establish `hdecomp` using `_root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := 𝒪[F]) c (fun x => Subtype.ext (by simp [hc, L.cj_cj])) (fun r => Subtype.ext (by simp [hc, hφ])) (fun x hx => by`. Take `⟨r, hr⟩` from `_root_.GlobalTheory.UnramOrder.exists_int_of_fixed L x.2 (congrArg Subtype.val hx)`. Conclude with `⟨r, Subtype.ext (by rw [hφ, ← hr])⟩) hunit`. Establish `hinjO : Function.Injective (algebraMap 𝒪[F] L.O)`. Introduce `r s h`.

Establish `h'` using `congrArg Subtype.val h`. Rewrite `h'` using `[hφ, hφ]`. Conclude with `Subtype.ext (_root_.GlobalTheory.UnramOrder.algebraMap_inj L h')`. Establish `hli : LinearIndependent 𝒪[F] ![(1 : L.O), ω']`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Establish `hst'` using `congrArg c hst`. Rewrite `hst'` using `[map_add, map_mul, map_zero]`. Establish `hfix : ∀ r : 𝒪[F], c (algebraMap 𝒪[F] L.O r) = algebraMap 𝒪[F] L.O r` using `fun r => Subtype.ext (by simp [hc, hφ])`.

Rewrite `hst'` using `[hfix, hfix]`. Establish `ht0 : algebraMap 𝒪[F] L.O t * (ω' - c ω') = 0`. Rewrite using `[mul_sub]`. Take the linear combination `hst - hst'`. Establish `ht : t = 0` using `hinjO (by rw [map_zero]; exact (hunit.mul_left_eq_zero).mp ht0)`.

Use `⟨hinjO ?_, ht⟩` and prove the remaining obligations. Rewrite `hst` using `[ht, map_zero, zero_mul, add_zero]`. Rewrite using `[hst, map_zero]`. Establish `hspan : ⊤ ≤ Submodule.span 𝒪[F] (Set.range ![(1 : L.O), ω'])`. Introduce `x _`.

Take `⟨a, b, hx⟩` from `hdecomp x`. Establish `hx' : x = a • ![(1 : L.O), ω'] 0 + b • ![(1 : L.O), ω'] 1`. Simplify using `[hx, Algebra.smul_def]`. Rewrite using `[hx']`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))`.

Set `bO` to `Module.Basis.mk hli hspan`. Use `haveI : Module.Free 𝒪[F] L.O := Module.Free.of_basis bO`. Use `haveI : Module.Finite 𝒪[F] L.O := Module.Finite.of_basis bO`. Establish `hrank : Module.finrank 𝒪[F] L.O = 2`. Rewrite using `[Module.finrank_eq_card_basis bO, Fintype.card_fin]`.

Establish `hdetA : A.det = algebraMap 𝒪[F] L.O (ϖ ^ j * (u : 𝒪[F]))`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hA, hφ]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hdetf : LinearMap.det (A.mulVecLin.restrictScalars 𝒪[F]) = (ϖ ^ j * (u : 𝒪[F])) ^ 2`. Rewrite using `[LinearMap.det_restrictScalars]`. Express the relevant statement in the definitionally equal form `Algebra.norm 𝒪[F] (LinearMap.det (Matrix.toLin' A)) = _`. Rewrite using `[LinearMap.det_toLin', hdetA, Algebra.norm_algebraMap, hrank]`. Establish `hne : (ϖ ^ j * (u : 𝒪[F])) ^ 2 ≠ 0` using `pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) u.ne_zero)`.

Establish `h1` using `_root_.GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det (A.mulVecLin.restrictScalars 𝒪[F]) (by rw [hdetf]; exact hne)`. Rewrite `h1` using `[LinearMap.range_restrictScalars, Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv 𝒪[F] _).toEquiv]`. Rewrite using `[h1, hdetf, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit u, add_zero]`. Establish `hres : Nat.card (IsLocalRing.ResidueField 𝒪[F]) = _root_.GlobalTheory.HL.resQ ϖ`. Unfold `_root_.GlobalTheory.HL.resQ`.

Rewrite using `[← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]`. Both sides reduce to the same expression. Rewrite using `[hres]`. Use `congr 1`. Simplify using `[mul_comm]`.
-/
theorem _root_.GlobalTheory.UnramOrder.card_coker_of_det_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι L.O) (j : ℕ) (u : (𝒪[F])ˣ), ((A.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ j * ((u : 𝒪[F]) : F)) → Nat.card ((ι → L.O) ⧸ LinearMap.range A.mulVecLin) = _root_.GlobalTheory.HL.resQ ϖ ^ (2 * j) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ ι _ _ A j u hA
  obtain ⟨-, hO, -, -, hmem, -⟩ := _root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  let φ : 𝒪[F] →+* L.O :=
    { toFun := fun r => ⟨algebraMap F E r, (hmem r).mpr r.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  letI : Algebra 𝒪[F] L.O := φ.toAlgebra
  have hφ : ∀ r : 𝒪[F], ((algebraMap 𝒪[F] L.O r : L.O) : E) = algebraMap F E r := fun r => rfl
  let c : L.O →+* L.O :=
    { toFun := fun x => ⟨L.cj x, (hO x.1 x.2).1⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hc : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun x => rfl
  obtain ⟨ω, hω, e, he, hωe⟩ := _root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  let ω' : L.O := ⟨ω, hω⟩
  have hunit : IsUnit (ω' - c ω') :=
    isUnit_iff_exists_inv.mpr ⟨⟨e, he⟩, Subtype.ext (by simpa [ω', hc] using hωe)⟩
  have hdecomp := _root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := 𝒪[F]) c
    (fun x => Subtype.ext (by simp [hc, L.cj_cj]))
    (fun r => Subtype.ext (by simp [hc, hφ]))
    (fun x hx => by
      obtain ⟨r, hr⟩ := _root_.GlobalTheory.UnramOrder.exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
      exact ⟨r, Subtype.ext (by rw [hφ, ← hr])⟩) hunit
  have hinjO : Function.Injective (algebraMap 𝒪[F] L.O) := by
    intro r s h
    have h' := congrArg Subtype.val h
    rw [hφ, hφ] at h'
    exact Subtype.ext (_root_.GlobalTheory.UnramOrder.algebraMap_inj L h')
  have hli : LinearIndependent 𝒪[F] ![(1 : L.O), ω'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have hst' := congrArg c hst
    rw [map_add, map_mul, map_zero] at hst'
    have hfix : ∀ r : 𝒪[F], c (algebraMap 𝒪[F] L.O r) = algebraMap 𝒪[F] L.O r :=
      fun r => Subtype.ext (by simp [hc, hφ])
    rw [hfix, hfix] at hst'
    have ht0 : algebraMap 𝒪[F] L.O t * (ω' - c ω') = 0 := by
      rw [mul_sub]
      linear_combination hst - hst'
    have ht : t = 0 := hinjO (by rw [map_zero]; exact (hunit.mul_left_eq_zero).mp ht0)
    refine ⟨hinjO ?_, ht⟩
    rw [ht, map_zero, zero_mul, add_zero] at hst
    rw [hst, map_zero]
  have hspan : ⊤ ≤ Submodule.span 𝒪[F] (Set.range ![(1 : L.O), ω']) := by
    intro x _
    obtain ⟨a, b, hx⟩ := hdecomp x
    have hx' : x = a • ![(1 : L.O), ω'] 0 + b • ![(1 : L.O), ω'] 1 := by
      simp [hx, Algebra.smul_def]
    rw [hx']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let bO := Module.Basis.mk hli hspan
  haveI : Module.Free 𝒪[F] L.O := Module.Free.of_basis bO
  haveI : Module.Finite 𝒪[F] L.O := Module.Finite.of_basis bO
  have hrank : Module.finrank 𝒪[F] L.O = 2 := by
    rw [Module.finrank_eq_card_basis bO, Fintype.card_fin]
  have hdetA : A.det = algebraMap 𝒪[F] L.O (ϖ ^ j * (u : 𝒪[F])) := by
    apply Subtype.ext
    rw [hA, hφ]
    push_cast
    rfl
  have hdetf : LinearMap.det (A.mulVecLin.restrictScalars 𝒪[F]) =
      (ϖ ^ j * (u : 𝒪[F])) ^ 2 := by
    rw [LinearMap.det_restrictScalars]
    change Algebra.norm 𝒪[F] (LinearMap.det (Matrix.toLin' A)) = _
    rw [LinearMap.det_toLin', hdetA, Algebra.norm_algebraMap, hrank]
  have hne : (ϖ ^ j * (u : 𝒪[F])) ^ 2 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) u.ne_zero)
  have h1 := _root_.GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det (A.mulVecLin.restrictScalars 𝒪[F])
    (by rw [hdetf]; exact hne)
  rw [LinearMap.range_restrictScalars,
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv 𝒪[F] _).toEquiv] at h1
  rw [h1, hdetf, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit u, add_zero]
  have hres : Nat.card (IsLocalRing.ResidueField 𝒪[F]) = _root_.GlobalTheory.HL.resQ ϖ := by
    unfold _root_.GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    rfl
  rw [hres]
  congr 1
  simp [mul_comm]

end GlobalTheory.UnramOrder
