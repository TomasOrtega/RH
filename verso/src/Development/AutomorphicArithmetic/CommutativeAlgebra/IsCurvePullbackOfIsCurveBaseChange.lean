import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

/- English proof (translation)
Use `letI : Field (R ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Algebra.FiniteType k (R ⧸ m) := inferInstance`. Use `haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)`. Use `haveI : Algebra.IsIntegral k (R ⧸ m) := inferInstance`. Set `e : k ≃ₐ[k] (R ⧸ m)` to `AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral`.

Use `⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `h0 : e.symm (Ideal.Quotient.mk m r) = 0` using `hr`. Conclude with `(map_eq_zero_iff e.symm e.symm.injective).mp h0`.
-/
private theorem exists_point {k R : Type} [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal] :
    ∃ φ : R →ₐ[k] k, ∀ r, φ r = 0 → r ∈ m := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) := inferInstance
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := inferInstance
  let e : k ≃ₐ[k] (R ⧸ m) :=
    AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : e.symm (Ideal.Quotient.mk m r) = 0 := hr
  exact (map_eq_zero_iff e.symm e.symm.injective).mp h0

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨⟨i0, hi0, ha⟩, ⟨j0, hj0, hb⟩⟩` from `hcon`. Use `haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)`. Establish `hab : a i0 * b j0 ≠ 0` using `mul_ne_zero ha hb`.

Establish `hjac : (⊥ : Ideal R).jacobson = ⊥` using `IsJacobsonRing.out inferInstance Ideal.isRadical_bot_of_noZeroDivisors`. Establish `hnot : a i0 * b j0 ∉ (⊥ : Ideal R).jacobson`. Rewrite using `[hjac]`. Simplify using `using hab`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm, hnm⟩ : ∃ m : Ideal R, m.IsMaximal ∧ a i0 * b j0 ∉ m := by`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `hnot` to reduce the goal to its premises. Rewrite using `[Ideal.jacobson, Submodule.mem_sInf]`. Introduce and unpack `J ⟨-, hJ⟩`.

Conclude with `hne J hJ`. Use `haveI := hm`. Take `⟨φ, hφ⟩` from `exists_point (k := k) m`. Establish `hφa : φ (a i0) ≠ 0` using `fun h0 => hnm (m.mul_mem_right _ (hφ _ h0))`. Establish `hφb : φ (b j0) ≠ 0` using `fun h0 => hnm (m.mul_mem_left _ (hφ _ h0))`.

Set `ψ : R ⊗[k] A →ₐ[k] A` to `Algebra.TensorProduct.lift ((Algebra.ofId k A).comp φ) (AlgHom.id k A) (fun _ _ => Commute.all _ _)`. Establish `hψ : ∀ (c : ι → R) (u : Finset ι), ψ (∑ i ∈ u, c i ⊗ₜ[k] e i) = ∑ i ∈ u, φ (c i) • e i`. Introduce `c u`. Simplify using `[ψ, map_sum, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]`. Establish `h2` using `congrArg ψ h`.

Rewrite `h2` using `[map_mul, hψ, hψ, map_zero]`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `hφa ((linearIndependent_iff'.mp e.linearIndependent) s (fun i => φ (a i)) h3 i0 hi0)`. Conclude with `hφb ((linearIndependent_iff'.mp e.linearIndependent) t (fun j => φ (b j)) h3 j0 hj0)`.
-/
private theorem dom_fg {k R A ι : Type} [Field k] [IsAlgClosed k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing A] [IsDomain A] [Algebra k A] (e : Module.Basis ι k A)
    (s t : Finset ι) (a b : ι → R)
    (h : (∑ i ∈ s, a i ⊗ₜ[k] e i) * (∑ j ∈ t, b j ⊗ₜ[k] e j) = 0) :
    (∀ i ∈ s, a i = 0) ∨ (∀ j ∈ t, b j = 0) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨i0, hi0, ha⟩, ⟨j0, hj0, hb⟩⟩ := hcon
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hab : a i0 * b j0 ≠ 0 := mul_ne_zero ha hb
  have hjac : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance Ideal.isRadical_bot_of_noZeroDivisors
  have hnot : a i0 * b j0 ∉ (⊥ : Ideal R).jacobson := by
    rw [hjac]
    simpa using hab
  obtain ⟨m, hm, hnm⟩ : ∃ m : Ideal R, m.IsMaximal ∧ a i0 * b j0 ∉ m := by
    by_contra hne
    push_neg at hne
    apply hnot
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro J ⟨-, hJ⟩
    exact hne J hJ
  haveI := hm
  obtain ⟨φ, hφ⟩ := exists_point (k := k) m
  have hφa : φ (a i0) ≠ 0 := fun h0 => hnm (m.mul_mem_right _ (hφ _ h0))
  have hφb : φ (b j0) ≠ 0 := fun h0 => hnm (m.mul_mem_left _ (hφ _ h0))
  let ψ : R ⊗[k] A →ₐ[k] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId k A).comp φ) (AlgHom.id k A) (fun _ _ => Commute.all _ _)
  have hψ : ∀ (c : ι → R) (u : Finset ι),
      ψ (∑ i ∈ u, c i ⊗ₜ[k] e i) = ∑ i ∈ u, φ (c i) • e i := by
    intro c u
    simp [ψ, map_sum, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  have h2 := congrArg ψ h
  rw [map_mul, hψ, hψ, map_zero] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hφa ((linearIndependent_iff'.mp e.linearIndependent) s (fun i => φ (a i)) h3 i0 hi0)
  · exact hφb ((linearIndependent_iff'.mp e.linearIndependent) t (fun j => φ (b j)) h3 j0 hj0)

/- English proof (translation)
Set `e` to `Module.Basis.ofVectorSpace k K`. Use `haveI : Nontrivial (L ⊗[k] K) := inferInstance`. It suffices to establish `hnz : NoZeroDivisors (L ⊗[k] K) from NoZeroDivisors.to_isDomain _`. Use `⟨fun {x y} hxy => ?_⟩` and prove the remaining obligations. Set `E` to `TensorProduct.equivFinsuppOfBasisRight (M := L) e`.

Establish `hrep : ∀ z : L ⊗[k] K, z = ∑ i ∈ (E z).support, (E z) i ⊗ₜ[k] e i`. Introduce `z`. Use `conv_lhs => rw [← E.symm_apply_apply z]`. Rewrite using `[TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum]`. Set `S : Finset L` to `(E x).support.image (E x) ∪ (E y).support.image (E y)`.

Set `R` to `Algebra.adjoin k (S : Set L)`. Use `haveI : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp (Subalgebra.fg_adjoin_finset S)`. Establish `hmem : ∀ (z : L ⊗[k] K), (z = x ∨ z = y) → ∀ i, (E z) i ∈ R`. Introduce and unpack `z hz i`. Distinguish the cases in `hi : i ∈ (E z).support`.

Apply `Algebra.subset_adjoin` to reduce the goal to its premises. Break down `hz with rfl | rfl` into its components or cases. Conclude with `Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)`. Conclude with `Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)`. Rewrite using `[Finsupp.notMem_support_iff.mp hi]`.

Conclude with `R.zero_mem`. Set `a : Module.Basis.ofVectorSpaceIndex k K → R` to `fun i => ⟨(E x) i, hmem x (Or.inl rfl) i⟩`. Set `b : Module.Basis.ofVectorSpaceIndex k K → R` to `fun i => ⟨(E y) i, hmem y (Or.inr rfl) i⟩`. Set `j : R ⊗[k] K →ₐ[k] L ⊗[k] K` to `Algebra.TensorProduct.map R.val (AlgHom.id k K)`. Establish `hj : Function.Injective j`.

Use `Module.Flat.rTensor_preserves_injective_linearMap (M := K) R.val.toLinearMap Subtype.val_injective` as an intermediate fact. Conclude with `this`. Establish `hja : j (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) = x`. Rewrite using `[map_sum]`. Use `conv_rhs => rw [hrep x]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[j, a]`. Establish `hjb : j (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = y`. Rewrite using `[map_sum]`. Use `conv_rhs => rw [hrep y]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[j, b]`. Establish `hprod : (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) * (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = 0`. Apply `hj` to reduce the goal to its premises. Rewrite using `[map_mul, hja, hjb, hxy, map_zero]`.

Break down `dom_fg (k := k) e _ _ a b hprod with h0 | h0` into its components or cases. Use `left`. Rewrite using `[hrep x]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Use `congrArg Subtype.val (h0 i hi)` as an intermediate fact.

Simplify using `only [a, ZeroMemClass.coe_zero] at this`. Rewrite using `[this, TensorProduct.zero_tmul]`. Use `right`. Rewrite using `[hrep y]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations.

Use `congrArg Subtype.val (h0 i hi)` as an intermediate fact. Simplify using `only [b, ZeroMemClass.coe_zero] at this`. Rewrite using `[this, TensorProduct.zero_tmul]`.
-/
private theorem dom_tensor (k K L : Type) [Field k] [IsAlgClosed k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] : IsDomain (L ⊗[k] K) := by
  classical
  let e := Module.Basis.ofVectorSpace k K
  haveI : Nontrivial (L ⊗[k] K) := inferInstance
  suffices hnz : NoZeroDivisors (L ⊗[k] K) from NoZeroDivisors.to_isDomain _
  refine ⟨fun {x y} hxy => ?_⟩
  let E := TensorProduct.equivFinsuppOfBasisRight (M := L) e
  have hrep : ∀ z : L ⊗[k] K, z = ∑ i ∈ (E z).support, (E z) i ⊗ₜ[k] e i := by
    intro z
    conv_lhs => rw [← E.symm_apply_apply z]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum]
  let S : Finset L := (E x).support.image (E x) ∪ (E y).support.image (E y)
  let R := Algebra.adjoin k (S : Set L)
  haveI : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp (Subalgebra.fg_adjoin_finset S)
  have hmem : ∀ (z : L ⊗[k] K), (z = x ∨ z = y) → ∀ i, (E z) i ∈ R := by
    rintro z hz i
    by_cases hi : i ∈ (E z).support
    · apply Algebra.subset_adjoin
      rcases hz with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact R.zero_mem
  let a : Module.Basis.ofVectorSpaceIndex k K → R := fun i => ⟨(E x) i, hmem x (Or.inl rfl) i⟩
  let b : Module.Basis.ofVectorSpaceIndex k K → R := fun i => ⟨(E y) i, hmem y (Or.inr rfl) i⟩
  let j : R ⊗[k] K →ₐ[k] L ⊗[k] K := Algebra.TensorProduct.map R.val (AlgHom.id k K)
  have hj : Function.Injective j := by
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := K) R.val.toLinearMap Subtype.val_injective
    exact this
  have hja : j (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) = x := by
    rw [map_sum]
    conv_rhs => rw [hrep x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [j, a]
  have hjb : j (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = y := by
    rw [map_sum]
    conv_rhs => rw [hrep y]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [j, b]
  have hprod : (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) * (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = 0 := by
    apply hj
    rw [map_mul, hja, hjb, hxy, map_zero]
  rcases dom_fg (k := k) e _ _ a b hprod with h0 | h0
  · left
    rw [hrep x]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := congrArg Subtype.val (h0 i hi)
    simp only [a, ZeroMemClass.coe_zero] at this
    rw [this, TensorProduct.zero_tmul]
  · right
    rw [hrep y]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := congrArg Subtype.val (h0 i hi)
    simp only [b, ZeroMemClass.coe_zero] at this
    rw [this, TensorProduct.zero_tmul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[geometrically_iff_of_commRing]`. Introduce `K _ _ Y fst snd h`. Use `haveI := dom_tensor k K L`. Set `e : Y ≅ Spec (CommRingCat.of (L ⊗[k] K))` to `h.isoPullback ≪≫ pullbackSpecIso k L K`.

Use `haveI : Nonempty Y := ⟨e.inv (Nonempty.some inferInstance)⟩`. Conclude with `isIntegral_of_isOpenImmersion e.hom`.
-/
private theorem gi (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  haveI := dom_tensor k K L
  let e : Y ≅ Spec (CommRingCat.of (L ⊗[k] K)) := h.isoPullback ≪≫ pullbackSpecIso k L K
  haveI : Nonempty Y := ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

/- English proof (translation)
Introduce `k L _ _ _ _ C c hc`. Take `⟨h1, h2, h3⟩` from `hc`. Use `haveI := gi k L`. Use `set g := Spec.map (CommRingCat.ofHom (algebraMap k L)) with hg`. Use `set p := pullback.fst c g with hp`.

Use `haveI : GeometricallyIrreducible p := inferInstance`. Use `haveI : GeometricallyReduced p := inferInstance`. Use `haveI : Flat p := inferInstance`. Use `haveI : Finite (irreducibleComponents C) := by`. Rewrite using `[irreducibleComponents_eq_singleton]`.

Use `infer_instance`. Use `haveI hred : IsReduced (pullback c g) := GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents p`. Establish `hgen : GeneralizingMap p` using `Flat.generalizingMap p`. Use `set η := genericPoint C`. Set `ξ : ↥(pullback c g)` to `p.fiberι η (genericPoint (p.fiber η))`.

Establish `hall : ∀ q : ↥(pullback c g), ξ ⤳ q`. Introduce `q`. Establish `h0 : η ⤳ p q` using `genericPoint_specializes _`. Take `⟨q', hq', hpq'⟩` from `hgen h0`. Establish `hmem : q' ∈ Set.range (p.fiberι η)`.

Rewrite using `[p.range_fiberι]`. Conclude with `hpq'`. Take `⟨r, rfl⟩` from `hmem`. Conclude with `((genericPoint_specializes r).map (p.fiberι η).continuous).trans hq'`. Use `haveI hirr : IrreducibleSpace ↥(pullback c g) := by`.

Rewrite using `[irreducibleSpace_def]`. Establish `hcl : closure ({ξ} : Set ↥(pullback c g)) = Set.univ` using `Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)`. Rewrite using `[Set.top_eq_univ, ← hcl]`. Conclude with `isIrreducible_singleton.closure`. Use `haveI := isSmoothOfRelativeDimension_isStableUnderBaseChange 1`.

Use `⟨isIntegral_of_irreducibleSpace_of_isReduced _, inferInstance, ?_⟩` and prove the remaining obligations. Conclude with `MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) (IsPullback.of_hasPullback c g) h3`.
-/
theorem UpperTheory.isCurve_pullback_of_isCurve_baseChange :
    ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] {C : Scheme.{0}} (c : C ⟶ Sp k), IsCurve c → IsCurve (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  intro k L _ _ _ _ C c hc
  obtain ⟨h1, h2, h3⟩ := hc
  haveI := gi k L
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L)) with hg
  set p := pullback.fst c g with hp
  haveI : GeometricallyIrreducible p := inferInstance
  haveI : GeometricallyReduced p := inferInstance
  haveI : Flat p := inferInstance
  haveI : Finite (irreducibleComponents C) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  haveI hred : IsReduced (pullback c g) :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents p
  have hgen : GeneralizingMap p := Flat.generalizingMap p
  set η := genericPoint C
  let ξ : ↥(pullback c g) := p.fiberι η (genericPoint (p.fiber η))
  have hall : ∀ q : ↥(pullback c g), ξ ⤳ q := by
    intro q
    have h0 : η ⤳ p q := genericPoint_specializes _
    obtain ⟨q', hq', hpq'⟩ := hgen h0
    have hmem : q' ∈ Set.range (p.fiberι η) := by
      rw [p.range_fiberι]
      exact hpq'
    obtain ⟨r, rfl⟩ := hmem
    exact ((genericPoint_specializes r).map (p.fiberι η).continuous).trans hq'
  haveI hirr : IrreducibleSpace ↥(pullback c g) := by
    rw [irreducibleSpace_def]
    have hcl : closure ({ξ} : Set ↥(pullback c g)) = Set.univ :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI := isSmoothOfRelativeDimension_isStableUnderBaseChange 1
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, inferInstance, ?_⟩
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) (IsPullback.of_hasPullback c g) h3
