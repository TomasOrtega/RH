import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory
namespace DegKer

/- English proof (translation)
Set `F` to `FractionRing R`. Set `E` to `FractionRing S`. Use `letI : Algebra F E := FractionRing.liftAlgebra R E`. Use `letI : Algebra F Ω := FractionRing.liftAlgebra R Ω`. Use `haveI : IsScalarTower R F E := FractionRing.isScalarTower_liftAlgebra R E`.

Use `haveI : IsScalarTower R F Ω := FractionRing.isScalarTower_liftAlgebra R Ω`. Use `haveI : FiniteDimensional F E := inferInstance`. Use `haveI : ExpChar F p := expChar_of_injective_algebraMap (IsFractionRing.injective R F) p`. Take `⟨e, he⟩` from `finInsepDegree_eq_pow F E p`. Establish `hc : Nat.card (E →ₐ[F] Ω) = Nat.card (S →ₐ[R] Ω)`.

Use `Nat.card_congr (Equiv.ofBijective (fun σ => (σ.restrictScalars R).comp (IsScalarTower.toAlgHom R S E)) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `σ τ h`. Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises. Conclude with `IsFractionRing.ringHom_ext (A := S) fun x => DFunLike.congr_fun h x`. Introduce `g`.

Establish `hg : Function.Injective g`. Rewrite using `[injective_iff_map_eq_zero]`. Establish `: RingHom.ker g = ⊥`. Use `Ideal.eq_bot_of_comap_eq_bot (R := R) (eq_bot_iff.mpr fun x hx => ?_)` and prove the remaining obligations. Establish `hx' : g (algebraMap R S x) = 0` using `hx`.

Rewrite `hx'` using `[AlgHom.commutes]`. Conclude with `(FaithfulSMul.algebraMap_injective R Ω) (by simpa using hx')`. Introduce `a ha`. Establish `: a ∈ RingHom.ker g` using `ha`. Simplify the hypotheses and the goal together.

Set `σ : E →ₐ[R] Ω` to `IsFractionRing.liftAlgHom hg`. Use `⟨{ σ.toRingHom with commutes' := fun x => ?_ }, ?_⟩` and prove the remaining obligations. Establish `: σ.toRingHom.comp (algebraMap F E) = algebraMap F Ω` using `IsFractionRing.ringHom_ext (A := R) fun x => by`. Simplify using `[← IsScalarTower.algebraMap_apply]`. Conclude with `DFunLike.congr_fun this x`.

Use extensionality with `x`. Simplify using `[σ]`. Rewrite using `[← hc, ← Field.finSepDegree_eq_of_isAlgClosed F E Ω]`. Use `⟨NeZero.ne _, e, ?_⟩` and prove the remaining obligations. Rewrite using `[← he, mul_comm, Field.finSepDegree_mul_finInsepDegree, Algebra.IsAlgebraic.finrank_of_isFractionRing R F S E]`.
-/
theorem finrank_eq_pow_mul_card (R S Ω : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    [FaithfulSMul R Ω] (p : ℕ) [ExpChar R p] :
    Nat.card (S →ₐ[R] Ω) ≠ 0 ∧ ∃ e : ℕ, Module.finrank R S = p ^ e * Nat.card (S →ₐ[R] Ω) := by
  let F := FractionRing R
  let E := FractionRing S
  letI : Algebra F E := FractionRing.liftAlgebra R E
  letI : Algebra F Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R F E := FractionRing.isScalarTower_liftAlgebra R E
  haveI : IsScalarTower R F Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  haveI : FiniteDimensional F E := inferInstance
  haveI : ExpChar F p := expChar_of_injective_algebraMap (IsFractionRing.injective R F) p
  obtain ⟨e, he⟩ := finInsepDegree_eq_pow F E p
  have hc : Nat.card (E →ₐ[F] Ω) = Nat.card (S →ₐ[R] Ω) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun σ => (σ.restrictScalars R).comp (IsScalarTower.toAlgHom R S E)) ⟨?_, ?_⟩)
    · intro σ τ h
      apply AlgHom.coe_ringHom_injective
      exact IsFractionRing.ringHom_ext (A := S) fun x => DFunLike.congr_fun h x
    · intro g
      have hg : Function.Injective g := by
        rw [injective_iff_map_eq_zero]
        have : RingHom.ker g = ⊥ := by
          refine Ideal.eq_bot_of_comap_eq_bot (R := R) (eq_bot_iff.mpr fun x hx => ?_)
          have hx' : g (algebraMap R S x) = 0 := hx
          rw [AlgHom.commutes] at hx'
          exact (FaithfulSMul.algebraMap_injective R Ω) (by simpa using hx')
        intro a ha
        have : a ∈ RingHom.ker g := ha
        simp_all
      let σ : E →ₐ[R] Ω := IsFractionRing.liftAlgHom hg
      refine ⟨{ σ.toRingHom with commutes' := fun x => ?_ }, ?_⟩
      · have : σ.toRingHom.comp (algebraMap F E) = algebraMap F Ω :=
          IsFractionRing.ringHom_ext (A := R) fun x => by
            simp [← IsScalarTower.algebraMap_apply]
        exact DFunLike.congr_fun this x
      · ext x
        simp [σ]
  rw [← hc, ← Field.finSepDegree_eq_of_isAlgClosed F E Ω]
  refine ⟨NeZero.ne _, e, ?_⟩
  rw [← he, mul_comm, Field.finSepDegree_mul_finInsepDegree,
    Algebra.IsAlgebraic.finrank_of_isFractionRing R F S E]

/- English proof (translation)
Use `letI := (f.app U).hom.toAlgebra`. Establish `hV : IsAffineOpen (f ⁻¹ᵁ U)` using `hU.preimage f`. Establish `w : hV.fromSpec ≫ f = Spec.map (f.app U) ≫ hU.fromSpec`. Rewrite using `[← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl, Scheme.Hom.app_eq_appLE]`. Establish `H` using `IsOpenImmersion.isPullback (Spec.map (f.app U)) hV.fromSpec hU.fromSpec f w (by simp)`.

Use `Nat.card_congr (Equiv.ofBijective (fun σ => ⟨Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ hV.fromSpec, ?_⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[Category.assoc, w, ← Category.assoc, ← Spec.map_comp]`. Use `congr 2`. Use extensionality with `x`. Conclude with `σ.commutes x`.

Introduce `σ τ h`. Establish `h1` using `Spec.map_injective ((cancel_mono _).mp (congrArg Subtype.val h))`. Conclude with `AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h1)`. Introduce and unpack `⟨y, hy⟩`. Take `⟨g, hg⟩` from `Spec.map_surjective (H.lift _ _ hy.symm)`.

Establish `h1 : f.app U ≫ g = CommRingCat.ofHom (algebraMap Γ(Y, U) Ω)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hg, H.lift_fst]`. Use `⟨{ g.hom with commutes' := fun x => ?_ }, Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h1) x`.

Express the relevant statement in the definitionally equal form `Spec.map g ≫ _ = y`. Rewrite using `[hg, H.lift_snd]`.
-/
theorem card_fibre_eq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffineHom f] {U : Y.Opens}
    (hU : IsAffineOpen U) (Ω : Type) [CommRing Ω] [Algebra Γ(Y, U) Ω] :
    letI := (f.app U).hom.toAlgebra
    Nat.card (Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Ω) = Nat.card {y : Spec (CommRingCat.of Ω) ⟶ X //
      y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) Ω)) ≫ hU.fromSpec} := by
  letI := (f.app U).hom.toAlgebra
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have w : hV.fromSpec ≫ f = Spec.map (f.app U) ≫ hU.fromSpec := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl, Scheme.Hom.app_eq_appLE]
  have H := IsOpenImmersion.isPullback (Spec.map (f.app U)) hV.fromSpec hU.fromSpec f w (by simp)
  refine Nat.card_congr (Equiv.ofBijective
    (fun σ => ⟨Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ hV.fromSpec, ?_⟩) ⟨?_, ?_⟩)
  · rw [Category.assoc, w, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact σ.commutes x
  · intro σ τ h
    have h1 := Spec.map_injective ((cancel_mono _).mp (congrArg Subtype.val h))
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h1)
  · rintro ⟨y, hy⟩
    obtain ⟨g, hg⟩ := Spec.map_surjective (H.lift _ _ hy.symm)
    have h1 : f.app U ≫ g = CommRingCat.ofHom (algebraMap Γ(Y, U) Ω) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, H.lift_fst]
    refine ⟨{ g.hom with commutes' := fun x => ?_ }, Subtype.ext ?_⟩
    · exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h1) x
    · change Spec.map g ≫ _ = y
      rw [hg, H.lift_snd]

/- English proof (translation)
Establish `h` using `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X y`. Establish `h2 : (X.fromSpecResidueField _ ≫ q) ≫ pointOfClosedPoint q _ hy = X.fromSpecResidueField (y (IsLocalRing.closedPoint Ω))`. Rewrite using `[pointOfClosedPoint, ← SpecMap_residueFieldIsoBase_inv q _ hy, ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]`. Use `conv_lhs => enter [1, 1]`. Rewrite using `[← h]`.

Rewrite using `[Category.assoc, Category.assoc, ← Category.assoc (X.fromSpecResidueField _), h2, h]`.
-/
theorem exists_descent {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] (Ω : Type) [Field Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ X) (hy : IsClosed {y (IsLocalRing.closedPoint Ω)}) :
    (y ≫ q) ≫ pointOfClosedPoint q _ hy = y := by
  have h := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X y
  have h2 : (X.fromSpecResidueField _ ≫ q) ≫ pointOfClosedPoint q _ hy =
      X.fromSpecResidueField (y (IsLocalRing.closedPoint Ω)) := by
    rw [pointOfClosedPoint, ← SpecMap_residueFieldIsoBase_inv q _ hy, ← Spec.map_comp_assoc,
      Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  conv_lhs => enter [1, 1]; rw [← h]
  rw [Category.assoc, Category.assoc, ← Category.assoc (X.fromSpecResidueField _), h2, h]

/- English proof (translation)
Set `t : Over.mk s ⟶ Out.baseOver (Sp K)` to `Over.homMk s (Category.comp_id _)`. Establish `hinj : ∀ x x' : Out.baseOver (Sp K) ⟶ A, t ≫ x = t ≫ x' → x = x'`. Introduce `x x' h`. Use `ext1`. Use `ext_of_apply_closedPoint_eq A.hom (Over.w x) (Over.w x') ?_` and prove the remaining obligations.

Establish `h1 : x.left (s (IsLocalRing.closedPoint Ω)) = x'.left (s (IsLocalRing.closedPoint Ω))` using `congr(($h).left (IsLocalRing.closedPoint Ω))`. Rewrite `h1` using `[Subsingleton.elim (s (IsLocalRing.closedPoint Ω)) (IsLocalRing.closedPoint K)]`. Then use the resulting hypothesis. Use `Nat.card_congr (Equiv.ofBijective (fun x => ⟨t ≫ x.1, by rw [Category.assoc, x.2, comp_one]⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `x x' h`. Conclude with `Subtype.ext (hinj _ _ (congrArg Subtype.val h))`.

Introduce and unpack `⟨y, hy⟩`. Set `o : Out.baseOver (Sp K) ⟶ A` to `1`. Establish `ho : IsClosed {o.left (IsLocalRing.closedPoint K)}` using `((pointEquivClosedPoint A.hom) ⟨o.left, Over.w o⟩).2`. Establish `h1 : y ≫ α = t ≫ o` using `by rw [hy, comp_one]`. Establish `h2 : α.left (y.left (IsLocalRing.closedPoint Ω)) = o.left (IsLocalRing.closedPoint K)`.

Establish `h3 : α.left (y.left (IsLocalRing.closedPoint Ω)) = o.left (s (IsLocalRing.closedPoint Ω))` using `congr(($h1).left (IsLocalRing.closedPoint Ω))`. Rewrite `h3` using `[Subsingleton.elim (s (IsLocalRing.closedPoint Ω)) (IsLocalRing.closedPoint K)]`. Then use the resulting hypothesis. Establish `hc : IsClosed {y.left (IsLocalRing.closedPoint Ω)}` using `isClosed_of_subset_discrete_closed (Set.singleton_subset_iff.mpr h2) (α.left.isDiscrete_preimage_singleton (o.left (IsLocalRing.closedPoint K))) (ho.preimage α.left.continuous)`. Set `x : Out.baseOver (Sp K) ⟶ A` to `Over.homMk (pointOfClosedPoint A.hom _ hc) (pointOfClosedPoint_comp A.hom _ hc)`. Establish `hx : t ≫ x = y` using `by ext1`.

Establish `h4` using `exists_descent A.hom Ω y.left hc`. Rewrite `h4` using `[Over.w y]`. Conclude with `h4`. Use `⟨⟨x, hinj _ _ ?_⟩, Subtype.ext hx⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hx, hy, comp_one]`.
-/
theorem card_ker_eq {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A]
    [LocallyOfFiniteType A.hom] (α : A ⟶ A) [IsMonHom α] [IsFinite α.left] (Ω : Type) [Field Ω]
    (s : Sp Ω ⟶ Sp K) :
    Nat.card {x : Out.baseOver (Sp K) ⟶ A // x ≫ α = 1} =
      Nat.card {y : Over.mk s ⟶ A // y ≫ α = 1} := by
  let t : Over.mk s ⟶ Out.baseOver (Sp K) := Over.homMk s (Category.comp_id _)
  have hinj : ∀ x x' : Out.baseOver (Sp K) ⟶ A, t ≫ x = t ≫ x' → x = x' := by
    intro x x' h
    ext1
    refine ext_of_apply_closedPoint_eq A.hom (Over.w x) (Over.w x') ?_
    have h1 : x.left (s (IsLocalRing.closedPoint Ω)) = x'.left (s (IsLocalRing.closedPoint Ω)) :=
      congr(($h).left (IsLocalRing.closedPoint Ω))
    rwa [Subsingleton.elim (s (IsLocalRing.closedPoint Ω)) (IsLocalRing.closedPoint K)] at h1
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨t ≫ x.1, by rw [Category.assoc, x.2, comp_one]⟩) ⟨?_, ?_⟩)
  · intro x x' h
    exact Subtype.ext (hinj _ _ (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    let o : Out.baseOver (Sp K) ⟶ A := 1
    have ho : IsClosed {o.left (IsLocalRing.closedPoint K)} :=
      ((pointEquivClosedPoint A.hom) ⟨o.left, Over.w o⟩).2
    have h1 : y ≫ α = t ≫ o := by rw [hy, comp_one]
    have h2 : α.left (y.left (IsLocalRing.closedPoint Ω)) = o.left (IsLocalRing.closedPoint K) := by
      have h3 : α.left (y.left (IsLocalRing.closedPoint Ω)) =
          o.left (s (IsLocalRing.closedPoint Ω)) := congr(($h1).left (IsLocalRing.closedPoint Ω))
      rwa [Subsingleton.elim (s (IsLocalRing.closedPoint Ω)) (IsLocalRing.closedPoint K)] at h3
    have hc : IsClosed {y.left (IsLocalRing.closedPoint Ω)} :=
      isClosed_of_subset_discrete_closed (Set.singleton_subset_iff.mpr h2)
        (α.left.isDiscrete_preimage_singleton (o.left (IsLocalRing.closedPoint K)))
        (ho.preimage α.left.continuous)
    let x : Out.baseOver (Sp K) ⟶ A :=
      Over.homMk (pointOfClosedPoint A.hom _ hc) (pointOfClosedPoint_comp A.hom _ hc)
    have hx : t ≫ x = y := by
      ext1
      have h4 := exists_descent A.hom Ω y.left hc
      rw [Over.w y] at h4
      exact h4
    refine ⟨⟨x, hinj _ _ ?_⟩, Subtype.ext hx⟩
    rw [← Category.assoc, hx, hy, comp_one]

/- English proof (translation)
Take `⟨⟨y₀, rfl⟩⟩` from `h`. Use `Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft y₀) fun y => ?_)` and prove the remaining obligations. Simplify using `[MonObj.mul_comp]`.
-/
theorem card_coset_eq {S : Scheme.{0}} (A T : Over S) [GrpObj A] (α : A ⟶ A) [IsMonHom α]
    (z : T ⟶ A) (h : Nonempty {y : T ⟶ A // y ≫ α = z}) :
    Nat.card {y : T ⟶ A // y ≫ α = 1} = Nat.card {y : T ⟶ A // y ≫ α = z} := by
  obtain ⟨⟨y₀, rfl⟩⟩ := h
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft y₀) fun y => ?_)
  simp [MonObj.mul_comp]

/- English proof (translation)
Use `letI : Algebra R S' := ((algebraMap S S').comp (algebraMap R S)).toAlgebra`. Use `haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' h.symm`. Establish `hle : Submonoid.powers f ≤ nonZeroDivisors R` using `powers_le_nonZeroDivisors_of_noZeroDivisors hf`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) S' := by`.

Rewrite using `[Algebra.algebraMapSubmonoid_powers]`. Use `infer_instance`. Use `haveI : IsLocalizedModule (Submonoid.powers f) (IsScalarTower.toAlgHom R S S').toLinearMap := (isLocalizedModule_iff_isLocalization).mpr this`. Rewrite using `[IsLocalization.finrank_eq R' (Submonoid.powers f) hle, IsLocalizedModule.finrank_eq (Submonoid.powers f) (IsScalarTower.toAlgHom R S S').toLinearMap hle]`.
-/
theorem finrank_away {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsDomain R] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] (f : R) (hf : f ≠ 0)
    [IsLocalization.Away f R'] [IsLocalization.Away (algebraMap R S f) S']
    (h : (algebraMap R' S').comp (algebraMap R R') = (algebraMap S S').comp (algebraMap R S)) :
    Module.finrank R' S' = Module.finrank R S := by
  letI : Algebra R S' := ((algebraMap S S').comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' h.symm
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) S' := by
    rw [Algebra.algebraMapSubmonoid_powers]; infer_instance
  haveI : IsLocalizedModule (Submonoid.powers f) (IsScalarTower.toAlgHom R S S').toLinearMap :=
    (isLocalizedModule_iff_isLocalization).mpr this
  rw [IsLocalization.finrank_eq R' (Submonoid.powers f) hle,
    IsLocalizedModule.finrank_eq (Submonoid.powers f) (IsScalarTower.toAlgHom R S S').toLinearMap hle]

def rankAbove {X Y : Scheme.{0}} (ψ : X ⟶ Y) (U : Y.Opens) : ℕ :=
  letI := (ψ.app U).hom.toAlgebra
  Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U)

/- English proof (translation)
Use `haveI : Nonempty U := by`. Take `⟨x, hx⟩` from `hne`. Conclude with `⟨⟨x, Y.basicOpen_le f hx⟩⟩`. Establish `hf : f ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hne`. Use `letI := (ψ.app U).hom.toAlgebra`. Use `letI := (ψ.app (Y.basicOpen f)).hom.toAlgebra`. Set `i : ψ ⁻¹ᵁ (Y.basicOpen f) ⟶ ψ ⁻¹ᵁ U` to `homOfLE (fun x hx => Y.basicOpen_le f hx)`. Use `letI : Algebra Γ(X, ψ ⁻¹ᵁ U) Γ(X, ψ ⁻¹ᵁ (Y.basicOpen f)) := (X.presheaf.map i.op).hom.toAlgebra`.

Use `haveI := hU.isLocalization_basicOpen f`. Use `haveI : IsLocalization.Away (algebraMap Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) f) Γ(X, ψ ⁻¹ᵁ (Y.basicOpen f)) := (hU.preimage ψ).isLocalization_of_eq_basicOpen _ i (Scheme.preimage_basicOpen ψ f)`. Use `finrank_away (R := Γ(Y, U)) (S := Γ(X, ψ ⁻¹ᵁ U)) (R' := Γ(Y, Y.basicOpen f)) (S' := Γ(X, ψ ⁻¹ᵁ (Y.basicOpen f))) f hf ?_` and prove the remaining obligations. Conclude with `congrArg CommRingCat.Hom.hom (ψ.naturality (homOfLE (Y.basicOpen_le f)).op)`.
-/
theorem rankAbove_basicOpen {X Y : Scheme.{0}} [IsIntegral Y] (ψ : X ⟶ Y) [IsAffineHom ψ]
    {U : Y.Opens} (hU : IsAffineOpen U) (f : Γ(Y, U)) (hne : (Y.basicOpen f : Set Y).Nonempty) :
    rankAbove ψ (Y.basicOpen f) = rankAbove ψ U := by
  haveI : Nonempty U := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, Y.basicOpen_le f hx⟩⟩
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hne
  letI := (ψ.app U).hom.toAlgebra
  letI := (ψ.app (Y.basicOpen f)).hom.toAlgebra
  let i : ψ ⁻¹ᵁ (Y.basicOpen f) ⟶ ψ ⁻¹ᵁ U := homOfLE (fun x hx => Y.basicOpen_le f hx)
  letI : Algebra Γ(X, ψ ⁻¹ᵁ U) Γ(X, ψ ⁻¹ᵁ (Y.basicOpen f)) := (X.presheaf.map i.op).hom.toAlgebra
  haveI := hU.isLocalization_basicOpen f
  haveI : IsLocalization.Away (algebraMap Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) f) Γ(X, ψ ⁻¹ᵁ (Y.basicOpen f)) :=
    (hU.preimage ψ).isLocalization_of_eq_basicOpen _ i (Scheme.preimage_basicOpen ψ f)
  refine finrank_away (R := Γ(Y, U)) (S := Γ(X, ψ ⁻¹ᵁ U)) (R' := Γ(Y, Y.basicOpen f))
    (S' := Γ(X, ψ ⁻¹ᵁ (Y.basicOpen f))) f hf ?_
  exact congrArg CommRingCat.Hom.hom (ψ.naturality (homOfLE (Y.basicOpen_le f)).op)

/- English proof (translation)
Introduce `X Y _ _ ψ hfin hsurj`. Take `⟨y⟩ : Nonempty Y` from `inferInstance`. Take `⟨_, ⟨U, hU, rfl⟩, hyU, -⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ`. Use `⟨rankAbove ψ U, ?_, MapDeg.of_isFinite fun V hV hne => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `ψ.surjective y haveI : Nonempty U := ⟨⟨_, hyU⟩⟩ haveI : Nonempty (ψ ⁻¹ᵁ U) := ⟨⟨x, hyU⟩⟩`.

Use `letI := (ψ.app U).hom.toAlgebra`. Use `haveI : Module.Finite Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) := ψ.finite_app U hU`. Use `haveI := IsSchemeTheoreticallyDominant.of_isDominant ψ`. Use `haveI : FaithfulSMul Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) := (faithfulSMul_iff_algebraMap_injective _ _).mpr (ψ.app_injective U)`. Conclude with `Module.finrank_pos`.

Take `⟨z, hz⟩` from `nonempty_preirreducible_inter U.isOpen V.isOpen ⟨y, hyU⟩ hne`. Take `⟨f, g, e, hzf⟩` from `exists_basicOpen_le_affine_inter hU hV z hz`. Express the relevant statement in the definitionally equal form `rankAbove ψ V = rankAbove ψ U`. Rewrite using `[← rankAbove_basicOpen ψ hU f ⟨z, hzf⟩, ← rankAbove_basicOpen ψ hV g ⟨z, e ▸ hzf⟩, e]`.
-/
theorem exists_mapDeg_of_isFinite : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (ψ : X ⟶ Y), IsFinite ψ → Surjective ψ → ∃ D : ℕ, 1 ≤ D ∧ MapDeg ψ D := by
  intro X Y _ _ ψ hfin hsurj
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  refine ⟨rankAbove ψ U, ?_, MapDeg.of_isFinite fun V hV hne => ?_⟩
  · obtain ⟨x, rfl⟩ := ψ.surjective y
    haveI : Nonempty U := ⟨⟨_, hyU⟩⟩
    haveI : Nonempty (ψ ⁻¹ᵁ U) := ⟨⟨x, hyU⟩⟩
    letI := (ψ.app U).hom.toAlgebra
    haveI : Module.Finite Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) := ψ.finite_app U hU
    haveI := IsSchemeTheoreticallyDominant.of_isDominant ψ
    haveI : FaithfulSMul Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (ψ.app_injective U)
    exact Module.finrank_pos
  · obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen ⟨y, hyU⟩ hne
    obtain ⟨f, g, e, hzf⟩ := exists_basicOpen_le_affine_inter hU hV z hz
    change rankAbove ψ V = rankAbove ψ U
    rw [← rankAbove_basicOpen ψ hU f ⟨z, hzf⟩, ← rankAbove_basicOpen ψ hV g ⟨z, e ▸ hzf⟩, e]

end DegKer

open DegKer in

/- English proof (translation)
Introduce `K _ _ P α _ _`. Use `polAV_isIntegral_of_isAlgClosed K P` as an intermediate fact. Use `P.isAb.smooth` as an intermediate fact. Establish `hs` using `(flat_and_surjective_of_isFinite_grpEnd K P.A α).2`. Take `⟨D, -, hD⟩` from `exists_mapDeg_of_isFinite _ _ α.left inferInstance hs`.

Take `⟨_, ⟨U, hU, rfl⟩, hξ, -⟩` from `P.A.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint P.A.left)) isOpen_univ`. Establish `: Nonempty U` using `⟨⟨_, hξ⟩⟩`. Establish `: Nonempty (α.left ⁻¹ᵁ U)`. Take `⟨x, hx⟩` from `α.left.surjective (genericPoint P.A.left)`. Conclude with `⟨⟨x, show α.left x ∈ U from hx ▸ hξ⟩⟩`.

Use `letI := (α.left.app U).hom.toAlgebra`. Establish `: Module.Finite Γ(P.A.left, U) Γ(P.A.left, α.left ⁻¹ᵁ U)` using `α.left.finite_app U hU`. Establish `: IsSchemeTheoreticallyDominant α.left` using `.of_isDominant _`. Establish `: FaithfulSMul Γ(P.A.left, U) Γ(P.A.left, α.left ⁻¹ᵁ U)` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr (α.left.app_injective U)`. Set `c : K →+* Γ(P.A.left, U)` to `(P.A.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom`.

Establish `: ExpChar Γ(P.A.left, U) (ringExpChar K)` using `expChar_of_injective_ringHom c.injective _`. Set `Ω` to `AlgebraicClosure (FractionRing Γ(P.A.left, U))`. Establish `: FaithfulSMul Γ(P.A.left, U) Ω`. Rewrite using `[faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq Γ(P.A.left, U) (FractionRing Γ(P.A.left, U)) Ω, RingHom.coe_comp]`. Conclude with `(RingHom.injective _).comp (IsFractionRing.injective _ _)`.

Take `⟨h0, e, he⟩` from `finrank_eq_pow_mul_card Γ(P.A.left, U) Γ(P.A.left, α.left ⁻¹ᵁ U) Ω (ringExpChar K)`. Rewrite `h0`, `he` using `[card_fibre_eq α.left hU Ω]`. Use `set z := Spec.map (CommRingCat.ofHom (algebraMap Γ(P.A.left, U) Ω)) ≫ hU.fromSpec with hz`. Set `z' : Over.mk (z ≫ P.A.hom) ⟶ P.A` to `Over.homMk z rfl`. Establish `h1 : Nat.card {y : Over.mk (z ≫ P.A.hom) ⟶ P.A // y ≫ α = z'} = Nat.card {y : Spec (CommRingCat.of Ω) ⟶ P.A.left // y ≫ α.left = z}`.

Use `Nat.card_congr (Equiv.ofBijective (fun y => ⟨y.1.left, congrArg CommaMorphism.left y.2⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `y y' h`. Conclude with `Subtype.ext (Over.OverMorphism.ext (congrArg Subtype.val h))`. Introduce and unpack `⟨y, hy⟩`. Use `⟨⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩, rfl⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `y ≫ P.A.hom = z ≫ P.A.hom`. Rewrite using `[← hy, Category.assoc, Over.w α]`. Rewrite `h0`, `he` using `[← h1]`. Establish `hne` using `(Nat.card_ne_zero.mp h0).1`. Rewrite `h0`, `he` using `[← card_coset_eq P.A _ α z' hne, ← card_ker_eq P.A α Ω (z ≫ P.A.hom)]`.

Use `⟨(Nat.card_ne_zero.mp h0).2, e, ?_⟩` and prove the remaining obligations. Rewrite using `[← he, hD.finrank_eq U hU ⟨_, hξ⟩]`. Conclude with `hD`.
-/
theorem mapDeg_eq_pow_mul_card_ker :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A), IsMonHom α → IsFinite α.left → Finite {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1} ∧ ∃ e : ℕ, MapDeg α.left (ringExpChar K ^ e * Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1}) := by
  intro K _ _ P α _ _
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P.isAb.smooth
  have hs := (flat_and_surjective_of_isFinite_grpEnd K P.A α).2
  obtain ⟨D, -, hD⟩ := exists_mapDeg_of_isFinite _ _ α.left inferInstance hs
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ := P.A.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint P.A.left)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  have : Nonempty (α.left ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := α.left.surjective (genericPoint P.A.left)
    exact ⟨⟨x, show α.left x ∈ U from hx ▸ hξ⟩⟩
  letI := (α.left.app U).hom.toAlgebra
  have : Module.Finite Γ(P.A.left, U) Γ(P.A.left, α.left ⁻¹ᵁ U) := α.left.finite_app U hU
  have : IsSchemeTheoreticallyDominant α.left := .of_isDominant _
  have : FaithfulSMul Γ(P.A.left, U) Γ(P.A.left, α.left ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (α.left.app_injective U)
  let c : K →+* Γ(P.A.left, U) :=
    (P.A.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have : ExpChar Γ(P.A.left, U) (ringExpChar K) := expChar_of_injective_ringHom c.injective _
  let Ω := AlgebraicClosure (FractionRing Γ(P.A.left, U))
  have : FaithfulSMul Γ(P.A.left, U) Ω := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq Γ(P.A.left, U) (FractionRing Γ(P.A.left, U)) Ω, RingHom.coe_comp]
    exact (RingHom.injective _).comp (IsFractionRing.injective _ _)
  obtain ⟨h0, e, he⟩ := finrank_eq_pow_mul_card Γ(P.A.left, U) Γ(P.A.left, α.left ⁻¹ᵁ U) Ω
    (ringExpChar K)
  rw [card_fibre_eq α.left hU Ω] at h0 he
  set z := Spec.map (CommRingCat.ofHom (algebraMap Γ(P.A.left, U) Ω)) ≫ hU.fromSpec with hz
  let z' : Over.mk (z ≫ P.A.hom) ⟶ P.A := Over.homMk z rfl
  have h1 : Nat.card {y : Over.mk (z ≫ P.A.hom) ⟶ P.A // y ≫ α = z'} =
      Nat.card {y : Spec (CommRingCat.of Ω) ⟶ P.A.left // y ≫ α.left = z} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun y => ⟨y.1.left, congrArg CommaMorphism.left y.2⟩) ⟨?_, ?_⟩)
    · intro y y' h
      exact Subtype.ext (Over.OverMorphism.ext (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      refine ⟨⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩, rfl⟩
      change y ≫ P.A.hom = z ≫ P.A.hom
      rw [← hy, Category.assoc, Over.w α]
  rw [← h1] at h0 he
  have hne := (Nat.card_ne_zero.mp h0).1
  rw [← card_coset_eq P.A _ α z' hne,
    ← card_ker_eq P.A α Ω (z ≫ P.A.hom)] at h0 he
  refine ⟨(Nat.card_ne_zero.mp h0).2, e, ?_⟩
  rw [← he, hD.finrank_eq U hU ⟨_, hξ⟩]
  exact hD

end GlobalTheory
end
