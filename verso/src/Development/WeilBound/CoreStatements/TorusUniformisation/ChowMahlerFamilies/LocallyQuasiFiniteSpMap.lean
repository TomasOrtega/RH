import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsContraction
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SameCompOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace PositivityTheory.Xgn.GeometricOfPeriods

open Polynomial in

/- English proof (translation)
Use `haveI : Fact (Irreducible (minpoly F f)) := ⟨minpoly.irreducible hf⟩`. Set `L` to `AdjoinRoot (minpoly F f)`. Set `a : L →ₐ[F] R` to `AdjoinRoot.liftAlgHom (minpoly F f) (Algebra.ofId F R) f (minpoly.aeval F f)`. Set `b : L →ₐ[F] ℂ` to `AdjoinRoot.liftAlgHom (minpoly F f) (Algebra.ofId F ℂ) r hr`. Establish `ha : a (AdjoinRoot.root _) = f` using `AdjoinRoot.liftAlgHom_root _ _ _ _`.

Establish `hb : b (AdjoinRoot.root _) = r` using `AdjoinRoot.liftAlgHom_root _ _ _ _`. Use `letI : Algebra L R := a.toRingHom.toAlgebra`. Use `letI : Algebra L ℂ := b.toRingHom.toAlgebra`. Use `haveI : IsScalarTower F L R := IsScalarTower.of_algebraMap_eq fun x => (a.commutes x).symm`. Use `haveI : IsScalarTower F L ℂ := IsScalarTower.of_algebraMap_eq fun x => (b.commutes x).symm`.

Use `haveI : Algebra.FiniteType L R := Algebra.FiniteType.of_restrictScalars_finiteType F L R`. Take `⟨M, hM⟩` from `Ideal.exists_maximal R`. Use `letI : Field (R ⧸ M) := Ideal.Quotient.field M`. Use `haveI : Module.Finite L (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing L (R ⧸ M)`. Set `q : (R ⧸ M) →ₐ[L] ℂ` to `IsAlgClosed.lift`.

Set `p : R →ₐ[L] ℂ` to `q.comp (Ideal.Quotient.mkₐ L M)`. Use `⟨p.restrictScalars F, ?_⟩` and prove the remaining obligations. Use `p.commutes (AdjoinRoot.root (minpoly F f))` as an intermediate fact. Express the relevant statement in the definitionally equal form `p (a _) = b _ at this`. Rewrite `this` using `[ha, hb]`.

Conclude with `this`.
-/
theorem exists_point {F R : Type} [Field F] [Algebra F ℂ] [CommRing R] [IsDomain R] [Algebra F R]
    [Algebra.FiniteType F R] (f : R) (hf : IsIntegral F f) (r : ℂ) (hr : aeval r (minpoly F f) = 0) :
    ∃ p : R →ₐ[F] ℂ, p f = r := by
  haveI : Fact (Irreducible (minpoly F f)) := ⟨minpoly.irreducible hf⟩
  let L := AdjoinRoot (minpoly F f)
  let a : L →ₐ[F] R := AdjoinRoot.liftAlgHom (minpoly F f) (Algebra.ofId F R) f (minpoly.aeval F f)
  let b : L →ₐ[F] ℂ := AdjoinRoot.liftAlgHom (minpoly F f) (Algebra.ofId F ℂ) r hr
  have ha : a (AdjoinRoot.root _) = f := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hb : b (AdjoinRoot.root _) = r := AdjoinRoot.liftAlgHom_root _ _ _ _
  letI : Algebra L R := a.toRingHom.toAlgebra
  letI : Algebra L ℂ := b.toRingHom.toAlgebra
  haveI : IsScalarTower F L R := IsScalarTower.of_algebraMap_eq fun x => (a.commutes x).symm
  haveI : IsScalarTower F L ℂ := IsScalarTower.of_algebraMap_eq fun x => (b.commutes x).symm
  haveI : Algebra.FiniteType L R := Algebra.FiniteType.of_restrictScalars_finiteType F L R
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite L (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing L (R ⧸ M)
  let q : (R ⧸ M) →ₐ[L] ℂ := IsAlgClosed.lift
  let p : R →ₐ[L] ℂ := q.comp (Ideal.Quotient.mkₐ L M)
  refine ⟨p.restrictScalars F, ?_⟩
  have := p.commutes (AdjoinRoot.root (minpoly F f))
  change p (a _) = b _ at this
  rw [ha, hb] at this
  exact this

open Polynomial TensorProduct in

/- English proof (translation)
Establish `hirr` using `minpoly.irreducible hf`. Establish `hsep : (minpoly F f).Separable` using `hirr.separable`. Establish `key : ∀ r r' : ℂ, aeval r (minpoly F f) = 0 → aeval r' (minpoly F f) = 0 → r = r'`. Introduce `r r' hr hr'`. Take `⟨p, hp⟩` from `exists_point f hf r hr`.

Take `⟨q, hq⟩` from `exists_point f hf r' hr'`. Establish `hroot : ((minpoly F f).map (algebraMap F ℂ)).IsRoot r`. Rewrite using `[IsRoot.def, eval_map_algebraMap]` and apply the resulting hypothesis. Take `⟨g, hg⟩` from `dvd_iff_isRoot.mpr hroot`. Establish `hs : ((X - C r) * g).Separable` using `hg ▸ hsep.map`.

Establish `hgr : g.eval r ≠ 0`. Introduce `h0`. Establish `h1 : (X - C r) ∣ g` using `dvd_iff_isRoot.mpr h0`. Conclude with `not_isUnit_X_sub_C r (hs.isCoprime.isUnit_of_dvd' dvd_rfl h1)`. Set `t : ℂ ⊗[F] R` to `1 ⊗ₜ f`.

Establish `ht : aeval t ((X - C r) * g) = 0`. Rewrite using `[← hg, aeval_map_algebraMap]`. Use `aeval_algHom_apply (Algebra.TensorProduct.includeRight (R := F) (A := ℂ) (B := R)) f (minpoly F f)` as an intermediate fact. Rewrite `this` using `[minpoly.aeval, map_zero]`. Conclude with `this`.

Take `⟨k, hk⟩ : (X - C r) ∣ g - C (g.eval r)` from `X_sub_C_dvd_sub_C_eval`. Establish `hidem : IsIdempotentElem (aeval t (C (g.eval r)⁻¹ * g))`. Establish `e1 : (C (g.eval r)⁻¹ * g) * (C (g.eval r)⁻¹ * g) = C (g.eval r)⁻¹ * g + (C (g.eval r)⁻¹ * C (g.eval r)⁻¹ * k) * ((X - C r) * g)`. Establish `e2 : C (g.eval r)⁻¹ * C (g.eval r) = 1` using `by rw [← C_mul, inv_mul_cancel₀ hgr, C_1]`. Take the linear combination `(C (g.eval r)⁻¹ * C (g.eval r)⁻¹ * g) * hk + (C (g.eval r)⁻¹ * g) * e2`.

Unfold `IsIdempotentElem`. Rewrite using `[← map_mul, e1, map_add, map_mul _ _ ((X - C r) * g), ht, mul_zero, add_zero]`. Establish `h2` using `h p q _ hidem`. Rewrite `h2` using `[← aeval_algHom_apply, ← aeval_algHom_apply]`. Simplify using `only [t, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul, hp, hq, coe_aeval_eq_eval, eval_mul, eval_C] at h2`.

Establish `h3 : g.eval r' ≠ 0`. Introduce `h0`. Rewrite `h2` using `[h0, mul_zero, inv_mul_cancel₀ hgr]`. Conclude with `one_ne_zero h2`. Establish `h4 : ((X - C r) * g).eval r' = 0` using `by rw [← hg, eval_map_algebraMap, hr']`.

Rewrite `h4` using `[eval_mul, eval_sub, eval_X, eval_C]`. Conclude with `(sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right h3)).symm`. Rewrite using `[← minpoly.natDegree_eq_one_iff]`. Establish `hc` using `card_rootSet_eq_natDegree (K := ℂ) hsep (IsAlgClosed.splits _)`. Establish `hle : Fintype.card ((minpoly F f).rootSet ℂ) ≤ 1` using `Fintype.card_le_one_iff.mpr fun a b => Subtype.ext (key _ _ (aeval_eq_zero_of_mem_rootSet a.2) (aeval_eq_zero_of_mem_rootSet b.2))`.

Use `minpoly.natDegree_pos hf` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_range_of_idem {F R : Type} [Field F] [CharZero F] [Algebra F ℂ] [CommRing R] [IsDomain R] [Algebra F R]
    [Algebra.FiniteType F R]
    (h : ∀ p q : R →ₐ[F] ℂ, ∀ e : ℂ ⊗[F] R, IsIdempotentElem e →
      Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _) e =
        Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) q (fun _ _ => Commute.all _ _) e)
    (f : R) (hf : IsIntegral F f) : f ∈ (algebraMap F R).range := by
  have hirr := minpoly.irreducible hf
  have hsep : (minpoly F f).Separable := hirr.separable
  have key : ∀ r r' : ℂ, aeval r (minpoly F f) = 0 → aeval r' (minpoly F f) = 0 → r = r' := by
    intro r r' hr hr'
    obtain ⟨p, hp⟩ := exists_point f hf r hr
    obtain ⟨q, hq⟩ := exists_point f hf r' hr'
    have hroot : ((minpoly F f).map (algebraMap F ℂ)).IsRoot r := by
      rwa [IsRoot.def, eval_map_algebraMap]
    obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr hroot
    have hs : ((X - C r) * g).Separable := hg ▸ hsep.map
    have hgr : g.eval r ≠ 0 := by
      intro h0
      have h1 : (X - C r) ∣ g := dvd_iff_isRoot.mpr h0
      exact not_isUnit_X_sub_C r (hs.isCoprime.isUnit_of_dvd' dvd_rfl h1)
    let t : ℂ ⊗[F] R := 1 ⊗ₜ f
    have ht : aeval t ((X - C r) * g) = 0 := by
      rw [← hg, aeval_map_algebraMap]
      have := aeval_algHom_apply (Algebra.TensorProduct.includeRight (R := F) (A := ℂ) (B := R)) f (minpoly F f)
      rw [minpoly.aeval, map_zero] at this
      exact this
    obtain ⟨k, hk⟩ : (X - C r) ∣ g - C (g.eval r) := X_sub_C_dvd_sub_C_eval
    have hidem : IsIdempotentElem (aeval t (C (g.eval r)⁻¹ * g)) := by
      have e1 : (C (g.eval r)⁻¹ * g) * (C (g.eval r)⁻¹ * g) =
          C (g.eval r)⁻¹ * g + (C (g.eval r)⁻¹ * C (g.eval r)⁻¹ * k) * ((X - C r) * g) := by
        have e2 : C (g.eval r)⁻¹ * C (g.eval r) = 1 := by rw [← C_mul, inv_mul_cancel₀ hgr, C_1]
        linear_combination (C (g.eval r)⁻¹ * C (g.eval r)⁻¹ * g) * hk + (C (g.eval r)⁻¹ * g) * e2
      unfold IsIdempotentElem
      rw [← map_mul, e1, map_add, map_mul _ _ ((X - C r) * g), ht, mul_zero, add_zero]
    have h2 := h p q _ hidem
    rw [← aeval_algHom_apply, ← aeval_algHom_apply] at h2
    simp only [t, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul, hp, hq, coe_aeval_eq_eval, eval_mul,
      eval_C] at h2
    have h3 : g.eval r' ≠ 0 := by
      intro h0
      rw [h0, mul_zero, inv_mul_cancel₀ hgr] at h2
      exact one_ne_zero h2
    have h4 : ((X - C r) * g).eval r' = 0 := by rw [← hg, eval_map_algebraMap, hr']
    rw [eval_mul, eval_sub, eval_X, eval_C] at h4
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right h3)).symm
  rw [← minpoly.natDegree_eq_one_iff]
  have hc := card_rootSet_eq_natDegree (K := ℂ) hsep (IsAlgClosed.splits _)
  have hle : Fintype.card ((minpoly F f).rootSet ℂ) ≤ 1 :=
    Fintype.card_le_one_iff.mpr fun a b => Subtype.ext
      (key _ _ (aeval_eq_zero_of_mem_rootSet a.2) (aeval_eq_zero_of_mem_rootSet b.2))
  have := minpoly.natDegree_pos hf
  omega

/- English proof (translation)
Establish `hf : IsField (X.presheaf.stalk (genPt ξ))` using `(RingEquiv.ofBijective _ h).toMulEquiv.isField (Field.toIsField Ω)`. Use `letI := hf.toField`. Establish `h1 : w ∈ Set.range (X.fromSpecStalk (genPt ξ))` using `by rw [Scheme.range_fromSpecStalk]; exact hw`. Take `⟨z, rfl⟩` from `h1`. Establish `: z = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ))` using `Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genPt ξ))) _ _`.

Rewrite using `[this]`. Conclude with `Scheme.fromSpecStalk_closedPoint`.
-/
theorem eq_of_specializes_of_bij {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (h : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) {w : X} (hw : w ⤳ genPt ξ) : w = genPt ξ := by
  have hf : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ h).toMulEquiv.isField (Field.toIsField Ω)
  letI := hf.toField
  have h1 : w ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by rw [Scheme.range_fromSpecStalk]; exact hw
  obtain ⟨z, rfl⟩ := h1
  have : z = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) :=
    Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genPt ξ))) _ _
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

/- English proof (translation)
Establish `e : spMap β ≫ spMap (Int.castRingHom O) = spMap (algebraMap ℚ F) ≫ spMap (algebraMap ℤ ℚ)`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Conclude with `Subsingleton.elim _ _`. Establish `h1 : IsPreimmersion (spMap (algebraMap ℤ ℚ))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors ℤ) (S := ℚ)`.

Establish `h2 : IsFinite (spMap (algebraMap ℚ F))` using `(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)`. Establish `h3 : LocallyQuasiFinite (spMap β ≫ spMap (Int.castRingHom O))` using `by rw [e]; infer_instance`. Conclude with `LocallyQuasiFinite.of_comp _ (spMap (Int.castRingHom O))`.
-/
theorem locallyQuasiFinite_spMap {O F : Type} [CommRing O] [Field F] [CharZero F] [FiniteDimensional ℚ F]
    (β : O →+* F) : LocallyQuasiFinite (spMap β) := by
  have e : spMap β ≫ spMap (Int.castRingHom O) = spMap (algebraMap ℚ F) ≫ spMap (algebraMap ℤ ℚ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact Subsingleton.elim _ _
  have h1 : IsPreimmersion (spMap (algebraMap ℤ ℚ)) := IsPreimmersion.of_isLocalization (nonZeroDivisors ℤ) (S := ℚ)
  have h2 : IsFinite (spMap (algebraMap ℚ F)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have h3 : LocallyQuasiFinite (spMap β ≫ spMap (Int.castRingHom O)) := by rw [e]; infer_instance
  exact LocallyQuasiFinite.of_comp _ (spMap (Int.castRingHom O))

/- English proof (translation)
Establish `hg` using `(isIrreducible_irreducibleComponent (x := genPt ξ)).isGenericPoint_genericPoint isClosed_irreducibleComponent`. Rewrite `hg` using `[hgen _ (hg.specializes mem_irreducibleComponent)]`. Establish `ho : IsOpen (irreducibleComponent (genPt ξ))` using `GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents _)`. Take `⟨s, hs⟩` from `h x`. Take `⟨V, hV, f, hf⟩` from `X.presheaf.germ_exist (x := genPt ξ) s`.

Take `⟨W, hW, hxW, hWle⟩` from `exists_isAffineOpen_mem_and_subset (x := genPt ξ) (U := V ⊓ ⟨_, ho⟩) ⟨hV, mem_irreducibleComponent⟩`. Establish `hWV : W ≤ V` using `fun z hz => (hWle hz).1`. Set `φ : Γ(X, W) ⟶ CommRingCat.of Ω` to `X.presheaf.germ W (genPt ξ) hxW ≫ Scheme.stalkClosedPointTo ξ`. Establish `hcomp : Spec.map φ ≫ hW.fromSpec = ξ`. Establish `e1 : Spec.map φ = Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.germ W (genPt ξ) hxW)` using `Spec.map_comp _ _`.

Establish `e2 : Spec.map (X.presheaf.germ W (genPt ξ) hxW) ≫ hW.fromSpec = X.fromSpecStalk (genPt ξ)` using `hW.fromSpecStalk_eq_fromSpecStalk hxW`. Conclude with `((e1 =≫ hW.fromSpec).trans ((Category.assoc _ _ _).trans (_ ≫= e2))).trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)`. Establish `hsp : ∀ z, genPt ξ ⤳ hW.fromSpec z` using `fun z => by`. Establish `: hW.fromSpec z ∈ (W : Set X)` using `by rw [← hW.range_fromSpec]; exact ⟨z, rfl⟩`. Conclude with `hg.specializes (hWle this).2`.

Use `⟨Γ(X, W), inferInstance, hW.fromSpec, φ.hom, inferInstanceAs (IsOpenImmersion hW.fromSpec), ?_, hcomp, ⟨X.presheaf.map (homOfLE hWV).op f, ?_⟩, hsp⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Apply `IsNilpotent.eq_zero` to reduce the goal to its premises. Rewrite using `[nilpotent_iff_mem_prime]`.

Introduce `J hJ`. Establish `h1` using `hsp (⟨J, hJ⟩ : PrimeSpectrum Γ(X, W))`. Establish `h2 : genPt ξ = hW.fromSpec (Spec.map φ (IsLocalRing.closedPoint Ω))` using `(congrArg genPt hcomp).symm.trans (Scheme.Hom.comp_apply _ _ _)`. Rewrite `h1` using `[h2]`. Establish `h3` using `(PrimeSpectrum.le_iff_specializes _ _).mpr (hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h1)`.

Apply `h3` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `φ.hom a ∈ (IsLocalRing.closedPoint Ω).asIdeal`. Rewrite using `[ha]`. Conclude with `Ideal.zero_mem _`. Rewrite using `[← hs, ← hf]`.

Conclude with `congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply (homOfLE hWV) _ hxW f)`.
-/
theorem exists_chart {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] {Ω : Type} [Field Ω]
    (ξ : Sp Ω ⟶ X) (h : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom)
    (hgen : ∀ w : X, w ⤳ genPt ξ → w = genPt ξ) (x : Ω) :
    ∃ (R : Type) (_ : CommRing R) (i : Sp R ⟶ X) (φ : R →+* Ω), IsOpenImmersion i ∧ Function.Injective φ ∧
      spMap φ ≫ i = ξ ∧ x ∈ Set.range φ ∧ ∀ z, genPt ξ ⤳ i z := by
  have hg := (isIrreducible_irreducibleComponent (x := genPt ξ)).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  rw [hgen _ (hg.specializes mem_irreducibleComponent)] at hg
  have ho : IsOpen (irreducibleComponent (genPt ξ)) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents _)
  obtain ⟨s, hs⟩ := h x
  obtain ⟨V, hV, f, hf⟩ := X.presheaf.germ_exist (x := genPt ξ) s
  obtain ⟨W, hW, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset (x := genPt ξ)
    (U := V ⊓ ⟨_, ho⟩) ⟨hV, mem_irreducibleComponent⟩
  have hWV : W ≤ V := fun z hz => (hWle hz).1
  let φ : Γ(X, W) ⟶ CommRingCat.of Ω := X.presheaf.germ W (genPt ξ) hxW ≫ Scheme.stalkClosedPointTo ξ
  have hcomp : Spec.map φ ≫ hW.fromSpec = ξ := by
    have e1 : Spec.map φ = Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.germ W (genPt ξ) hxW) :=
      Spec.map_comp _ _
    have e2 : Spec.map (X.presheaf.germ W (genPt ξ) hxW) ≫ hW.fromSpec = X.fromSpecStalk (genPt ξ) :=
      hW.fromSpecStalk_eq_fromSpecStalk hxW
    exact ((e1 =≫ hW.fromSpec).trans ((Category.assoc _ _ _).trans (_ ≫= e2))).trans
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)
  have hsp : ∀ z, genPt ξ ⤳ hW.fromSpec z := fun z => by
    have : hW.fromSpec z ∈ (W : Set X) := by rw [← hW.range_fromSpec]; exact ⟨z, rfl⟩
    exact hg.specializes (hWle this).2
  refine ⟨Γ(X, W), inferInstance, hW.fromSpec, φ.hom, inferInstanceAs (IsOpenImmersion hW.fromSpec), ?_, hcomp,
    ⟨X.presheaf.map (homOfLE hWV).op f, ?_⟩, hsp⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    apply IsNilpotent.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have h1 := hsp (⟨J, hJ⟩ : PrimeSpectrum Γ(X, W))
    have h2 : genPt ξ = hW.fromSpec (Spec.map φ (IsLocalRing.closedPoint Ω)) :=
      (congrArg genPt hcomp).symm.trans (Scheme.Hom.comp_apply _ _ _)
    rw [h2] at h1
    have h3 := (PrimeSpectrum.le_iff_specializes _ _).mpr
      (hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h1)
    apply h3
    change φ.hom a ∈ (IsLocalRing.closedPoint Ω).asIdeal
    rw [ha]; exact Ideal.zero_mem _
  · rw [← hs, ← hf]
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply (homOfLE hWV) _ hxW f)

/- English proof (translation)
Take `⟨hp', hq', h⟩` from `h`. Establish `e : spMap σ ≫ spMap e₀ = spMap (σ.comp e₀)` using `by rw [← Spec.map_comp]; rfl`. Set `j₀ : pullback s (spMap (σ.comp e₀)) ⟶ pullback s (spMap e₀)` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap σ) (by rw [Category.assoc, e, pullback.condition])`. Set `j : pullback s (spMap (σ.comp e₀)) ⟶ pullback (pullback.snd s (spMap e₀)) (spMap σ)` to `pullback.lift j₀ (pullback.snd _ _) (pullback.lift_snd _ _ _)`. Establish `key : ∀ (p : Sp ℂ ⟶ pullback s (spMap e₀)) (hp : p ≫ pullback.snd _ _ = 𝟙 _ ≫ spMap σ) hp', pullback.lift p (𝟙 _) hp = pullback.lift (p ≫ pullback.fst _ _) (𝟙 _) hp' ≫ j`.

Introduce `p hp hp'`. Apply `pullback.hom_ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [j, j₀, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]`. Simplify using `only [j, j₀, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, hp]`.

Simplify using `only [j, Category.assoc, pullback.lift_snd]`. Use `⟨by rw [hp, Category.id_comp], by rw [hq, Category.id_comp], fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[key p _ hp', key q _ hq', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Conclude with `j.continuous.image_connectedComponent_subset _ ⟨_, h z, rfl⟩`.
-/
theorem sameComp_baseChange {K F : Type} [Field K] [Field F] (e₀ : K →+* F) (σ : F →+* ℂ) {X : Scheme.{0}}
    (s : X ⟶ Sp K) (p q : Sp ℂ ⟶ pullback s (spMap e₀)) (hp : p ≫ pullback.snd _ _ = spMap σ)
    (hq : q ≫ pullback.snd _ _ = spMap σ)
    (h : GlobalTheory.KeyFam.SameComp s (σ.comp e₀) (p ≫ pullback.fst _ _) (q ≫ pullback.fst _ _)) :
    GlobalTheory.KeyFam.SameComp (pullback.snd s (spMap e₀)) σ p q := by
  obtain ⟨hp', hq', h⟩ := h
  have e : spMap σ ≫ spMap e₀ = spMap (σ.comp e₀) := by rw [← Spec.map_comp]; rfl
  let j₀ : pullback s (spMap (σ.comp e₀)) ⟶ pullback s (spMap e₀) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap σ) (by rw [Category.assoc, e, pullback.condition])
  let j : pullback s (spMap (σ.comp e₀)) ⟶ pullback (pullback.snd s (spMap e₀)) (spMap σ) :=
    pullback.lift j₀ (pullback.snd _ _) (pullback.lift_snd _ _ _)
  have key : ∀ (p : Sp ℂ ⟶ pullback s (spMap e₀)) (hp : p ≫ pullback.snd _ _ = 𝟙 _ ≫ spMap σ) hp',
      pullback.lift p (𝟙 _) hp = pullback.lift (p ≫ pullback.fst _ _) (𝟙 _) hp' ≫ j := by
    intro p hp hp'
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [j, j₀, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [j, j₀, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, hp]
    · simp only [j, Category.assoc, pullback.lift_snd]
  refine ⟨by rw [hp, Category.id_comp], by rw [hq, Category.id_comp], fun z => ?_⟩
  rw [key p _ hp', key q _ hq', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact j.continuous.image_connectedComponent_subset _ ⟨_, h z, rfl⟩

/- English proof (translation)
Take `⟨m, B, Q, -, hB, hc, h0, hQ0, hhol, hall⟩` from `GlobalTheory.PeriodChart.period_chart E H (FU.Di i) g ty (by rw [(FU.sig i).1, (FU.sig i).2]; exact hty) P hP`. Take `⟨b, ⟨hb, h, hh⟩, -⟩` from `hall P' hP'`. Establish `e : FU.u i (Q b) = FU.u i P'` using `(FU.fibre i _ _ (hhol.1 b hb) hP').2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩`. Use `GlobalTheory.KeyFam.sameComp_of_isHolTo (KA l) σ Xo.X Xo.s m B (fun b => FU.u i (Q b)) hB hc.isPreconnected (fun b hb => FU.over_σ i _ (hhol.1 b hb)) (FU.hol i m B Q hB hhol).1 0 h0 b hb` as an intermediate fact. Simplify `this` using `only [hQ0, e]`.
-/
theorem sameComp_periods {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (i : Fin FU.n)
    (hty : IsTypeFn H D.p D.q ty) {P P' : (FU.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (FU.Di i) ty P)
    (hP' : IsPeriod (FU.Di i) ty P') : GlobalTheory.KeyFam.SameComp Xo.s σ (FU.u i P) (FU.u i P') := by
  obtain ⟨m, B, Q, -, hB, hc, h0, hQ0, hhol, hall⟩ := GlobalTheory.PeriodChart.period_chart E H (FU.Di i) g ty
    (by rw [(FU.sig i).1, (FU.sig i).2]; exact hty) P hP
  obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := hall P' hP'
  have e : FU.u i (Q b) = FU.u i P' := (FU.fibre i _ _ (hhol.1 b hb) hP').2
    ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
  have := GlobalTheory.KeyFam.sameComp_of_isHolTo (KA l) σ Xo.X Xo.s m B (fun b => FU.u i (Q b)) hB hc.isPreconnected
    (fun b hb => FU.over_σ i _ (hhol.1 b hb)) (FU.hol i m B Q hB hhol).1 0 h0 b hb
  simpa only [hQ0, e] using this

end PositivityTheory.Xgn.GeometricOfPeriods

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y U Z g ty FU i hty hy x ⟨f, hf0, hf⟩`. Use `haveI := c.fin`. Use `haveI := Xo.smooth`. Use `haveI hs0 : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s`. Set `s : Xo.XF c ⟶ Sp c.F` to `pullback.snd _ _`.

Use `haveI hs : Smooth s := inferInstanceAs (Smooth (pullback.snd _ _))`. Establish `hK : GlobalTheory.IsNormalScheme (Spec (.of c.F))` using `inferInstance`. Use `haveI : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).mpr (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s ((GlobalTheory.isNormalScheme_iff _).mp hK))`. Use `haveI : IsLocallyNoetherian (Xo.XF c) := LocallyOfFiniteType.isLocallyNoetherian s`. Establish `hsurj : Function.Surjective (Scheme.stalkClosedPointTo Z.ξ₀).hom`.

Establish `h` using `Z.gen.bij.2`. Rewrite `h` using `[Scheme.stalkClosedPointTo_comp]`. Introduce `a`. Take `⟨b, hb⟩` from `h a`. Conclude with `⟨_, hb⟩`.

Establish `hgen : ∀ w : Xo.XF c, w ⤳ genPt Z.ξ₀ → w = genPt Z.ξ₀`. Introduce `w hw`. Use `haveI := PositivityTheory.Xgn.GeometricOfPeriods.locallyQuasiFinite_spMap β`. Use `haveI := Y.jQ_open`. Use `haveI : LocallyQuasiFinite Y.j := inferInstanceAs (LocallyQuasiFinite (Y.jQ ≫ pullback.fst _ _))`.

Establish `h1 : Y.j w = genPt (Z.ξ₀ ≫ Y.j)` using `PositivityTheory.Xgn.GeometricOfPeriods.eq_of_specializes_of_bij _ Z.gen.bij (hw.map Y.j.continuous)`. Establish `hd` using `(Y.j.isDiscrete_preimage_singleton (genPt (Z.ξ₀ ≫ Y.j))).to_subtype`. Establish `h2 : (⟨w, h1⟩ : Y.j ⁻¹' {genPt (Z.ξ₀ ≫ Y.j)}) ⤳ ⟨genPt Z.ξ₀, rfl⟩` using `(subtype_specializes_iff _ _).2 hw`. Conclude with `congrArg Subtype.val h2.eq`. Take `⟨R, _, j, φ, hj, hφ, hφj, ⟨a, rfl⟩, hsp⟩` from `PositivityTheory.Xgn.GeometricOfPeriods.exists_chart Z.ξ₀ hsurj hgen x`.

Use `haveI : IsDomain R := hφ.isDomain φ`. Set `ρ : c.F →+* R` to `(Spec.preimage (j ≫ s)).hom`. Establish `hρ : j ≫ s = spMap ρ` using `(Spec.map_preimage _).symm`. Use `letI : Algebra c.F R := ρ.toAlgebra`. Establish `hinc : φ.comp ρ = Z.inc`.

Establish `e : spMap (φ.comp ρ) = spMap Z.inc`. Rewrite using `[← Z.over_inc, ← hφj, Category.assoc]`. Express the relevant statement in the definitionally equal form `_ = spMap φ ≫ j ≫ s`. Rewrite using `[hρ, ← Spec.map_comp]`. Both sides reduce to the same expression.

Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective e)`. Use `haveI : Algebra.FiniteType c.F R := by`. Establish `h : LocallyOfFiniteType (spMap ρ)` using `by rw [← hρ]; infer_instance`. Conclude with `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h`. Establish `ha : IsIntegral c.F a`.

Use `IsAlgebraic.isIntegral ⟨f, hf0, hφ ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, ← hf, ← hinc, Polynomial.aeval_def, Polynomial.hom_eval₂]`. Both sides reduce to the same expression. Establish `hover : ∀ p : R →ₐ[c.F] ℂ, (spMap p.toRingHom ≫ j) ≫ s = spMap (algebraMap c.F ℂ)`. Introduce `p`.

Rewrite using `[Category.assoc, hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Conclude with `p.comp_algebraMap`. Establish `hper : ∀ p : R →ₐ[c.F] ℂ, ∃ P, IsPeriod (FU.Di i) ty P ∧ under (spMap p.toRingHom ≫ j) = FU.u i P`. Introduce `p`.

Use `hy _ (hover p) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Z.closure, Scheme.Hom.comp_apply]`. Conclude with `hsp _`. Take `⟨b, hb⟩` from `PositivityTheory.Xgn.GeometricOfPeriods.mem_range_of_idem (F := c.F) (R := R) (fun p q => by`.

Take `⟨P, hP, eP⟩` from `hper p`. Take `⟨Q, hQ, eQ⟩` from `hper q`. Use `GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem c.F (Xo.XF c) s R j p q hs hj hρ ?_` and prove the remaining obligations. Use `PositivityTheory.Xgn.GeometricOfPeriods.sameComp_baseChange _ _ Xo.s _ _ (hover p) (hover q) ?_` and prove the remaining obligations. Establish `h` using `PositivityTheory.Xgn.GeometricOfPeriods.sameComp_periods FU i hty hP hQ`.

Rewrite `h` using `[← eP, ← eQ]`. Conclude with `h) a ha`. Conclude with `⟨b, by rw [← hinc, ← hb]; rfl⟩`.
-/
theorem PositivityTheory.Xgn.geometric_of_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → Z.IsGeom := by
  intro E _ _ _ H D l Xo c O _ β Y U Z g ty FU i hty hy x ⟨f, hf0, hf⟩
  haveI := c.fin
  haveI := Xo.smooth
  haveI hs0 : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  haveI hs : Smooth s := inferInstanceAs (Smooth (pullback.snd _ _))
  have hK : GlobalTheory.IsNormalScheme (Spec (.of c.F)) := inferInstance
  haveI : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).mpr
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s ((GlobalTheory.isNormalScheme_iff _).mp hK))
  haveI : IsLocallyNoetherian (Xo.XF c) := LocallyOfFiniteType.isLocallyNoetherian s
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo Z.ξ₀).hom := by
    have h := Z.gen.bij.2
    rw [Scheme.stalkClosedPointTo_comp] at h
    intro a
    obtain ⟨b, hb⟩ := h a
    exact ⟨_, hb⟩
  have hgen : ∀ w : Xo.XF c, w ⤳ genPt Z.ξ₀ → w = genPt Z.ξ₀ := by
    intro w hw
    haveI := PositivityTheory.Xgn.GeometricOfPeriods.locallyQuasiFinite_spMap β
    haveI := Y.jQ_open
    haveI : LocallyQuasiFinite Y.j := inferInstanceAs (LocallyQuasiFinite (Y.jQ ≫ pullback.fst _ _))
    have h1 : Y.j w = genPt (Z.ξ₀ ≫ Y.j) :=
      PositivityTheory.Xgn.GeometricOfPeriods.eq_of_specializes_of_bij _ Z.gen.bij (hw.map Y.j.continuous)
    have hd := (Y.j.isDiscrete_preimage_singleton (genPt (Z.ξ₀ ≫ Y.j))).to_subtype
    have h2 : (⟨w, h1⟩ : Y.j ⁻¹' {genPt (Z.ξ₀ ≫ Y.j)}) ⤳ ⟨genPt Z.ξ₀, rfl⟩ :=
      (subtype_specializes_iff _ _).2 hw
    exact congrArg Subtype.val h2.eq
  obtain ⟨R, _, j, φ, hj, hφ, hφj, ⟨a, rfl⟩, hsp⟩ :=
    PositivityTheory.Xgn.GeometricOfPeriods.exists_chart Z.ξ₀ hsurj hgen x
  haveI : IsDomain R := hφ.isDomain φ
  let ρ : c.F →+* R := (Spec.preimage (j ≫ s)).hom
  have hρ : j ≫ s = spMap ρ := (Spec.map_preimage _).symm
  letI : Algebra c.F R := ρ.toAlgebra
  have hinc : φ.comp ρ = Z.inc := by
    have e : spMap (φ.comp ρ) = spMap Z.inc := by
      rw [← Z.over_inc, ← hφj, Category.assoc]
      change _ = spMap φ ≫ j ≫ s
      rw [hρ, ← Spec.map_comp]; rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  haveI : Algebra.FiniteType c.F R := by
    have h : LocallyOfFiniteType (spMap ρ) := by rw [← hρ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  have ha : IsIntegral c.F a := by
    refine IsAlgebraic.isIntegral ⟨f, hf0, hφ ?_⟩
    rw [map_zero, ← hf, ← hinc, Polynomial.aeval_def, Polynomial.hom_eval₂]
    rfl
  have hover : ∀ p : R →ₐ[c.F] ℂ, (spMap p.toRingHom ≫ j) ≫ s = spMap (algebraMap c.F ℂ) := by
    intro p
    rw [Category.assoc, hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact p.comp_algebraMap
  have hper : ∀ p : R →ₐ[c.F] ℂ, ∃ P, IsPeriod (FU.Di i) ty P ∧ under (spMap p.toRingHom ≫ j) = FU.u i P := by
    intro p
    refine hy _ (hover p) ?_
    rintro _ ⟨z, rfl⟩
    rw [Z.closure, Scheme.Hom.comp_apply]
    exact hsp _
  obtain ⟨b, hb⟩ := PositivityTheory.Xgn.GeometricOfPeriods.mem_range_of_idem (F := c.F) (R := R) (fun p q => by
    obtain ⟨P, hP, eP⟩ := hper p
    obtain ⟨Q, hQ, eQ⟩ := hper q
    refine GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem c.F (Xo.XF c) s R j p q hs hj hρ ?_
    refine PositivityTheory.Xgn.GeometricOfPeriods.sameComp_baseChange _ _ Xo.s _ _ (hover p) (hover q) ?_
    have h := PositivityTheory.Xgn.GeometricOfPeriods.sameComp_periods FU i hty hP hQ
    rw [← eP, ← eQ] at h
    exact h) a ha
  exact ⟨b, by rw [← hinc, ← hb]; rfl⟩
