import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UPoinc.UCTraitEx

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨a, ha, ha0⟩` from `hne`. Establish `hP : (RingHom.ker ψ).IsPrime` using `RingHom.ker_isPrime ψ`.

Establish `hbot : RingHom.ker ψ ≠ ⊥` using `fun h => ha0 (by`. Establish `h' : a ∈ RingHom.ker ψ` using `ha`. Rewrite using `[h, Ideal.mem_bot] at h')` and apply the resulting hypothesis. Use `haveI hmax : (RingHom.ker ψ).IsMaximal := hP.isMaximal hbot`. Use `haveI := GlobalTheory.finite_quotient_of_finiteType_int (RingHom.ker ψ)`.

Use `haveI : CharZero (o ⧸ RingHom.ker ψ) := (RingHom.charZero_iff (RingHom.kerLift_injective ψ)).2 inferInstance`. Conclude with `not_finite (o ⧸ RingHom.ker ψ)`.
-/
theorem injective_of_charZero {o K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field K] [CharZero K]
    (ψ : o →+* K) : Function.Injective ψ := by
  rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha, ha0⟩ := hne
  have hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hbot : RingHom.ker ψ ≠ ⊥ := fun h => ha0 (by
    have h' : a ∈ RingHom.ker ψ := ha
    rwa [h, Ideal.mem_bot] at h')
  haveI hmax : (RingHom.ker ψ).IsMaximal := hP.isMaximal hbot
  haveI := GlobalTheory.finite_quotient_of_finiteType_int (RingHom.ker ψ)
  haveI : CharZero (o ⧸ RingHom.ker ψ) := (RingHom.charZero_iff (RingHom.kerLift_injective ψ)).2 inferInstance
  exact not_finite (o ⧸ RingHom.ker ψ)

/- English proof (translation)
Use `letI := b.toAlgebra`. Use `haveI := hb`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (x ≫ z)`. Establish `hinj` using `injective_of_charZero ψ.hom`. Set `ψ' : F →+* K` to `IsFractionRing.lift hinj`.

Establish `hc : ψ'.comp b = ψ.hom` using `RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a`. Establish `e : x ≫ z = spMap ψ' ≫ spMap b`. Rewrite using `[GlobalTheory.Poinc.GCTrait.spMap_comp'', hc, ← hψ]`. Both sides reduce to the same expression. Conclude with `⟨pullback.lift x (spMap ψ') e, pullback.lift_fst _ _ _⟩`.
-/
theorem exists_lift_genericFibre {o F K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F]
    (b : o →+* F) (hb : letI := b.toAlgebra; IsFractionRing o F) [Field K] [CharZero K] {Z : Scheme.{0}} (z : Z ⟶ Sp o)
    (x : Sp K ⟶ Z) : ∃ x' : Sp K ⟶ pullback z (spMap b), x' ≫ pullback.fst _ _ = x := by
  letI := b.toAlgebra
  haveI := hb
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ z)
  have hinj := injective_of_charZero ψ.hom
  let ψ' : F →+* K := IsFractionRing.lift hinj
  have hc : ψ'.comp b = ψ.hom := RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  have e : x ≫ z = spMap ψ' ≫ spMap b := by
    rw [GlobalTheory.Poinc.GCTrait.spMap_comp'', hc, ← hψ]; rfl
  exact ⟨pullback.lift x (spMap ψ') e, pullback.lift_fst _ _ _⟩

/- English proof (translation)
Take `⟨U, hU, hy, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := y (default : PrimeSpectrum (PadicAlgCl p))) trivial`. Establish `hr : Set.range y ⊆ Set.range hU.fromSpec`. Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) q default]`. Conclude with `hy`.

Take `⟨φ, hφ⟩` from `Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec y hr)`. Take `⟨a, ha⟩` from `Spec.map_surjective (hU.fromSpec ≫ s)`. Establish `hft : a.hom.FiniteType`. Rewrite using `[← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ha]`. Use `infer_instance`.

Use `letI := a.hom.toAlgebra`. Take `⟨T, hT⟩` from `Algebra.FiniteType.out (R := ℚ) (A := Γ(X, U)) (self := hft)`. Set `S : Set (PadicAlgCl p)` to `φ.hom '' (T : Set Γ(X, U))`. Establish `hSfin : S.Finite` using `T.finite_toSet.image _`. Use `haveI : Finite S := hSfin.to_subtype`.

Set `K` to `IntermediateField.adjoin ℚ_[p] S`. Establish `hK : FiniteDimensional ℚ_[p] K` using `IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Establish `hS : S ⊆ K` using `IntermediateField.subset_adjoin ℚ_[p] S`. Establish `hc : ∀ c : ℚ, φ.hom (a.hom c) ∈ K` using `fun c => by`. Rewrite using `[show φ.hom (a.hom c) = (φ.hom.comp a.hom) c from rfl, eq_ratCast]`.

Conclude with `SubfieldClass.ratCast_mem K c`. Establish `hmem : ∀ b, φ.hom b ∈ K` using `fun b => by`. Establish `hb : b ∈ Algebra.adjoin ℚ (T : Set Γ(X, U))` using `hT ▸ Algebra.mem_top`. Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hS ⟨x, hx, rfl⟩`.

Consider the case `algebraMap c => exact hc c`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `K.add_mem ha hb`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `K.mul_mem ha hb`.

Set `φK : Γ(X, U) →+* K` to `φ.hom.codRestrict K hmem`. Use `⟨K, hK, spMap φK ≫ hU.fromSpec, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, GlobalTheory.Poinc.GCTrait.spMap_comp'', ← IsOpenImmersion.lift_fac hU.fromSpec y hr, ← hφ]`. Both sides reduce to the same expression.
-/
theorem exists_finite_point_rat {X : Scheme.{0}} (s : X ⟶ Sp ℚ) [LocallyOfFiniteType s] (p : ℕ) [Fact p.Prime]
    (y : Sp (PadicAlgCl p) ⟶ X) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (x : Sp K ⟶ X),
      spMap (algebraMap K (PadicAlgCl p)) ≫ x = y := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum (PadicAlgCl p))) trivial
  have hr : Set.range y ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) q default]
    exact hy
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec y hr)
  obtain ⟨a, ha⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hft : a.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ha]
    infer_instance
  letI := a.hom.toAlgebra
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := ℚ) (A := Γ(X, U)) (self := hft)
  let S : Set (PadicAlgCl p) := φ.hom '' (T : Set Γ(X, U))
  have hSfin : S.Finite := T.finite_toSet.image _
  haveI : Finite S := hSfin.to_subtype
  let K := IntermediateField.adjoin ℚ_[p] S
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hS : S ⊆ K := IntermediateField.subset_adjoin ℚ_[p] S
  have hc : ∀ c : ℚ, φ.hom (a.hom c) ∈ K := fun c => by
    rw [show φ.hom (a.hom c) = (φ.hom.comp a.hom) c from rfl, eq_ratCast]
    exact SubfieldClass.ratCast_mem K c
  have hmem : ∀ b, φ.hom b ∈ K := fun b => by
    have hb : b ∈ Algebra.adjoin ℚ (T : Set Γ(X, U)) := hT ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS ⟨x, hx, rfl⟩
    | algebraMap c => exact hc c
    | add a b _ _ ha hb => rw [map_add]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  let φK : Γ(X, U) →+* K := φ.hom.codRestrict K hmem
  refine ⟨K, hK, spMap φK ≫ hU.fromSpec, ?_⟩
  rw [← Category.assoc, GlobalTheory.Poinc.GCTrait.spMap_comp'', ← IsOpenImmersion.lift_fac hU.fromSpec y hr, ← hφ]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H Dw _ l Xo cf C X p _`. Use `haveI := C.iF_open`. Use `haveI := C.ded`. Use `haveI := C.ft`. Use `letI := C.b.toAlgebra`.

Use `haveI := C.isFractionRing`. Use `haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)`. Establish `hemb : Topology.IsEmbedding (pullback.fst C.z (spMap C.b))` using `Scheme.Hom.isEmbedding _`. Set `S : Set C.Z` to `pullback.fst C.z (spMap C.b) '' (Set.range C.iF)ᶜ`. Establish `hS : pullback.fst C.z (spMap C.b) ⁻¹' closure S = (Set.range C.iF)ᶜ`.

Rewrite using `[← hemb.isInducing.closure_eq_preimage_closure_image]`. Conclude with `C.iF.isOpenEmbedding.isOpen_range.isClosed_compl.closure_eq`. Set `V : C.Z.Opens` to `⟨(closure S)ᶜ, isClosed_closure.isOpen_compl⟩`. Use `⟨X.π ⁻¹ᵁ V, ?_, ?_⟩` and prove the remaining obligations. Set `w : Sp X.Ω₁` to `IsLocalRing.closedPoint X.Ω₁`.

Use `⟨X.M.pt w, ?_⟩` and prove the remaining obligations. Establish `e : X.π (X.M.pt w) = pullback.fst C.z (spMap C.b) (C.iF ((spMap (ratHull X.S.R).val.toRingHom ≫ X.u) w))`. Rewrite using `[← Scheme.Hom.comp_apply, X.comp]`. Simplify using `only [UCompact.i, Scheme.Hom.comp_apply]`. Use `show X.π (X.M.pt w) ∈ (closure S)ᶜ`.

Rewrite using `[e]`. Introduce `hc`. Establish `h' : C.iF ((spMap (ratHull X.S.R).val.toRingHom ≫ X.u) w) ∈ (Set.range C.iF)ᶜ` using `hS ▸ hc`. Conclude with `h' ⟨_, rfl⟩`. Introduce `y hr`.

Take `⟨x', hx'⟩` from `exists_lift_genericFibre C.b C.isFractionRing C.z (gPt p ≫ y ≫ X.π)`. Establish `hr' : Set.range x' ⊆ Set.range C.iF`. Introduce and unpack `_ ⟨w, rfl⟩`. Assume the negation of the conclusion as `hn`. Establish `h1 : pullback.fst C.z (spMap C.b) (x' w) ∈ closure S` using `subset_closure ⟨_, hn, rfl⟩`.

Establish `h2 : (gPt p ≫ y) w ∈ X.π ⁻¹ᵁ V` using `hr ⟨w, rfl⟩`. Establish `h3 : pullback.fst C.z (spMap C.b) (x' w) = X.π ((gPt p ≫ y) w)`. Rewrite using `[← Scheme.Hom.comp_apply, hx']`. Simplify using `only [Scheme.Hom.comp_apply]`. Conclude with `h2 (h3 ▸ h1)`.

Set `y₁ : Sp (PadicAlgCl p) ⟶ Xo.XF cf` to `IsOpenImmersion.lift C.iF x' hr'`. Establish `hy₁ : y₁ ≫ C.i = gPt p ≫ y ≫ X.π` using `by show y₁ ≫ C.iF ≫ pullback.fst _ _ = _`. Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac, hx']`. Use `haveI := cf.fin`. Use `haveI := Xo.smooth`.

Use `haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _`. Use `haveI : LocallyOfFiniteType (spMap (algebraMap ℚ cf.F)) := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)`. Take `⟨K, hK, x, hx⟩` from `exists_finite_point_rat (pullback.snd _ _ ≫ spMap (algebraMap ℚ cf.F)) p y₁`. Take `⟨hdvr, hcomp, hunit⟩` from `GlobalTheory.intRing_complete_dvr p K hK`. Use `haveI := hdvr`.

Use `haveI : CharZero (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := inferInstance`. Set `e : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ≃ₐ[GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K] K` to `FractionRing.algEquiv _ K`. Set `es : K →+* FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)` to `e.symm.toRingEquiv.toRingHom`. Establish `hbase : GlobalTheory.Mum.Base (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)` using `⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩`. Take `⟨T, f, fK, hinj, hloc, hfin, hc, hTy⟩` from `GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo cf _ hbase hdvr (spMap es ≫ x)`.

Use `haveI : IsDiscreteValuationRing T.V := T.cdvr.1`. Take `⟨ι, hι, hint⟩` from `GlobalTheory.Poinc.GCTrait.exists_ext_emb p _ T.V f fK hinj hloc hfin hc _ hunit`. Establish `h2 : algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p) = (algebraMap K (PadicAlgCl p)).comp e.toRingEquiv.toRingHom`. Use `IsLocalization.ringHom_ext (nonZeroDivisors (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (RingHom.ext fun v => ?_)` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]`.

Use `(IsFractionRing.lift_algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) v).trans ?_` and prove the remaining obligations. Use `show _ = algebraMap K (PadicAlgCl p) (e (algebraMap _ _ v))`. Rewrite using `[AlgEquiv.commutes]`. Both sides reduce to the same expression. Establish `hκ : (algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p)).comp es = algebraMap K (PadicAlgCl p)`.

Use extensionality with `k`. Rewrite using `[h2]`. Use `show algebraMap K (PadicAlgCl p) (e (e.symm k)) = _`. Rewrite using `[AlgEquiv.apply_symm_apply]`. Establish `key : spMap ι ≫ spMap fK ≫ spMap es = spMap (algebraMap K (PadicAlgCl p))`.

Rewrite using `[GlobalTheory.Poinc.GCTrait.spMap_comp'', GlobalTheory.Poinc.GCTrait.spMap_comp'', ← RingHom.comp_assoc, hι, hκ]`. Use `⟨⟨y, rfl, T, ι, hint, ?_⟩, rfl⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_uCTrait_of_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime], ∃ U : X.M.Z.Opens, (U : Set X.M.Z).Nonempty ∧ ∀ y : Sp (OO p) ⟶ X.M.Z, Set.range (gPt p ≫ y) ⊆ U → ∃ ct : UCTrait X p (y (cPt p)), ct.y = y := by
  intro E _ _ _ H Dw _ l Xo cf C X p _
  haveI := C.iF_open
  haveI := C.ded
  haveI := C.ft
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb : Topology.IsEmbedding (pullback.fst C.z (spMap C.b)) := Scheme.Hom.isEmbedding _
  let S : Set C.Z := pullback.fst C.z (spMap C.b) '' (Set.range C.iF)ᶜ
  have hS : pullback.fst C.z (spMap C.b) ⁻¹' closure S = (Set.range C.iF)ᶜ := by
    rw [← hemb.isInducing.closure_eq_preimage_closure_image]
    exact C.iF.isOpenEmbedding.isOpen_range.isClosed_compl.closure_eq
  let V : C.Z.Opens := ⟨(closure S)ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨X.π ⁻¹ᵁ V, ?_, ?_⟩
  · let w : Sp X.Ω₁ := IsLocalRing.closedPoint X.Ω₁
    refine ⟨X.M.pt w, ?_⟩
    have e : X.π (X.M.pt w) =
        pullback.fst C.z (spMap C.b) (C.iF ((spMap (ratHull X.S.R).val.toRingHom ≫ X.u) w)) := by
      rw [← Scheme.Hom.comp_apply, X.comp]
      simp only [UCompact.i, Scheme.Hom.comp_apply]
    show X.π (X.M.pt w) ∈ (closure S)ᶜ
    rw [e]
    intro hc
    have h' : C.iF ((spMap (ratHull X.S.R).val.toRingHom ≫ X.u) w) ∈ (Set.range C.iF)ᶜ := hS ▸ hc
    exact h' ⟨_, rfl⟩
  · intro y hr
    obtain ⟨x', hx'⟩ := exists_lift_genericFibre C.b C.isFractionRing C.z (gPt p ≫ y ≫ X.π)
    have hr' : Set.range x' ⊆ Set.range C.iF := by
      rintro _ ⟨w, rfl⟩
      by_contra hn
      have h1 : pullback.fst C.z (spMap C.b) (x' w) ∈ closure S := subset_closure ⟨_, hn, rfl⟩
      have h2 : (gPt p ≫ y) w ∈ X.π ⁻¹ᵁ V := hr ⟨w, rfl⟩
      have h3 : pullback.fst C.z (spMap C.b) (x' w) = X.π ((gPt p ≫ y) w) := by
        rw [← Scheme.Hom.comp_apply, hx']
        simp only [Scheme.Hom.comp_apply]
      exact h2 (h3 ▸ h1)
    let y₁ : Sp (PadicAlgCl p) ⟶ Xo.XF cf := IsOpenImmersion.lift C.iF x' hr'
    have hy₁ : y₁ ≫ C.i = gPt p ≫ y ≫ X.π := by
      show y₁ ≫ C.iF ≫ pullback.fst _ _ = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hx']
    haveI := cf.fin
    haveI := Xo.smooth
    haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
    haveI : LocallyOfFiniteType (spMap (algebraMap ℚ cf.F)) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
    obtain ⟨K, hK, x, hx⟩ := exists_finite_point_rat (pullback.snd _ _ ≫ spMap (algebraMap ℚ cf.F)) p y₁
    obtain ⟨hdvr, hcomp, hunit⟩ := GlobalTheory.intRing_complete_dvr p K hK
    haveI := hdvr
    haveI : CharZero (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := inferInstance
    let e : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ≃ₐ[GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K] K := FractionRing.algEquiv _ K
    let es : K →+* FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := e.symm.toRingEquiv.toRingHom
    have hbase : GlobalTheory.Mum.Base (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) :=
      ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
    obtain ⟨T, f, fK, hinj, hloc, hfin, hc, hTy⟩ :=
      GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo cf _ hbase hdvr (spMap es ≫ x)
    haveI : IsDiscreteValuationRing T.V := T.cdvr.1
    obtain ⟨ι, hι, hint⟩ := GlobalTheory.Poinc.GCTrait.exists_ext_emb p _ T.V f fK hinj hloc hfin hc _ hunit
    have h2 : algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p) =
        (algebraMap K (PadicAlgCl p)).comp e.toRingEquiv.toRingHom := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (RingHom.ext fun v => ?_)
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
      refine (IsFractionRing.lift_algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) v).trans ?_
      show _ = algebraMap K (PadicAlgCl p) (e (algebraMap _ _ v))
      rw [AlgEquiv.commutes]
      rfl
    have hκ : (algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p)).comp es =
        algebraMap K (PadicAlgCl p) := by
      ext k
      rw [h2]
      show algebraMap K (PadicAlgCl p) (e (e.symm k)) = _
      rw [AlgEquiv.apply_symm_apply]
    have key : spMap ι ≫ spMap fK ≫ spMap es = spMap (algebraMap K (PadicAlgCl p)) := by
      rw [GlobalTheory.Poinc.GCTrait.spMap_comp'', GlobalTheory.Poinc.GCTrait.spMap_comp'', ← RingHom.comp_assoc, hι, hκ]
    refine ⟨⟨y, rfl, T, ι, hint, ?_⟩, rfl⟩
    calc gPt p ≫ y ≫ X.π = y₁ ≫ C.i := hy₁.symm
      _ = (spMap (algebraMap K (PadicAlgCl p)) ≫ x) ≫ C.i := by rw [hx]
      _ = ((spMap ι ≫ spMap fK ≫ spMap es) ≫ x) ≫ C.i := by rw [key]
      _ = spMap ι ≫ T.y ≫ C.i := by rw [hTy]; simp only [Category.assoc]

end GlobalTheory.UPoinc.UCTraitEx
