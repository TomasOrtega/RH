import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossNormallyAtOfForallMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardBasisExtensionDetNeZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh
open GlobalTheory.TopForm

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AdaptedFrame

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in

/- English proof (translation)
Take `⟨V, hV, hx, hVO⟩` from `Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hxO`. Establish `h` using `HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top`. Take `⟨s, hs, h⟩` from `(RingHom.locally_iff_isLocalization RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h`. Take `⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), x ∈ Y.basicOpen (t : Γ(Y, V))` from `Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)`. Use `IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))` as an intermediate fact.

Establish `h₁` using `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))`. Establish `h₂ : (algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D`. Rewrite using `[← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]`. Conclude with `h₁`. Use `letI := (algX p (Y.basicOpen (t : Γ(Y, V)))).toAlgebra`.

Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension D k Γ(Y, Y.basicOpen (t : Γ(Y, V))) := h₂`. Take `⟨ι, σ, _, _, P, hP⟩` from `‹Algebra.IsStandardSmoothOfRelativeDimension D k Γ(Y, Y.basicOpen (t : Γ(Y, V)))›.out`. Use `letI := Fintype.ofFinite ι`. Use `letI := Fintype.ofFinite σ`. Establish `hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D`.

Rewrite using `[Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]`. Simplify using `[Algebra.Presentation.dimension]`. Set `e` to `Fintype.equivFinOfCardEq hc`. Conclude with `⟨_, fun i => P.val (e.symm i), P.basisKaehler.reindex e, (Y.basicOpen_le _).trans hVO, hxt, hV.basicOpen _, fun i => by simp⟩`.
-/
theorem exists_basis_dFun {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ)
    [SmoothOfRelativeDimension D p] {O : Y.Opens} {x : Y} (hxO : x ∈ O) :
    ∃ (U : Y.Opens) (f : Fin D → Γ(Y, U)) (b : Module.Basis (Fin D) Γ(Y, U) (Omega (algX p U))),
      U ≤ O ∧ x ∈ U ∧ IsAffineOpen U ∧ ∀ i, b i = dFun (algX p U) (f i) := by
  classical
  obtain ⟨V, hV, hx, hVO⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hxO
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), x ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  letI := (algX p (Y.basicOpen (t : Γ(Y, V)))).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k Γ(Y, Y.basicOpen (t : Γ(Y, V))) := h₂
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    ‹Algebra.IsStandardSmoothOfRelativeDimension D k Γ(Y, Y.basicOpen (t : Γ(Y, V)))›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨_, fun i => P.val (e.symm i), P.basisKaehler.reindex e, (Y.basicOpen_le _).trans hVO, hxt,
    hV.basicOpen _, fun i => by simp⟩

/- English proof (translation)
Establish `hs : Function.Surjective (algebraMap A (IsLocalRing.ResidueField A))` using `IsLocalRing.residue_surjective`. Establish `hinj` using `GlobalTheory.SmoothTangent.kerCotangentToTensor_injective k A (IsLocalRing.ResidueField A) hs`. Establish `hker : IsLocalRing.maximalIdeal A = RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))` using `IsLocalRing.ker_residue.symm`. Set `c` to `Ideal.Cotangent.equivOfEq _ _ hker`. Set `e : IsLocalRing.CotangentSpace A →ₗ[A] IsLocalRing.ResidueField A ⊗[A] Ω[A⁄k]` to `KaehlerDifferential.kerCotangentToTensor k A (IsLocalRing.ResidueField A) ∘ₗ c.toLinearMap`.

Establish `he : Function.Injective (e.extendScalarsOfSurjective hs)` using `hinj.comp c.injective`. Use `h.map' (e.extendScalarsOfSurjective hs) (LinearMap.ker_eq_bot.2 he)` as an intermediate fact. Establish `key : ⇑(e.extendScalarsOfSurjective hs) ∘ (fun j => ((IsLocalRing.maximalIdeal A).toCotangent ⟨f j, hf j⟩ : IsLocalRing.CotangentSpace A)) = fun j => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f j)`. Use function extensionality and compare the values at `j`. Simplify using `only [Function.comp_apply, LinearMap.extendScalarsOfSurjective_apply, e, LinearMap.comp_apply,`.

Use the proof step `LinearEquiv.coe_coe, c]`. Rewrite using `[Ideal.Cotangent.equivOfEq_toCotangent, KaehlerDifferential.kerCotangentToTensor_toCotangent]`. Both sides reduce to the same expression. Rewrite `this` using `[key]`. Conclude with `this`.
-/
theorem linearIndependent_tmul_D {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] {J : Type} (f : J → A)
    (hf : ∀ j, f j ∈ IsLocalRing.maximalIdeal A)
    (h : LinearIndependent (IsLocalRing.ResidueField A) (fun j =>
      ((IsLocalRing.maximalIdeal A).toCotangent ⟨f j, hf j⟩ : IsLocalRing.CotangentSpace A))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun j => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f j)) := by
  have hs : Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) :=
    IsLocalRing.residue_surjective
  have hinj := GlobalTheory.SmoothTangent.kerCotangentToTensor_injective k A (IsLocalRing.ResidueField A) hs
  have hker : IsLocalRing.maximalIdeal A = RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) :=
    IsLocalRing.ker_residue.symm
  let c := Ideal.Cotangent.equivOfEq _ _ hker
  let e : IsLocalRing.CotangentSpace A →ₗ[A] IsLocalRing.ResidueField A ⊗[A] Ω[A⁄k] :=
    KaehlerDifferential.kerCotangentToTensor k A (IsLocalRing.ResidueField A) ∘ₗ c.toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) := hinj.comp c.injective
  have := h.map' (e.extendScalarsOfSurjective hs) (LinearMap.ker_eq_bot.2 he)
  have key : ⇑(e.extendScalarsOfSurjective hs) ∘ (fun j =>
      ((IsLocalRing.maximalIdeal A).toCotangent ⟨f j, hf j⟩ : IsLocalRing.CotangentSpace A)) =
      fun j => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f j) := by
    funext j
    simp only [Function.comp_apply, LinearMap.extendScalarsOfSurjective_apply, e, LinearMap.comp_apply,
    LinearEquiv.coe_coe, c]
    rw [Ideal.Cotangent.equivOfEq_toCotangent, KaehlerDifferential.kerCotangentToTensor_toCotangent]
    rfl
  rw [key] at this
  exact this

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in

/- English proof (translation)
Use `letI : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hy).hom.toAlgebra`. Use `letI : Algebra k Γ(X, U) := (algX p U).toAlgebra`. Use `haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' h`. Use `haveI : Smooth p := SmoothOfRelativeDimension.smooth n p`. Establish `hft : (algX p U).FiniteType`.

Establish `h₀` using `HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top`. Conclude with `RingHom.FiniteType.comp h₀ (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)`. Use `haveI : Algebra.FiniteType k Γ(X, U) := hft`. Use `haveI : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal := hU.isLocalization_stalk ⟨y, hy⟩`. Use `haveI : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk y) := Algebra.EssFiniteType.of_isLocalization _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl`.

Use `haveI : Algebra.EssFiniteType k (X.presheaf.stalk y) := Algebra.EssFiniteType.comp k Γ(X, U) (X.presheaf.stalk y)`. Use `haveI : Algebra.EssFiniteType (X.presheaf.stalk y) (IsLocalRing.ResidueField (X.presheaf.stalk y)) := inferInstance`. Use `haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk y)) := Algebra.EssFiniteType.comp k (X.presheaf.stalk y) _`. Conclude with `Algebra.FormallySmooth.of_perfectField`.
-/
theorem formallySmooth_residueField {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    (p : X ⟶ Sp k) {n : ℕ} [SmoothOfRelativeDimension n p] {U : X.Opens} (hU : IsAffineOpen U)
    (y : X) (hy : y ∈ U) [Algebra k (X.presheaf.stalk y)]
    (h : algebraMap k (X.presheaf.stalk y) = (X.presheaf.germ U y hy).hom.comp (algX p U)) :
    Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk y)) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hy).hom.toAlgebra
  letI : Algebra k Γ(X, U) := (algX p U).toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' h
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  have hft : (algX p U).FiniteType := by
    have h₀ := HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    exact RingHom.FiniteType.comp h₀
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  haveI : Algebra.FiniteType k Γ(X, U) := hft
  haveI : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  haveI : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk y) :=
    Algebra.EssFiniteType.of_isLocalization _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  haveI : Algebra.EssFiniteType k (X.presheaf.stalk y) :=
    Algebra.EssFiniteType.comp k Γ(X, U) (X.presheaf.stalk y)
  haveI : Algebra.EssFiniteType (X.presheaf.stalk y) (IsLocalRing.ResidueField (X.presheaf.stalk y)) :=
    inferInstance
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk y)) :=
    Algebra.EssFiniteType.comp k (X.presheaf.stalk y) _
  exact Algebra.FormallySmooth.of_perfectField

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in

/- English proof (translation)
Introduce `X p n _ y J _ f hf hli`. Use `choose V hyV s hs using fun j => X.presheaf.germ_exist (x := y) (f j)`. Set `O : X.Opens` to `⟨⋂ j, (V j : Set X), isOpen_iInter_of_finite fun j => (V j).isOpen⟩`. Establish `hyO : y ∈ O` using `Set.mem_iInter.2 hyV`. Establish `hOV (j : J) : O ≤ V j` using `fun _ hx => Set.mem_iInter.1 hx j`.

Take `⟨U, x, b, hUO, hyU, hU, hb⟩` from `exists_basis_dFun p n hyO`. Set `z₀ : J → Γ(X, U)` to `fun j => resG X (hUO.trans (hOV j)) (s j)`. Establish `hz₀ (j : J) : (X.presheaf.germ U y hyU).hom (z₀ j) = f j`. Rewrite using `[germ_resG]`. Conclude with `hs j`.

Set `a : J → Fin n → Γ(X, U)` to `fun j l => b.repr (dFun (algX p U) (z₀ j)) l`. Establish `ha (j : J) : dFun (algX p U) (z₀ j) = ∑ l, a j l • dFun (algX p U) (x l)` using `by conv_lhs => rw [← b.sum_repr (dFun (algX p U) (z₀ j))]`. Simplify using `only [hb, a]`. Use `letI iΓ : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra`. Use `letI iA : Algebra ℂ (X.presheaf.stalk y) := ((X.presheaf.germ U y hyU).hom.comp (algX p U)).toAlgebra`.

Use `letI iΓA : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra`. Use `haveI : IsScalarTower ℂ Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI := formallySmooth_residueField (n := n) p hU y hyU rfl`. Establish `hw` using `linearIndependent_tmul_D (k := ℂ) f hf hli`. Set `ρ : Γ(X, U) →+* IsLocalRing.ResidueField (X.presheaf.stalk y)` to `(IsLocalRing.residue (X.presheaf.stalk y)).comp (X.presheaf.germ U y hyU).hom`.

Set `ab : J → Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y)` to `fun j l => ρ (a j l)`. Establish `hab : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) ab`. Set `wx : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) ⊗[X.presheaf.stalk y] Ω[(X.presheaf.stalk y)⁄ℂ]` to `fun l => 1 ⊗ₜ KaehlerDifferential.D ℂ (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (x l))`. Use `LinearIndependent.of_comp (Fintype.linearCombination _ wx) ?_` and prove the remaining obligations. Establish `key : ⇑(Fintype.linearCombination (IsLocalRing.ResidueField (X.presheaf.stalk y)) wx) ∘ ab = fun j => (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗ₜ[X.presheaf.stalk y] KaehlerDifferential.D ℂ (X.presheaf.stalk y) (f j)`.

Use function extensionality and compare the values at `j`. Rewrite using `[Function.comp_apply, Fintype.linearCombination_apply, ← hz₀ j]`. Establish `e1` using `congrArg (KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y)) (ha j)`. Rewrite `e1` using `[map_sum]`. Express the relevant statement in the definitionally equal form `KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y) (KaehlerDifferential.D ℂ Γ(X, U) (z₀ j)) = _ at e1`.

Rewrite `e1` using `[KaehlerDifferential.map_D]`. Express the relevant statement in the definitionally equal form `KaehlerDifferential.D ℂ (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (z₀ j)) = _ at e1`. Rewrite using `[e1, TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Express the relevant statement in the definitionally equal form `_ = 1 ⊗ₜ (a j l • KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y) (KaehlerDifferential.D ℂ Γ(X, U) (x l)))`. Rewrite using `[KaehlerDifferential.map_D, ← algebraMap_smul (X.presheaf.stalk y) (a j l), TensorProduct.tmul_smul, ← algebraMap_smul (IsLocalRing.ResidueField (X.presheaf.stalk y))]`. Both sides reduce to the same expression. Rewrite using `[key]`. Conclude with `hw`.

Take `⟨e, he, hdet⟩` from `GlobalTheory.T.exists_standard_basis_extension_det_ne_zero ab hab`. Set `z : Fin n → Γ(X, U)` to `Function.extend e z₀ x`. Set `c : Matrix (Fin n) (Fin n) Γ(X, U)` to `Matrix.of (Function.extend e a (fun i => Pi.single i (1 : Γ(X, U))))`. Establish `hdz (i : Fin n) : dFun (algX p U) (z i) = ∑ l, c i l • dFun (algX p U) (x l)`. Distinguish the cases in `hi : ∃ j, e j = i`.

Take `⟨j, rfl⟩` from `hi`. Simplify using `only [z, c, Matrix.of_apply, he.extend_apply]`. Conclude with `ha j`. Simplify using `only [z, c, Matrix.of_apply, Function.extend_apply' _ _ _ hi]`. Simplify using `[Pi.single_apply]`.

Establish `hform : dOn p z = c.det • dOn p x` using `dForm_eq_det_smul z x c hdz`. Establish `hρ : ρ c.det ≠ 0`. Establish `hm : c.map ρ = Matrix.of (Function.extend e ab (fun i => Pi.single i (1 : IsLocalRing.ResidueField (X.presheaf.stalk y))))`. Use extensionality with `i l`. Distinguish the cases in `hi : ∃ j, e j = i`.

Take `⟨j, rfl⟩` from `hi`. Simplify using `only [c, ab, Matrix.map_apply, Matrix.of_apply, he.extend_apply]`. Simplify using `only [c, Matrix.map_apply, Matrix.of_apply, Function.extend_apply' _ _ _ hi]`. Distinguish the cases in `hil : l = i`. Substitute `hil` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hil]`. Rewrite using `[RingHom.map_det]`. Conclude with `(congrArg Matrix.det hm).trans_ne hdet`. Establish `hunit : IsUnit ((X.presheaf.germ U y hyU).hom c.det)` using `(IsLocalRing.residue_ne_zero_iff_isUnit _).1 hρ`.

Establish `hyW : y ∈ X.basicOpen c.det` using `(X.mem_basicOpen c.det y hyU).2 hunit`. Establish `hWU : X.basicOpen c.det ≤ U` using `X.basicOpen_le _`. Use `⟨X.basicOpen c.det, hyW, fun i => resG X hWU (z i), e, he, fun j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[germ_resG]`. Simplify using `only [z, he.extend_apply]`.

Conclude with `hz₀ j`. Establish `hx : IsFrame (dOn p x)` using `⟨hU, isFreeGen_dForm x b hb⟩`. Establish `h1` using `hx.res (hU.basicOpen c.det) hWU`. Use `⟨hU.basicOpen c.det, ?_⟩` and prove the remaining obligations. Rewrite using `[← resForm_dOn hWU, hform, resForm_smul]`.

Conclude with `h1.gen.smul_iff.2 (RingedSpace.isUnit_res_basicOpen X.toRingedSpace c.det)`.
-/
theorem exists_adapted_frame : ∀ {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {n : ℕ} [SmoothOfRelativeDimension n p] (y : X) {J : Type}
    [Fintype J] (f : J → X.presheaf.stalk y)
    (hf : ∀ j, f j ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y)),
    LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y))
      (fun j => ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).toCotangent ⟨f j, hf j⟩ :
        IsLocalRing.CotangentSpace (X.presheaf.stalk y))) →
    ∃ (U : X.Opens) (hy : y ∈ U) (z : Fin n → Γ(X, U)) (e : J → Fin n), Function.Injective e ∧
      (∀ j, X.presheaf.germ U y hy (z (e j)) = f j) ∧ IsFrame (dOn p z) := by
  classical
  intro X p n _ y J _ f hf hli

  choose V hyV s hs using fun j => X.presheaf.germ_exist (x := y) (f j)
  let O : X.Opens := ⟨⋂ j, (V j : Set X), isOpen_iInter_of_finite fun j => (V j).isOpen⟩
  have hyO : y ∈ O := Set.mem_iInter.2 hyV
  have hOV (j : J) : O ≤ V j := fun _ hx => Set.mem_iInter.1 hx j
  obtain ⟨U, x, b, hUO, hyU, hU, hb⟩ := exists_basis_dFun p n hyO
  let z₀ : J → Γ(X, U) := fun j => resG X (hUO.trans (hOV j)) (s j)
  have hz₀ (j : J) : (X.presheaf.germ U y hyU).hom (z₀ j) = f j := by
    rw [germ_resG]
    exact hs j

  let a : J → Fin n → Γ(X, U) := fun j l => b.repr (dFun (algX p U) (z₀ j)) l
  have ha (j : J) : dFun (algX p U) (z₀ j) = ∑ l, a j l • dFun (algX p U) (x l) := by
    conv_lhs => rw [← b.sum_repr (dFun (algX p U) (z₀ j))]
    simp only [hb, a]

  letI iΓ : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  letI iA : Algebra ℂ (X.presheaf.stalk y) :=
    ((X.presheaf.germ U y hyU).hom.comp (algX p U)).toAlgebra
  letI iΓA : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  haveI : IsScalarTower ℂ Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := formallySmooth_residueField (n := n) p hU y hyU rfl
  have hw := linearIndependent_tmul_D (k := ℂ) f hf hli
  let ρ : Γ(X, U) →+* IsLocalRing.ResidueField (X.presheaf.stalk y) :=
    (IsLocalRing.residue (X.presheaf.stalk y)).comp (X.presheaf.germ U y hyU).hom
  let ab : J → Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) := fun j l => ρ (a j l)
  have hab : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) ab := by
    let wx : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) ⊗[X.presheaf.stalk y]
        Ω[(X.presheaf.stalk y)⁄ℂ] :=
      fun l => 1 ⊗ₜ KaehlerDifferential.D ℂ (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (x l))
    refine LinearIndependent.of_comp (Fintype.linearCombination _ wx) ?_
    have key : ⇑(Fintype.linearCombination (IsLocalRing.ResidueField (X.presheaf.stalk y)) wx) ∘ ab =
        fun j => (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗ₜ[X.presheaf.stalk y]
          KaehlerDifferential.D ℂ (X.presheaf.stalk y) (f j) := by
      funext j
      rw [Function.comp_apply, Fintype.linearCombination_apply, ← hz₀ j]
      have e1 := congrArg (KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y)) (ha j)
      rw [map_sum] at e1
      change KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D ℂ Γ(X, U) (z₀ j)) = _ at e1
      rw [KaehlerDifferential.map_D] at e1
      change KaehlerDifferential.D ℂ (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (z₀ j)) = _ at e1
      rw [e1, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      change _ = 1 ⊗ₜ (a j l • KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D ℂ Γ(X, U) (x l)))
      rw [KaehlerDifferential.map_D, ← algebraMap_smul (X.presheaf.stalk y) (a j l),
        TensorProduct.tmul_smul, ← algebraMap_smul (IsLocalRing.ResidueField (X.presheaf.stalk y))]
      rfl
    rw [key]
    exact hw

  obtain ⟨e, he, hdet⟩ := GlobalTheory.T.exists_standard_basis_extension_det_ne_zero ab hab
  let z : Fin n → Γ(X, U) := Function.extend e z₀ x
  let c : Matrix (Fin n) (Fin n) Γ(X, U) :=
    Matrix.of (Function.extend e a (fun i => Pi.single i (1 : Γ(X, U))))
  have hdz (i : Fin n) : dFun (algX p U) (z i) = ∑ l, c i l • dFun (algX p U) (x l) := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      simp only [z, c, Matrix.of_apply, he.extend_apply]
      exact ha j
    · simp only [z, c, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
      simp [Pi.single_apply]
  have hform : dOn p z = c.det • dOn p x := dForm_eq_det_smul z x c hdz
  have hρ : ρ c.det ≠ 0 := by
    have hm : c.map ρ = Matrix.of (Function.extend e ab
        (fun i => Pi.single i (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)))) := by
      ext i l
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        simp only [c, ab, Matrix.map_apply, Matrix.of_apply, he.extend_apply]
      · simp only [c, Matrix.map_apply, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
        by_cases hil : l = i
        · subst hil
          simp
        · simp [Pi.single_apply, hil]
    rw [RingHom.map_det]
    exact (congrArg Matrix.det hm).trans_ne hdet
  have hunit : IsUnit ((X.presheaf.germ U y hyU).hom c.det) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hρ
  have hyW : y ∈ X.basicOpen c.det := (X.mem_basicOpen c.det y hyU).2 hunit
  have hWU : X.basicOpen c.det ≤ U := X.basicOpen_le _
  refine ⟨X.basicOpen c.det, hyW, fun i => resG X hWU (z i), e, he, fun j => ?_, ?_⟩
  · rw [germ_resG]
    simp only [z, he.extend_apply]
    exact hz₀ j
  · have hx : IsFrame (dOn p x) := ⟨hU, isFreeGen_dForm x b hb⟩
    have h1 := hx.res (hU.basicOpen c.det) hWU
    refine ⟨hU.basicOpen c.det, ?_⟩
    rw [← resForm_dOn hWU, hform, resForm_smul]
    exact h1.gen.smul_iff.2 (RingedSpace.isUnit_res_basicOpen X.toRingedSpace c.det)

end GlobalTheory.AdaptedFrame
