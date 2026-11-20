import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureOfCoheightField
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtVert

/- English proof (translation)
Use `⟨fun y => ?_⟩` and prove the remaining obligations. Set `f : κ →+* ℂ` to `(Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp (y.1.appTop.hom.comp (algebraMap κ Γ(Z, ⊤)))`. Establish `: CharZero κ` using `f.charZero`. Conclude with `not_finite κ`.
-/
theorem isEmpty_cxPts {k : Type} [CommRing k] {Z : Scheme.{0}} (q : Z ⟶ Sp k) (σ : k →+* ℂ) (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] : IsEmpty (CxPts q σ) := by
  refine ⟨fun y => ?_⟩
  let f : κ →+* ℂ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp (y.1.appTop.hom.comp (algebraMap κ Γ(Z, ⊤)))
  have : CharZero κ := f.charZero
  exact not_finite κ

/- English proof (translation)
Establish `h0 : ∀ (L' : HermLB q), L'.archInt M e hr = 0`. Introduce `L'`. Use `finsum_eq_zero_of_forall_eq_zero fun σ => ?_` and prove the remaining obligations. Use `h σ` as an intermediate fact. Simplify using `[Weight.chernInt, MeasureTheory.integral_of_isEmpty]`.

Simplify using `[mixArch, FibreProj.pol, h0]`.
-/
theorem mixArch_eq_zero {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (h : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) {e : ℕ} (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : mixArch L M hr = 0 := by
  have h0 : ∀ (L' : HermLB q), L'.archInt M e hr = 0 := by
    intro L'
    refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
    have := h σ
    simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]
  simp [mixArch, FibreProj.pol, h0]

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

/- English proof (translation)
Establish `: IsProper (strHom κ Z)` using `(isProper_and_exists_isAmpleLB_of_isProjOver hp).1`. Establish `h1 : (strHom κ Z).appTop.hom.FiniteType` using `HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) |>.1 inferInstance`. Establish `h2 : (algebraMap κ Γ(Z, ⊤)).FiniteType`. Establish `e : algebraMap κ Γ(Z, ⊤) = (strHom κ Z).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom` using `RingHom.ext (algebraMap_eq_strHom κ Z)`. Rewrite using `[e]`.

Conclude with `h1.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)`. Establish `hft : Algebra.FiniteType κ Γ(Z, ⊤)` using `RingHom.finiteType_algebraMap.1 h2`. Use `letI : Algebra κ (Z.residueField (genericPoint Z)) := (φ.comp (algebraMap κ Γ(Z, ⊤))).toAlgebra`. Set `ψ : Γ(Z, ⊤) →ₐ[κ] Z.residueField (genericPoint Z)` to `{ φ with commutes' := fun _ => rfl }`. Establish `: Algebra.FiniteType κ (Z.residueField (genericPoint Z))` using `Algebra.FiniteType.of_surjective ψ hφ.2`.

Establish `: Module.Finite κ (Z.residueField (genericPoint Z))` using `finite_of_finite_type_of_isJacobsonRing _ _`. Establish `: Finite (Z.residueField (genericPoint Z))` using `Module.finite_of_finite κ`. Conclude with `Finite.of_injective φ hφ.1`.
-/
theorem finite_Γ {Z : Scheme.{0}} [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] [IsAffine Z]
    (hp : IsProjOver (strHom κ Z)) (φ : Γ(Z, ⊤) →+* Z.residueField (genericPoint Z)) (hφ : Function.Bijective φ) :
    Finite Γ(Z, ⊤) := by
  have : IsProper (strHom κ Z) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have h1 : (strHom κ Z).appTop.hom.FiniteType :=
    HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) |>.1 inferInstance
  have h2 : (algebraMap κ Γ(Z, ⊤)).FiniteType := by
    have e : algebraMap κ Γ(Z, ⊤) = (strHom κ Z).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom :=
      RingHom.ext (algebraMap_eq_strHom κ Z)
    rw [e]
    exact h1.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have hft : Algebra.FiniteType κ Γ(Z, ⊤) := RingHom.finiteType_algebraMap.1 h2
  letI : Algebra κ (Z.residueField (genericPoint Z)) := (φ.comp (algebraMap κ Γ(Z, ⊤))).toAlgebra
  let ψ : Γ(Z, ⊤) →ₐ[κ] Z.residueField (genericPoint Z) := { φ with commutes' := fun _ => rfl }
  have : Algebra.FiniteType κ (Z.residueField (genericPoint Z)) := Algebra.FiniteType.of_surjective ψ hφ.2
  have : Module.Finite κ (Z.residueField (genericPoint Z)) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Finite (Z.residueField (genericPoint Z)) := Module.finite_of_finite κ
  exact Finite.of_injective φ hφ.1

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

/- English proof (translation)
Establish `h₁` using `(genericPoint_spec Z).image i.continuous`. Rewrite `h₁` using `[Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq]`. Rewrite using `[HasDim, topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding h₁.def.symm]`.
-/
theorem hasDim_iff {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (d : ℕ) :
    HasDim (i (genericPoint Z)) d ↔ topologicalKrullDim Z = d := by
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  rw [HasDim, topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding h₁.def.symm]

/- English proof (translation)
Establish `hu (w : Z) : w = genericPoint Z`. Use `Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 0 from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩` as an intermediate fact. Conclude with `IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)`. Establish `hZ : ({genericPoint Z} : Set Z) = Set.univ` using `Set.eq_univ_of_forall hu`. Establish `hc : IsClosed ({genericPoint Z} : Set Z)` using `hZ ▸ isClosed_univ`.

Use `isClosed_singleton_iff_isClosedImmersion.1 hc` as an intermediate fact. Establish `: Surjective (Z.fromSpecResidueField (genericPoint Z))` using `⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩`. Use `isIso_of_isClosedImmersion_of_surjective (Z.fromSpecResidueField (genericPoint Z))` as an intermediate fact. Establish `: IsAffine Z` using `.of_isIso (inv (Z.fromSpecResidueField (genericPoint Z)))`. Establish `: IsIso (Z.fromSpecResidueField (genericPoint Z)).appTop` using `inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))`.

Establish `b₁ : Function.Bijective (i.residueFieldMap (genericPoint Z))`. Use `⟨RingHom.injective _, fun a => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Z.residue_surjective _ a`. Take `⟨b, rfl⟩` from `i.stalkMap_surjective _ a`. Conclude with `⟨X.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩`.

Establish `b₂ : Function.Bijective ((Z.fromSpecResidueField (genericPoint Z)).appTop ≫ (Scheme.ΓSpecIso (Z.residueField (genericPoint Z))).hom)` using `ConcreteCategory.bijective_of_isIso _`. Establish `e : Γ(Z, ⊤) ≃ X.residueField (i (genericPoint Z))` using `(Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm`. Establish `: Finite Γ(Z, ⊤)` using `finite_Γ κ hp _ b₂`. Rewrite using `[← Nat.card_congr e, chi_structureModule_of_isAffine, Module.natCard_eq_pow_finrank (K := κ)]`. Simplify using the standard rewrite rules.
-/
theorem dim_zero {X : Scheme.{0}} {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] (h0 : topologicalKrullDim Z = (0 : ℕ))
    (hp : IsProjOver (strHom κ Z)) :
    Real.log (Nat.card (X.residueField (i (genericPoint Z)))) = chi κ (structureModule Z) * Real.log (Nat.card κ) := by
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)
  have hZ : ({genericPoint Z} : Set Z) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint Z} : Set Z) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (Z.fromSpecResidueField (genericPoint Z)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (Z.fromSpecResidueField (genericPoint Z))
  have : IsAffine Z := .of_isIso (inv (Z.fromSpecResidueField (genericPoint Z)))
  have : IsIso (Z.fromSpecResidueField (genericPoint Z)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (i.residueFieldMap (genericPoint Z)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := Z.residue_surjective _ a
    obtain ⟨b, rfl⟩ := i.stalkMap_surjective _ a
    exact ⟨X.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((Z.fromSpecResidueField (genericPoint Z)).appTop ≫
      (Scheme.ΓSpecIso (Z.residueField (genericPoint Z))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(Z, ⊤) ≃ X.residueField (i (genericPoint Z)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  have : Finite Γ(Z, ⊤) := finite_Γ κ hp _ b₂
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, Module.natCard_eq_pow_finrank (K := κ)]
  simp

/- English proof (translation)
Use `hX.finite` as an intermediate fact. Take `⟨hpr, H, hH⟩` from `(isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver`. Establish `: IsFinite (spMap (Int.castRingHom k))`. Rewrite using `[spMap, IsFinite.SpecMap_iff]`. Conclude with `(RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance`.

Establish `e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k)` using `specZIsTerminal.hom_ext _ _`. Establish `: IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ))` using `by rw [e]; infer_instance`. Establish `hpr' : IsProper (strHom κ Z)` using `IsProper.of_comp _ (spMap (Int.castRingHom κ))`. Conclude with `(isProjOver_iff_isProper_and_exists_isAmpleLB (strHom κ Z)).2 ⟨hpr', _, hH.pull_of_isClosedImmersion i⟩`.
-/
theorem isProjOver_strHom {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (hX : IsAmb p) {Z : Scheme.{0}}
    (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)] : IsProjOver (strHom κ Z) := by
  have := hX.finite
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have hpr' : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  exact (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom κ Z)).2 ⟨hpr', _, hH.pull_of_isClosedImmersion i⟩

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

/- English proof (translation)
Introduce `k _ X p hA m T hT N d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `_ Z i _ _ κ _ _ _ hd`. Rewrite using `[hT.zero _ _ ((hasDim_iff i 0).2 hd), dim_zero i κ hd (isProjOver_strHom hA i κ), topSelf_def, interNum_of_isEmpty]`.

Consider the case `succ e ih`. Introduce `hm Z i _ _ κ _ _ _ hd`. Establish `hZa : IsAmb (i ≫ p)` using `hA.sub i`. Establish `: IsNoetherian Z` using `hZa.isNoetherian`. Establish `hp` using `isProjOver_strHom hA i κ`.

Establish `: IsProper (strHom κ Z)` using `(isProper_and_exists_isAmpleLB_of_isProjOver hp).1`. Take `⟨r, hr⟩` from `exists_isRatSec (N.restr i).isLB`. Establish `hL : (N.B.pull i).IsLB` using `(N.restr i).isLB`. Establish `hrec` using `hT.recur Z (i ≫ p) i rfl e hm hd N (fun _ => N) (N.restr i) (fun _ => N.restr i) (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr`. Establish `ec : (Fin.cons N (fun _ => N) : Fin (e + 1) → HermLB p) = fun _ => N`.

Use function extensionality and compare the values at `(Fin.cases rfl fun _ => rfl)`. Rewrite `hrec` using `[ec]`. Rewrite using `[hrec, recVal, mixArch_eq_zero (fun σ => isEmpty_cxPts (i ≫ p) σ κ), sub_zero]`. Establish `key` using `GlobalTheory.ratSec_cycle_formula κ Z hp e hd.le (N.B.pull i) hL (fun _ => N.B.pull i) (fun _ => hL) r hr`. Establish `ec' : (Fin.cons (N.B.pull i) (fun _ => N.B.pull i) : Fin (e + 1) → LB Z) = fun _ => N.B.pull i`.

Use function extensionality and compare the values at `(Fin.cases rfl fun _ => rfl)`. Rewrite `key` using `[ec', ← topSelf_def]`. Establish `hfin : Function.HasFiniteSupport fun w => (divOfRatSec hL hr).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) fun _ : Fin e => N.B.pull i` using `(CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)`. Rewrite using `[key]`. Establish `em` using `(AddMonoidHom.mulRight (Real.log (Nat.card κ))).comp (Int.castAddHom ℝ) |>.map_finsum hfin`.

Use `.trans (finsum_congr fun z => ?_) em.symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((divOfRatSec hL hr).mult z : ℝ) * _ = (((divOfRatSec hL hr).mult z * _ : ℤ) : ℝ) * _`. Distinguish the cases in `hz : (divOfRatSec hL hr).mult z = 0`. Simplify using `[hz]`. Rewrite using `[Int.cast_mul, mul_assoc]`.

Use `congrArg _ ?_` and prove the remaining obligations. Establish `hdim` using `VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Z) hd (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)`. Take `⟨W, j, _, _, rfl⟩` from `exists_isClosedImmersion_genericPoint z`. Establish `hrange : Set.range j = closure {j (genericPoint W)}`. Rewrite using `[← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]`.

Use `letI := algebraΓAlong κ j`. Establish `hW : topologicalKrullDim W = e` using `(topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim`. Rewrite using `[← Scheme.Hom.comp_apply, ih (by omega) W (j ≫ i) κ hW, InterModel.interNumRed_eq_interNumOn _ j _ hrange, interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun _ => hL), topSelf_def]`. Use `congr 2`. Use `interNum_congr_cls κ _ (fun _ => LB.isLB_pull N.isLB _) (fun _ => LB.isLB_pull hL _) fun _ => ?_` and prove the remaining obligations.

Rewrite using `[CechPic.cls_pull hL, CechPic.cls_pull N.isLB, CechPic.cls_pull N.isLB, CechPic.pull_comp]`.
-/
theorem mixHt_pow_eq_topSelf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ (m : ℕ) T, IsMix p m T → ∀ (N : HermLB p) (d : ℕ), d ≤ m → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = d → T d (fun _ => N) (i (genericPoint Z)) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ) := by
  intro k _ X p hA m T hT N d
  induction d with
  | zero =>
    intro _ Z i _ _ κ _ _ _ hd
    rw [hT.zero _ _ ((hasDim_iff i 0).2 hd), dim_zero i κ hd (isProjOver_strHom hA i κ), topSelf_def,
      interNum_of_isEmpty]
  | succ e ih =>
    intro hm Z i _ _ κ _ _ _ hd
    have hZa : IsAmb (i ≫ p) := hA.sub i
    have : IsNoetherian Z := hZa.isNoetherian
    have hp := isProjOver_strHom hA i κ
    have : IsProper (strHom κ Z) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
    obtain ⟨r, hr⟩ := exists_isRatSec (N.restr i).isLB
    have hL : (N.B.pull i).IsLB := (N.restr i).isLB
    have hrec := hT.recur Z (i ≫ p) i rfl e hm hd N (fun _ => N) (N.restr i) (fun _ => N.restr i)
      (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr
    have ec : (Fin.cons N (fun _ => N) : Fin (e + 1) → HermLB p) = fun _ => N :=
      funext (Fin.cases rfl fun _ => rfl)
    rw [ec] at hrec
    rw [hrec, recVal, mixArch_eq_zero (fun σ => isEmpty_cxPts (i ≫ p) σ κ), sub_zero]
    have key := GlobalTheory.ratSec_cycle_formula κ Z hp e hd.le (N.B.pull i) hL (fun _ => N.B.pull i) (fun _ => hL) r hr
    have ec' : (Fin.cons (N.B.pull i) (fun _ => N.B.pull i) : Fin (e + 1) → LB Z) = fun _ => N.B.pull i :=
      funext (Fin.cases rfl fun _ => rfl)
    rw [ec', ← topSelf_def] at key
    have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hL hr).mult w *
        interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) fun _ : Fin e => N.B.pull i :=
      (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
    rw [key]
    have em := (AddMonoidHom.mulRight (Real.log (Nat.card κ))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
    refine .trans (finsum_congr fun z => ?_) em.symm
    change ((divOfRatSec hL hr).mult z : ℝ) * _ = (((divOfRatSec hL hr).mult z * _ : ℤ) : ℝ) * _
    by_cases hz : (divOfRatSec hL hr).mult z = 0
    · simp [hz]
    rw [Int.cast_mul, mul_assoc]
    refine congrArg _ ?_
    have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Z) hd
      (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
    obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    have hrange : Set.range j = closure {j (genericPoint W)} := by
      rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
    letI := algebraΓAlong κ j
    have hW : topologicalKrullDim W = e :=
      (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
    rw [← Scheme.Hom.comp_apply, ih (by omega) W (j ≫ i) κ hW, InterModel.interNumRed_eq_interNumOn _ j _ hrange,
      interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun _ => hL), topSelf_def]
    congr 2
    refine interNum_congr_cls κ _ (fun _ => LB.isLB_pull N.isLB _) (fun _ => LB.isLB_pull hL _) fun _ => ?_
    rw [CechPic.cls_pull hL, CechPic.cls_pull N.isLB, CechPic.cls_pull N.isLB, CechPic.pull_comp]

end GlobalTheory.MixHtVert
