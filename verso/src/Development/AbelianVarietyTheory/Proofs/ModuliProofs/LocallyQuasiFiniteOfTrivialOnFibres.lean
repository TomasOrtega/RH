import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.AmpleFibre

open TopologicalSpace GlobalTheory.MulFinite

/- English proof (translation)
Set `V : L.ι → Z.Opens` to `fun j => r ⁻¹ᵁ L.U j`. Establish `l₁ : ∀ j, V j ≤ r ⁻¹ᵁ LB.wchart L (K` using `Fin N) (fun _ => 𝟙 X) (fun _ => j) := fun j z hz => Set.mem_iInter.2 fun _ => hz`. Establish `l₂ : ∀ j, V j ≤ LB.wchart L (K` using `PUnit) (fun _ => r) (fun _ => j) := fun j z hz => Set.mem_iInter.2 fun _ => hz`. Take `⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) = gs r z (LB.wchart L (K` from `Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j)) * ((gm (𝟙 Z) z (LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j)) (t.s (fun _ => j)))⁻¹).val ^ N := by`. Use `⟨fun j => (r.appLE _ _ (l₁ j)).hom (s.f (fun _ => j)) * (Z.presheaf.map (homOfLE (l₂ j)).op).hom ((t.s (fun _ => j))⁻¹).val ^ N, fun j z hz => ?_⟩` and prove the remaining obligations.

Use `(gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) (gs_appLE r z _ _ _ hz _) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))` and prove the remaining obligations. Use `congrArg (· ^ N) ((gs_res (𝟙 Z) z _ hz _).trans ?_)` and prove the remaining obligations. Conclude with `(gs_unit (𝟙 Z) z _ (l₂ j hz) _).trans (congrArg Units.val (map_inv _ _))`. Establish `hcov : (⊤ : Z.Opens) ≤ iSup V` using `fun z _ => by`. Take `⟨j, hj⟩` from `exists_chart hL (r z)`.

Conclude with `Opens.mem_iSup.2 ⟨j, hj⟩`. Take `⟨a, ha, -⟩` from `Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by`. Use `(gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)` and prove the remaining obligations. Rewrite using `[hu j z hz.1, hu j' z hz.2, sec_trans s r z (l₁ j hz.1) (l₁ j' hz.2), gen_trans ht (𝟙 Z) z (l₂ j hz.1) (l₂ j' hz.2)]`. Establish `t₁ : trF (L` using `L) (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1) r z (fun _ => j) (fun _ => j') = gm r z (L.U j ⊓ L.U j') (L.g j j') ^ N := by simp [trF]`.

Establish `t₂ : trF (L` using `L) (K := PUnit) (fun _ => r) (fun _ => 1) (𝟙 Z) z (fun _ => j) (fun _ => j') = gm r z (L.U j ⊓ L.U j') (L.g j j') := by simp [trF]`. Rewrite using `[t₁, t₂]`. Simplify `pow_aux _ _ _ 1 N)` using `only [pow_one]`. Use `⟨a, ?_⟩` and prove the remaining obligations. Use extensionality with `z`.

Take `⟨j, hj⟩` from `exists_chart hL (r z)`. Establish `k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j)` using `(gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))`. Establish `k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔ IsUnit (gs r z (LB.wchart L (K` using `Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j))) := by`. Use `(isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_` and prove the remaining obligations. Rewrite using `[k₁, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units]`.

Use `k₂.trans ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Conclude with `Opens.mem_iSup.2 ⟨fun _ => j, (isUnit_gs r z _ (l₁ j hj) _).1 h⟩`. Take `⟨k, hk⟩` from `Opens.mem_iSup.1 (show r z ∈ Out.nonzeroLocus s from h)`. Establish `hk' : r z ∈ LB.wchart L (K` using `Fin N) (fun _ => 𝟙 X) k := X.basicOpen_le _ hk`. Rewrite using `[sec_trans s r z (l₁ j hj) hk']`.

Conclude with `(Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)`.
-/
theorem exists_fn {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (N : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1))) (r : Z ⟶ X)
    (t : (L.pull r).Gen) (ht : t.IsGen) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ Out.nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => r ⁻¹ᵁ L.U j
  have l₁ : ∀ j, V j ≤ r ⁻¹ᵁ LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  have l₂ : ∀ j, V j ≤ LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j)) *
        ((gm (𝟙 Z) z (LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j)) (t.s (fun _ => j)))⁻¹).val ^ N := by
    refine ⟨fun j => (r.appLE _ _ (l₁ j)).hom (s.f (fun _ => j)) *
      (Z.presheaf.map (homOfLE (l₂ j)).op).hom ((t.s (fun _ => j))⁻¹).val ^ N, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) (gs_appLE r z _ _ _ hz _)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))
    refine congrArg (· ^ N) ((gs_res (𝟙 Z) z _ hz _).trans ?_)
    exact (gs_unit (𝟙 Z) z _ (l₂ j hz) _).trans (congrArg Units.val (map_inv _ _))
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart hL (r z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_trans s r z (l₁ j hz.1) (l₁ j' hz.2),
        gen_trans ht (𝟙 Z) z (l₂ j hz.1) (l₂ j' hz.2)]
      have t₁ : trF (L := L) (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1) r z (fun _ => j) (fun _ => j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') ^ N := by simp [trF]
      have t₂ : trF (L := L) (K := PUnit) (fun _ => r) (fun _ => 1) (𝟙 Z) z (fun _ => j) (fun _ => j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') := by simp [trF]
      rw [t₁, t₂]
      simpa only [pow_one] using pow_aux _ _ _ 1 N)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := exists_chart hL (r z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔
      IsUnit (gs r z (LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j))) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨fun _ => j, (isUnit_gs r z _ (l₁ j hj) _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ Out.nonzeroLocus s from h)
    have hk' : r z ∈ LB.wchart L (K := Fin N) (fun _ => 𝟙 X) k := X.basicOpen_le _ hk
    rw [sec_trans s r z (l₁ j hj) hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

/- English proof (translation)
Use `⟨fun U _ => ?_⟩` and prove the remaining obligations. Establish `: Subsingleton ↥(Sp k)` using `inferInstanceAs (Subsingleton (PrimeSpectrum k))`. Distinguish the cases in `h : ∃ p, p ∈ y ⁻¹ᵁ U`. Take `⟨p, hp⟩` from `h`. Establish `: y ⁻¹ᵁ U = ⊤` using `top_unique fun x _ => by rwa [Subsingleton.elim x p]`.

Rewrite using `[this]`. Conclude with `isAffineOpen_top _`. Establish `: y ⁻¹ᵁ U = ⊥` using `bot_unique fun x hx => (h ⟨x, hx⟩).elim`. Rewrite using `[this]`. Conclude with `isAffineOpen_bot _`.
-/
theorem isAffineHom_of_field {k : Type} [Field k] {Y : Scheme.{0}} (y : Sp k ⟶ Y) : IsAffineHom y := by
  refine ⟨fun U _ => ?_⟩
  have : Subsingleton ↥(Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  by_cases h : ∃ p, p ∈ y ⁻¹ᵁ U
  · obtain ⟨p, hp⟩ := h
    have : y ⁻¹ᵁ U = ⊤ := top_unique fun x _ => by rwa [Subsingleton.elim x p]
    rw [this]; exact isAffineOpen_top _
  · have : y ⁻¹ᵁ U = ⊥ := bot_unique fun x hx => (h ⟨x, hx⟩).elim
    rw [this]; exact isAffineOpen_bot _

/- English proof (translation)
Set `I` to `Scheme.IdealSheafData.vanishingIdeal (X := P) ⟨Z, hc⟩`. Establish `hr : Set.range I.subschemeι = Z`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι]`. Simplify using `[I]`. Establish `: IsReduced I.subscheme` using `ReducedSubgroup.isReduced_subscheme_vanishingIdeal _`.

Establish `: IrreducibleSpace I.subscheme`. Establish `e` using `I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph`. Establish `: IrreducibleSpace (Set.range I.subschemeι)`. Rewrite using `[hr]`. Conclude with `Subtype.irreducibleSpace hi`.

Conclude with `e.irreducibleSpace_iff.2 this`. Conclude with `⟨I.subscheme, isIntegral_of_irreducibleSpace_of_isReduced _, I.subschemeι, inferInstance, hr⟩`.
-/
theorem exists_integral_closedImmersion {P : Scheme.{0}} (Z : Set P) (hc : IsClosed Z)
    (hi : IsIrreducible Z) :
    ∃ (C : Scheme.{0}) (_ : IsIntegral C) (i : C ⟶ P), IsClosedImmersion i ∧ Set.range i = Z := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := P) ⟨Z, hc⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace I.subscheme := by
    have e := I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
    have : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [hr]; exact Subtype.irreducibleSpace hi
    exact e.irreducibleSpace_iff.2 this
  exact ⟨I.subscheme, isIntegral_of_irreducibleSpace_of_isReduced _, I.subschemeι, inferInstance, hr⟩

/- English proof (translation)
Introduce `X Y f A hf hA hs ht`. Use `LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_` and prove the remaining obligations. Set `Ω` to `AlgebraicClosure (Y.residueField y)`. Set `y' : Sp Ω ⟶ Y` to `Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y`. Establish `hy : y ∈ Set.range y'`.

Take `⟨z⟩ : Nonempty ↥(Spec (.of Ω))` from `inferInstance`. Conclude with `⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩`. Use `clear_value y'`. Establish `hy'` using `isAffineHom_of_field y'`. Establish `h₁ : IsAffineHom (pullback.fst f y')` using `MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0}) (IsPullback.of_hasPullback f y').flip hy'`.

Establish `h₂ : IsLocallyNoetherian (pullback f y')` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f y')`. Establish `h₃ : CompactSpace ↥(pullback f y')` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd f y')`. Establish `h₄ : IsNoetherian (pullback f y')` using `{}`. Establish `hP : (Set.univ : Set ↥(pullback f y')).Finite`. Rewrite using `[← sUnion_irreducibleComponents]`.

Use `NoetherianSpace.finite_irreducibleComponents.sUnion fun Z hZ => ?_` and prove the remaining obligations. Take `⟨C, _, i, hi, rfl⟩` from `exists_integral_closedImmersion Z (isClosed_of_mem_irreducibleComponents Z hZ) hZ.1`. Take `⟨t, ht⟩` from `ht Ω y' C i inferInstance`. Use `choose d s hx ha using hs`. Use `choose a ha' using fun x => exists_fn A hA (d x) (s x) _ t ht`.

Establish `: LocallyQuasiFinite (i ≫ pullback.snd f y')`. Use `locallyQuasiFinite_of_cover (K := Ω) _ a (top_unique fun c _ => ?_) fun x => ?_` and prove the remaining obligations. Use `Opens.mem_iSup.2 ⟨(i ≫ pullback.fst f y') c, ?_⟩` and prove the remaining obligations. Rewrite using `[ha']`. Conclude with `hx _`.

Rewrite using `[ha']`. Conclude with `(ha x).preimage _`. Establish `: Subsingleton ↥(Sp Ω)` using `inferInstanceAs (Subsingleton (PrimeSpectrum Ω))`. Take `⟨p⟩ : Nonempty ↥(Sp Ω)` from `inferInstance`. Establish `hC : Finite C` using `Set.finite_univ_iff.1 (((i ≫ pullback.snd f y').finite_preimage_singleton p).subset fun c _ => Subsingleton.elim _ _)`.

Conclude with `Set.finite_range i`. Use `Set.finite_univ_iff.1 hP` as an intermediate fact. Use `(Set.finite_range (pullback.fst f y')).subset ?_` and prove the remaining obligations. Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `Set.preimage_mono (Set.singleton_subset_iff.mpr hy)`.
-/
theorem locallyQuasiFinite_of_trivial_on_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (A : LB X), IsProper f → A.IsLB → (∀ x : X, ∃ (d : ℕ) (s : LB.Sec (LB.LinComb A (K := Fin d) (fun _ => 𝟙 X) (fun _ => 1))), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (C : Scheme.{0}) [IsIntegral C] (i : C ⟶ pullback f y), IsFinite i → ∃ t : (A.pull (i ≫ pullback.fst f y)).Gen, t.IsGen) → LocallyQuasiFinite f := by
  intro X Y f A hf hA hs ht
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  let Ω := AlgebraicClosure (Y.residueField y)
  let y' : Sp Ω ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y
  have hy : y ∈ Set.range y' := by
    obtain ⟨z⟩ : Nonempty ↥(Spec (.of Ω)) := inferInstance
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩
  clear_value y'
  have hy' := isAffineHom_of_field y'
  have h₁ : IsAffineHom (pullback.fst f y') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback f y').flip hy'
  have h₂ : IsLocallyNoetherian (pullback f y') :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f y')
  have h₃ : CompactSpace ↥(pullback f y') := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f y')
  have h₄ : IsNoetherian (pullback f y') := {}
  have hP : (Set.univ : Set ↥(pullback f y')).Finite := by
    rw [← sUnion_irreducibleComponents]
    refine NoetherianSpace.finite_irreducibleComponents.sUnion fun Z hZ => ?_
    obtain ⟨C, _, i, hi, rfl⟩ := exists_integral_closedImmersion Z
      (isClosed_of_mem_irreducibleComponents Z hZ) hZ.1
    obtain ⟨t, ht⟩ := ht Ω y' C i inferInstance
    choose d s hx ha using hs
    choose a ha' using fun x => exists_fn A hA (d x) (s x) _ t ht
    have : LocallyQuasiFinite (i ≫ pullback.snd f y') := by
      refine locallyQuasiFinite_of_cover (K := Ω) _ a (top_unique fun c _ => ?_) fun x => ?_
      · refine Opens.mem_iSup.2 ⟨(i ≫ pullback.fst f y') c, ?_⟩
        rw [ha']
        exact hx _
      · rw [ha']
        exact (ha x).preimage _
    have : Subsingleton ↥(Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    obtain ⟨p⟩ : Nonempty ↥(Sp Ω) := inferInstance
    have hC : Finite C := Set.finite_univ_iff.1
      (((i ≫ pullback.snd f y').finite_preimage_singleton p).subset fun c _ => Subsingleton.elim _ _)
    exact Set.finite_range i
  have := Set.finite_univ_iff.1 hP
  refine (Set.finite_range (pullback.fst f y')).subset ?_
  rw [Scheme.Pullback.range_fst]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hy)

end GlobalTheory.AmpleFibre
