import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionApplyEqOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFlatFibresDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericFlatnessScheme

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.IntDiv

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hξ, -⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ`. Establish `: Nonempty U` using `⟨⟨_, hξ⟩⟩`. Establish `: IsNoetherianRing Γ(Y, U)` using `IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Set `b : Sp Γ(Y, U) ⟶ Y` to `hU.fromSpec`. Establish `: IsOpenImmersion b` using `IsAffineOpen.isOpenImmersion_fromSpec hU`.

Take `⟨r, hr, H⟩` from `generic_flatness_scheme Γ(Y, U) _ (pullback.snd f b) inferInstance inferInstance`. Set `φ` to `algebraMap Γ(Y, U) (Localization.Away r)`. Establish `h1` using `H _ φ (IsLocalization.Away.algebraMap_isUnit r)`. Establish `: IsOpenImmersion (spMap φ)` using `IsOpenImmersion.of_isLocalization r`. Set `j` to `pullback.fst (pullback.snd f b) (spMap φ) ≫ pullback.fst f b`.

Establish `hj : j ≫ f = pullback.snd (pullback.snd f b) (spMap φ) ≫ spMap φ ≫ b`. Simplify using `only [j, Category.assoc, pullback.condition, pullback.condition_assoc]`. Establish `h2 : Flat (j ≫ f)` using `by rw [hj]; infer_instance`. Establish `hd : IsDomain (Localization.Away r)` using `IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)`. Use `⟨j.opensRange, ?_, ?_⟩` and prove the remaining obligations.

Establish `h3 : genericPoint Y ∈ Set.range (spMap φ ≫ b)` using `((genericPoint_spec Y).mem_open_set_iff (spMap φ ≫ b).opensRange.2).mpr ⟨_, trivial, (⊥ : PrimeSpectrum (Localization.Away r)), rfl⟩`. Take `⟨z, hz⟩` from `h3`. Take `⟨w, -, hw⟩` from `Scheme.Pullback.exists_preimage_pullback (f := f) (g := b) (genericPoint X) (spMap φ z) (hf.trans (hz.symm.trans (Scheme.Hom.comp_apply _ _ _)))`. Take `⟨v, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f b) (g := spMap φ) w z hw`. Conclude with `⟨_, v, rfl⟩`.

Introduce and unpack `_ ⟨v, rfl⟩`. Establish `h4` using `Flat.stalkMap (j ≫ f) v`. Rewrite `h4` using `[Scheme.Hom.stalkMap_comp]`. Conclude with `(RingHom.Flat.respectsIso.cancel_right_isIso (f.stalkMap (j v)) (j.stalkMap v)).mp h4`.
-/
theorem exists_open_flat {X Y : Scheme.{0}} [IrreducibleSpace X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f (genericPoint X) = genericPoint Y) :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ ∀ x ∈ W, (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let b : Sp Γ(Y, U) ⟶ Y := hU.fromSpec
  have : IsOpenImmersion b := IsAffineOpen.isOpenImmersion_fromSpec hU
  obtain ⟨r, hr, H⟩ := generic_flatness_scheme Γ(Y, U) _ (pullback.snd f b) inferInstance inferInstance
  let φ := algebraMap Γ(Y, U) (Localization.Away r)
  have h1 := H _ φ (IsLocalization.Away.algebraMap_isUnit r)
  have : IsOpenImmersion (spMap φ) := IsOpenImmersion.of_isLocalization r
  let j := pullback.fst (pullback.snd f b) (spMap φ) ≫ pullback.fst f b
  have hj : j ≫ f = pullback.snd (pullback.snd f b) (spMap φ) ≫ spMap φ ≫ b := by
    simp only [j, Category.assoc, pullback.condition, pullback.condition_assoc]
  have h2 : Flat (j ≫ f) := by rw [hj]; infer_instance
  have hd : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  refine ⟨j.opensRange, ?_, ?_⟩
  · have h3 : genericPoint Y ∈ Set.range (spMap φ ≫ b) :=
      ((genericPoint_spec Y).mem_open_set_iff (spMap φ ≫ b).opensRange.2).mpr
        ⟨_, trivial, (⊥ : PrimeSpectrum (Localization.Away r)), rfl⟩
    obtain ⟨z, hz⟩ := h3
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := b) (genericPoint X)
      (spMap φ z) (hf.trans (hz.symm.trans (Scheme.Hom.comp_apply _ _ _)))
    obtain ⟨v, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f b) (g := spMap φ) w z hw
    exact ⟨_, v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    have h4 := Flat.stalkMap (j ≫ f) v
    rw [Scheme.Hom.stalkMap_comp] at h4
    exact (RingHom.Flat.respectsIso.cancel_right_isIso (f.stalkMap (j v)) (j.stalkMap v)).mp h4

open UnramifiedEndFlat in

/- English proof (translation)
Use `LocallyOfFiniteType.jacobsonSpace G.hom` as an intermediate fact. Establish `: IsLocallyNoetherian G.left` using `LocallyOfFiniteType.isLocallyNoetherian G.hom`. Establish `: LocallyOfFiniteType (φ.left ≫ G.hom)` using `by rw [Over.w φ]; infer_instance`. Establish `: LocallyOfFiniteType φ.left` using `locallyOfFiniteType_of_comp _ G.hom`. Set `o : G.left` to `η[G].left (IsLocalRing.closedPoint K)`.

Establish `hfo : φ.left o = o`. Establish `: η[G] ≫ φ = η[G]` using `IsMonHom.one_hom φ`. Conclude with `congr(($this).left (IsLocalRing.closedPoint K))`. Establish `hξ` using `FiniteEndFlat.apply_genericPoint φ.left hfo`. Take `⟨W, hW, H⟩` from `exists_open_flat φ.left hξ`.

Take `⟨y, hy, hyc⟩` from `nonempty_inter_closedPoints hW W.2.isLocallyClosed`. Use `flat_of_closedPoints _ fun x hx => ?_` and prove the remaining obligations. Set `x' : 𝟙_ _ ⟶ G` to `Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2`. Set `y' : 𝟙_ _ ⟶ G` to `Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2`. Set `α` to `GrpObj.mulRight (A := G) (y'⁻¹ * x')`.

Set `β` to `GrpObj.mulRight (A := G) ((y'⁻¹ * x') ≫ φ)`. Establish `hαβ : α.hom ≫ φ = φ ≫ β.hom`. Simplify using `only [α, β]`. Generalize the expression as in `y'⁻¹ * x' = z`. Simplify using `[comp_lift_assoc]`.

Establish `hα : y' ≫ α.hom = x'`. Establish `: y' ≫ α.hom = y' * (y'⁻¹ * x')`. Simplify using `[α, comp_lift_assoc, Hom.mul_def]`. Rewrite using `[this, mul_inv_cancel_left]`. Establish `hα' : α.hom.left y = x`.

Establish `h` using `congr(($hα).left (IsLocalRing.closedPoint K))`. Rewrite using `[← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K), ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]`. Conclude with `h`. Establish `: IsIso α.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map α.hom))`. Establish `: IsIso β.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map β.hom))`.

Establish `h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat`. Rewrite using `[Scheme.Hom.stalkMap_comp]`. Conclude with `(Flat.stalkMap β.hom.left _).comp (H y hy)`. Rewrite `h1` using `[← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp]`. Rewrite using `[← hα']`.

Conclude with `(RingHom.Flat.respectsIso.cancel_right_isIso (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1`.
-/
theorem flat_of_quasiFinite_grpEnd (K : Type) [Field K] [IsAlgClosed K]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsIntegral G.left]
    [LocallyOfFiniteType G.hom] (φ : G ⟶ G) [IsMonHom φ] [LocallyQuasiFinite φ.left] [QuasiCompact φ.left] :
    Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : LocallyOfFiniteType (φ.left ≫ G.hom) := by rw [Over.w φ]; infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp _ G.hom
  let o : G.left := η[G].left (IsLocalRing.closedPoint K)
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint K))
  have hξ := FiniteEndFlat.apply_genericPoint φ.left hfo
  obtain ⟨W, hW, H⟩ := exists_open_flat φ.left hξ
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
  let β := GrpObj.mulRight (A := G) ((y'⁻¹ * x') ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize y'⁻¹ * x' = z
    simp [comp_lift_assoc]
  have hα : y' ≫ α.hom = x' := by
    have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, comp_lift_assoc, Hom.mul_def]
    rw [this, mul_inv_cancel_left]
  have hα' : α.hom.left y = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint K))
    rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
    exact h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (H y hy)
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1

/- English proof (translation)
Use `flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) _ _ _ ?_` and prove the remaining obligations. Set `t : Sp (AlgebraicClosure k) ⟶ Sp k` to `spMap (algebraMap _ _)`. Establish `hi` using `grpObj_geometricallyIntegral_of_smooth _ G`. Establish `h₁ : GeometricallyIntegral ((Over.pullback s).obj G).hom` using `inferInstanceAs (GeometricallyIntegral (pullback.snd G.hom s))`. Establish `h₂ : GeometricallyIntegral ((Over.pullback t).obj ((Over.pullback s).obj G)).hom` using `inferInstanceAs (GeometricallyIntegral (pullback.snd ((Over.pullback s).obj G).hom t))`.

Use `GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj ((Over.pullback s).obj G)).hom` as an intermediate fact. Establish `h₃ : LocallyOfFiniteType ((Over.pullback s).obj G).hom` using `inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom s))`. Establish `h₄ : LocallyOfFiniteType ((Over.pullback t).obj ((Over.pullback s).obj G)).hom` using `inferInstanceAs (LocallyOfFiniteType (pullback.snd ((Over.pullback s).obj G).hom t))`. Establish `p₁` using `AbLaw.MulN.isPullback_baseChange s φ`. Establish `p₂` using `AbLaw.MulN.isPullback_baseChange t ((Over.pullback s).map φ)`.

Establish `: LocallyQuasiFinite ((Over.pullback t).map ((Over.pullback s).map φ)).left` using `MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) p₂ (MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) p₁ inferInstance)`. Establish `: QuasiCompact ((Over.pullback t).map ((Over.pullback s).map φ)).left` using `MorphismProperty.of_isPullback (P := @QuasiCompact) p₂ (MorphismProperty.of_isPullback (P := @QuasiCompact) p₁ inferInstance)`. Conclude with `flat_of_quasiFinite_grpEnd _ _ _`.
-/
theorem flat_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom]
    (φ : G ⟶ G) [IsMonHom φ] [LocallyQuasiFinite φ.left] [QuasiCompact φ.left] (k : Type) [Field k]
    (s : Sp k ⟶ S) : Flat ((Over.pullback s).map φ).left := by
  refine flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) _ _ _ ?_
  let t : Sp (AlgebraicClosure k) ⟶ Sp k := spMap (algebraMap _ _)
  have hi := grpObj_geometricallyIntegral_of_smooth _ G
  have h₁ : GeometricallyIntegral ((Over.pullback s).obj G).hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd G.hom s))
  have h₂ : GeometricallyIntegral ((Over.pullback t).obj ((Over.pullback s).obj G)).hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd ((Over.pullback s).obj G).hom t))
  have := GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj ((Over.pullback s).obj G)).hom
  have h₃ : LocallyOfFiniteType ((Over.pullback s).obj G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom s))
  have h₄ : LocallyOfFiniteType ((Over.pullback t).obj ((Over.pullback s).obj G)).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd ((Over.pullback s).obj G).hom t))
  have p₁ := AbLaw.MulN.isPullback_baseChange s φ
  have p₂ := AbLaw.MulN.isPullback_baseChange t ((Over.pullback s).map φ)
  have : LocallyQuasiFinite ((Over.pullback t).map ((Over.pullback s).map φ)).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) p₂
      (MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) p₁ inferInstance)
  have : QuasiCompact ((Over.pullback t).map ((Over.pullback s).map φ)).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) p₂
      (MorphismProperty.of_isPullback (P := @QuasiCompact) p₁ inferInstance)
  exact flat_of_quasiFinite_grpEnd _ _ _

/- English proof (translation)
Rewrite using `[mulA, MonObj.comp_pow, Category.comp_id]`.
-/
theorem comp_mulA {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x : T ⟶ G) (n : ℕ) : x ≫ mulA G n = x ^ n := by
  rw [mulA, MonObj.comp_pow, Category.comp_id]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Set `e : Sp K ⟶ B.left` to `(1 : Over.mk t ⟶ B).left`. Set `g` to `pullback.snd (mulA B n).left e`. Establish `hfin : Finite ↥(pullback (mulA B n).left e)`. Use `g.finite_preimage_singleton (IsLocalRing.closedPoint K)` as an intermediate fact.

Use `Set.finite_univ_iff.mp (this.subset fun z _ => ?_)` and prove the remaining obligations. Conclude with `Subsingleton.elim (α := PrimeSpectrum K) _ _`. Establish `hx : ∀ x : {x : Over.mk t ⟶ B // x ^ n = 1}, x.1.left ≫ (mulA B n).left = 𝟙 _ ≫ e` using `fun x => by`. Rewrite using `[Category.id_comp, ← Over.comp_left, comp_mulA, x.2]`. Use `Finite.of_injective (β := ↥(pullback (mulA B n).left e)) (fun x => pullback.lift x.1.left (𝟙 (Sp K)) (hx x) (IsLocalRing.closedPoint K)) fun a b h => ?_` and prove the remaining obligations.

Use `ext_of_apply_closedPoint_eq (K := K) g (pullback.lift_snd _ _ (hx a)) (pullback.lift_snd _ _ (hx b)) h` as an intermediate fact. Use `Subtype.ext (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Conclude with `(pullback.lift_fst _ _ (hx a)).symm.trans ((congrArg (· ≫ pullback.fst _ _) this).trans (pullback.lift_fst _ _ (hx b)))`. Introduce `x`. Take `⟨y, hy⟩` from `GeomSurj.exists_lift_of_surjective (mulA B n).left x.left`.

Use `⟨Over.homMk y ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.w (mulA B n), ← Category.assoc, ← hy]`. Conclude with `Over.w x`. Rewrite using `[← comp_mulA]`. Conclude with `Over.OverMorphism.ext hy.symm`.
-/
theorem points_of_finite_surjective {S : Scheme.{0}} (B : Over S) [GrpObj B] (n : ℕ)
    [IsFinite (mulA B n).left] [Surjective (mulA B n).left] {K : Type} [Field K] [IsAlgClosed K] (t : Sp K ⟶ S) :
    Finite {x : Over.mk t ⟶ B // x ^ n = 1} ∧ ∀ x : Over.mk t ⟶ B, ∃ y, y ^ n = x := by
  constructor
  · let e : Sp K ⟶ B.left := (1 : Over.mk t ⟶ B).left
    let g := pullback.snd (mulA B n).left e
    have hfin : Finite ↥(pullback (mulA B n).left e) := by
      have := g.finite_preimage_singleton (IsLocalRing.closedPoint K)
      refine Set.finite_univ_iff.mp (this.subset fun z _ => ?_)
      exact Subsingleton.elim (α := PrimeSpectrum K) _ _
    have hx : ∀ x : {x : Over.mk t ⟶ B // x ^ n = 1}, x.1.left ≫ (mulA B n).left = 𝟙 _ ≫ e := fun x => by
      rw [Category.id_comp, ← Over.comp_left, comp_mulA, x.2]
    refine Finite.of_injective (β := ↥(pullback (mulA B n).left e))
      (fun x => pullback.lift x.1.left (𝟙 (Sp K)) (hx x) (IsLocalRing.closedPoint K)) fun a b h => ?_
    have := ext_of_apply_closedPoint_eq (K := K) g (pullback.lift_snd _ _ (hx a)) (pullback.lift_snd _ _ (hx b)) h
    refine Subtype.ext (Over.OverMorphism.ext ?_)
    exact (pullback.lift_fst _ _ (hx a)).symm.trans
      ((congrArg (· ≫ pullback.fst _ _) this).trans (pullback.lift_fst _ _ (hx b)))
  · intro x
    obtain ⟨y, hy⟩ := GeomSurj.exists_lift_of_surjective (mulA B n).left x.left
    refine ⟨Over.homMk y ?_, ?_⟩
    · rw [← Over.w (mulA B n), ← Category.assoc, ← hy]; exact Over.w x
    · rw [← comp_mulA]; exact Over.OverMorphism.ext hy.symm

/- English proof (translation)
Break down `ZJ.field_point_factor_dvr V K t with ⟨r, hr⟩ | ⟨r, hr⟩` into its components or cases. Establish `ht : Set.range t = {IsLocalRing.closedPoint V}`. Establish `: ∀ z, t z = IsLocalRing.closedPoint V` using `fun z => by`. Rewrite using `[hr, Scheme.Hom.comp_apply, Subsingleton.elim (α := PrimeSpectrum _) (r z) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))]`. Conclude with `IsLocalRing.comap_closedPoint (IsLocalRing.residue V)`.

Conclude with `Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint K, this _⟩, by rintro _ ⟨z, rfl⟩; exact this z⟩`. Take `⟨p, h₁, h₂, h₃, -⟩` from `FewZeros.exists_points_hom U t ht hn`. Take `⟨m₁, -, m₂, -⟩` from `hm _ D.toPre.P n hn`. Take `⟨b₁, b₂⟩` from `points_of_finite_surjective D.toPre.P.A n t`. Use `⟨h₃ b₁, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨b, hb⟩` from `b₂ (p x)`. Take `⟨y, rfl⟩` from `h₁ b`. Take `⟨z, -, hz⟩` from `h₂ (x * (y ^ n)⁻¹) (by rw [map_mul, map_inv, map_pow, hb, mul_inv_cancel])`. Conclude with `⟨z * y, by rw [mul_pow, hz, inv_mul_cancel_right]⟩`. Take `⟨m₁, -, m₂, -⟩` from `hm _ A n hn`.

Take `⟨b₁, b₂⟩` from `points_of_finite_surjective A.A n r`. Use `U.gen_hom` as an intermediate fact. Set `e₁` to `TorsionLift.ptsEquiv (jK V) G (Over.mk r) t hr.symm`. Set `e₂ : (Over.mk r ⟶ (Over.pullback (jK V)).obj G) ≃* (Over.mk r ⟶ A.A)` to `MulEquiv.ofBijective (IsMonHom.monoidHom U.gen.hom (Over.mk r)) ⟨fun a b h => (cancel_mono U.gen.hom).1 h, fun b => ⟨b ≫ U.gen.inv, by`. Express the relevant statement in the definitionally equal form `(b ≫ U.gen.inv) ≫ U.gen.hom = b`.

Use the proof step `simp⟩⟩`. Set `e` to `e₂.symm.trans e₁`. Use `⟨FewZeros.finite_torsion_of_mulEquiv e n b₁, fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `b₂ (e.symm x)`. Conclude with `⟨e y, by rw [← map_pow, hy, e.apply_symm_apply]⟩`.
-/
theorem points_of_unifPre (hm : MulNSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (IsLocalRing.maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (IsLocalRing.maximalIdeal V) D A G) {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [IsAlgClosed K]
    (t : Sp K ⟶ Sp V) :
    Finite {x : Over.mk t ⟶ G // x ^ n = 1} ∧ ∀ x : Over.mk t ⟶ G, ∃ y, y ^ n = x := by
  rcases ZJ.field_point_factor_dvr V K t with ⟨r, hr⟩ | ⟨r, hr⟩
  · have ht : Set.range t = {IsLocalRing.closedPoint V} := by
      have : ∀ z, t z = IsLocalRing.closedPoint V := fun z => by
        rw [hr, Scheme.Hom.comp_apply,
          Subsingleton.elim (α := PrimeSpectrum _) (r z) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))]
        exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
      exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint K, this _⟩, by rintro _ ⟨z, rfl⟩; exact this z⟩
    obtain ⟨p, h₁, h₂, h₃, -⟩ := FewZeros.exists_points_hom U t ht hn
    obtain ⟨m₁, -, m₂, -⟩ := hm _ D.toPre.P n hn
    obtain ⟨b₁, b₂⟩ := points_of_finite_surjective D.toPre.P.A n t
    refine ⟨h₃ b₁, fun x => ?_⟩
    obtain ⟨b, hb⟩ := b₂ (p x)
    obtain ⟨y, rfl⟩ := h₁ b
    obtain ⟨z, -, hz⟩ := h₂ (x * (y ^ n)⁻¹) (by rw [map_mul, map_inv, map_pow, hb, mul_inv_cancel])
    exact ⟨z * y, by rw [mul_pow, hz, inv_mul_cancel_right]⟩
  · obtain ⟨m₁, -, m₂, -⟩ := hm _ A n hn
    obtain ⟨b₁, b₂⟩ := points_of_finite_surjective A.A n r
    have := U.gen_hom
    let e₁ := TorsionLift.ptsEquiv (jK V) G (Over.mk r) t hr.symm
    let e₂ : (Over.mk r ⟶ (Over.pullback (jK V)).obj G) ≃* (Over.mk r ⟶ A.A) :=
      MulEquiv.ofBijective (IsMonHom.monoidHom U.gen.hom (Over.mk r))
        ⟨fun a b h => (cancel_mono U.gen.hom).1 h, fun b => ⟨b ≫ U.gen.inv, by
          change (b ≫ U.gen.inv) ≫ U.gen.hom = b
          simp⟩⟩
    let e := e₂.symm.trans e₁
    refine ⟨FewZeros.finite_torsion_of_mulEquiv e n b₁, fun x => ?_⟩
    obtain ⟨y, hy⟩ := b₂ (e.symm x)
    exact ⟨e y, by rw [← map_pow, hy, e.apply_symm_apply]⟩

/- English proof (translation)
Establish `hm` using `AbLaw.MulN.isMonHom_mulA G n`. Establish `: LocallyOfFiniteType ((mulA G n).left ≫ G.hom)` using `by rw [Over.w]; infer_instance`. Establish `: LocallyOfFiniteType (mulA G n).left` using `locallyOfFiniteType_of_comp _ G.hom`. Establish `: QuasiCompact ((mulA G n).left ≫ G.hom)` using `by rw [Over.w]; infer_instance`. Establish `: QuasiCompact (mulA G n).left` using `QuasiCompact.of_comp _ G.hom`.

Establish `: IsSeparated ((mulA G n).left ≫ G.hom)` using `by rw [Over.w]; infer_instance`. Establish `: IsSeparated (mulA G n).left` using `IsSeparated.of_comp _ G.hom`. Establish `: LocallyQuasiFinite (mulA G n).left` using `locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by`. Simplify using `only [comp_mulA]`. Conclude with `(h K t).1`.

Establish `: Flat (mulA G n).left` using `flat_of_flat_fibres_dvr V (FractionRing V) G G _ inferInstance inferInstance inferInstance inferInstance (flat_fibre G _ _ _) (flat_fibre G _ _ _)`. Set `K` to `AlgebraicClosure (IsLocalRing.ResidueField O)`. Set `r : Sp K ⟶ Sp O` to `spMap (algebraMap (IsLocalRing.ResidueField O) K) ≫ spMap (IsLocalRing.residue O)`. Establish `hr : ∀ z : Sp K, r z = IsLocalRing.closedPoint O` using `fun z => by`. Use `(Scheme.Hom.comp_apply _ _ z).trans ?_` and prove the remaining obligations.

Rewrite using `[Subsingleton.elim (α := PrimeSpectrum _) (spMap (algebraMap (IsLocalRing.ResidueField O) K) z) (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))]`. Conclude with `IsLocalRing.comap_closedPoint (IsLocalRing.residue O)`. Take `⟨y, hy⟩` from `(h K ((r ≫ c) ≫ G.hom)).2 (Over.homMk (r ≫ c) rfl)`. Establish `hy' : y.left ≫ (mulA G n).left = r ≫ c`. Rewrite using `[← Over.comp_left, comp_mulA, hy]`.

Both sides reduce to the same expression. Take `⟨s, hs, -⟩` from `exists_section_of_quasiFinite_flat O C _ (pullback.snd (mulA G n).left c) (pullback.lift y.left r hy' (IsLocalRing.closedPoint K)) ((congrArg (fun g => g (IsLocalRing.closedPoint K)) (pullback.lift_snd y.left r hy')).trans (hr _))`. Conclude with `⟨s ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, reassoc_of% hs]⟩`.
-/
theorem exists_root {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    [GeometricallyConnected G.hom] (n : ℕ)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp V),
      Finite {x : Over.mk t ⟶ G // x ^ n = 1} ∧ ∀ x : Over.mk t ⟶ G, ∃ y, y ^ n = x)
    (O C : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] (c : Sp O ⟶ G.left) : ∃ c' : Sp O ⟶ G.left, c' ≫ (mulA G n).left = c := by
  have hm := AbLaw.MulN.isMonHom_mulA G n
  have : LocallyOfFiniteType ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (mulA G n).left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated (mulA G n).left := IsSeparated.of_comp _ G.hom
  have : LocallyQuasiFinite (mulA G n).left :=
    locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      simp only [comp_mulA]
      exact (h K t).1
  have : Flat (mulA G n).left :=
    flat_of_flat_fibres_dvr V (FractionRing V) G G _ inferInstance inferInstance inferInstance inferInstance
      (flat_fibre G _ _ _) (flat_fibre G _ _ _)
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  let r : Sp K ⟶ Sp O := spMap (algebraMap (IsLocalRing.ResidueField O) K) ≫ spMap (IsLocalRing.residue O)
  have hr : ∀ z : Sp K, r z = IsLocalRing.closedPoint O := fun z => by
    refine (Scheme.Hom.comp_apply _ _ z).trans ?_
    rw [Subsingleton.elim (α := PrimeSpectrum _)
      (spMap (algebraMap (IsLocalRing.ResidueField O) K) z) (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  obtain ⟨y, hy⟩ := (h K ((r ≫ c) ≫ G.hom)).2 (Over.homMk (r ≫ c) rfl)
  have hy' : y.left ≫ (mulA G n).left = r ≫ c := by
    rw [← Over.comp_left, comp_mulA, hy]; rfl
  obtain ⟨s, hs, -⟩ := exists_section_of_quasiFinite_flat O C _ (pullback.snd (mulA G n).left c)
    (pullback.lift y.left r hy' (IsLocalRing.closedPoint K))
    ((congrArg (fun g => g (IsLocalRing.closedPoint K)) (pullback.lift_snd y.left r hy')).trans (hr _))
  exact ⟨s ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, reassoc_of% hs]⟩

/- English proof (translation)
Introduce `hL o Ω _ _ _ _ S ρ p _ y₀ u a k hk ⟨c, hc, hca⟩`. Use `u.semi.smooth` as an intermediate fact. Use `u.semi.separated` as an intermediate fact. Use `u.semi.quasiCompact` as an intermediate fact. Use `u.semi.geomConnected` as an intermediate fact.

Take `⟨c', hc'⟩` from `exists_root u.G k (fun K _ _ t => points_of_unifPre hL.1.mulN u.U.toUnifPre hk t) (OO p) (PadicAlgCl p) c`. Establish `h₁ : c' ≫ u.G.hom = c ≫ u.G.hom` using `by rw [← hc', Category.assoc, Over.w]`. Set `e` to `TorsionLift.ptsEquiv (jK u.V) u.G (TFK (R := u.V) (PadicAlgCl p)) _ rfl`. Establish `he : ∀ x : u.PtC, (e x).left = u.toG x` using `fun x => TorsionLift.ptsEquiv_left _ _ _ _ _ x`. Set `x' : Over.mk ((TFK (R` to `u.V) (PadicAlgCl p)).hom ≫ jK u.V) ⟶ u.G := Over.homMk (gPt p ≫ c') (by`.

Rewrite using `[Category.assoc, h₁, ← Category.assoc, hca, ← he]`. Conclude with `Over.w (e a))`. Use `⟨e.symm x', ⟨c', h₁.trans hc, ?_⟩, e.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← he, e.apply_symm_apply]`. Both sides reduce to the same expression.

Rewrite using `[map_pow, e.apply_symm_apply, ← comp_mulA]`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Rewrite using `[he, ← hca, ← hc']`. Conclude with `Category.assoc _ _ _`.
-/
theorem exists_integral_root : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : u.PtC) (k : ℕ), 1 ≤ k → u.Int a → ∃ a' : u.PtC, u.Int a' ∧ a' ^ k = a := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u a k hk ⟨c, hc, hca⟩
  have := u.semi.smooth
  have := u.semi.separated
  have := u.semi.quasiCompact
  have := u.semi.geomConnected
  obtain ⟨c', hc'⟩ := exists_root u.G k (fun K _ _ t => points_of_unifPre hL.1.mulN u.U.toUnifPre hk t)
    (OO p) (PadicAlgCl p) c
  have h₁ : c' ≫ u.G.hom = c ≫ u.G.hom := by rw [← hc', Category.assoc, Over.w]
  let e := TorsionLift.ptsEquiv (jK u.V) u.G (TFK (R := u.V) (PadicAlgCl p)) _ rfl
  have he : ∀ x : u.PtC, (e x).left = u.toG x := fun x => TorsionLift.ptsEquiv_left _ _ _ _ _ x
  let x' : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ jK u.V) ⟶ u.G :=
    Over.homMk (gPt p ≫ c') (by
      rw [Category.assoc, h₁, ← Category.assoc, hca, ← he]
      exact Over.w (e a))
  refine ⟨e.symm x', ⟨c', h₁.trans hc, ?_⟩, e.injective ?_⟩
  · rw [← he, e.apply_symm_apply]; rfl
  · rw [map_pow, e.apply_symm_apply, ← comp_mulA]
    refine Over.OverMorphism.ext ?_
    rw [he, ← hca, ← hc']
    exact Category.assoc _ _ _

end GlobalTheory.IntDiv
