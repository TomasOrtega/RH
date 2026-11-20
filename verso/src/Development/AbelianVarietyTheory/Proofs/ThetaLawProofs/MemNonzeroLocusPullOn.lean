import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnivChartOfStandardSmooth
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecOnNonvanishing

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyNear

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Pull

variable {X Y : Scheme.{0}} {L : LB X}

/- English proof (translation)
Rewrite using `[← Scheme.Hom.appLE_map φ e (homOfLE h).op]`. Both sides reduce to the same expression.
-/
theorem res_appLE (φ : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (e : V ≤ φ ⁻¹ᵁ U) (h : V' ≤ V) (s : Γ(X, U)) :
    resG Y h ((φ.appLE U V e).hom s) = (φ.appLE U V' (h.trans e)).hom s := by
  rw [← Scheme.Hom.appLE_map φ e (homOfLE h).op]; rfl

/- English proof (translation)
Rewrite using `[← Scheme.Hom.map_appLE φ e (homOfLE h).op]`. Both sides reduce to the same expression.
-/
theorem appLE_res (φ : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : U' ≤ U) (e : V ≤ φ ⁻¹ᵁ U') (s : Γ(X, U)) :
    (φ.appLE U' V e).hom (resG X h s) = (φ.appLE U V (e.trans (φ.preimage_mono h))).hom s := by
  rw [← Scheme.Hom.map_appLE φ e (homOfLE h).op]; rfl

def pullOn (φ : Y ⟶ X) {W : X.Opens} (hW : ∀ y, φ y ∈ W) (θ : ∀ i, Γ(X, W ⊓ L.U i)) (hθ : θ ∈ secOn L W) :
    (L.pull φ).Sec where
  f j := (φ.appLE (W ⊓ L.U (j PUnit.unit)) ((L.pull φ).U j)
    (fun y hy => ⟨hW y, LB.wchart_le L (fun _ : PUnit => φ) j PUnit.unit hy⟩)).hom (θ _)
  compat i j := by
    have e : (L.pull φ).U i ⊓ (L.pull φ).U j ≤ φ ⁻¹ᵁ (W ⊓ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      fun y hy => ⟨⟨hW y, LB.wchart_le L (fun _ : PUnit => φ) i PUnit.unit hy.1⟩,
        LB.wchart_le L (fun _ : PUnit => φ) j PUnit.unit hy.2⟩
    have h := congrArg (φ.appLE _ _ e).hom (hθ (i PUnit.unit) (j PUnit.unit))
    rw [map_mul, appLE_res, appLE_res, appLE_res] at h
    refine (res_appLE φ _ _ _).trans (h.trans ?_)
    refine congrArg₂ (· * ·) ?_ (res_appLE φ _ _ _).symm
    have e₁ : ∀ {G : Type} [CommGroup G] (a : G), a = ∏ _k : PUnit.{1}, a ^ (1 : ℤ) := fun a => by simp
    exact congrArg Units.val (e₁ (res (e.trans (φ.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
      (pullU φ _ (L.g (i PUnit.unit) (j PUnit.unit)))))

/- English proof (translation)
Use `TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩` and prove the remaining obligations. Conclude with `(Scheme.basicOpen_appLE φ _ _ _ (θ i)).ge ⟨mem_pull.2 (X.basicOpen_le _ hy).2, hy⟩`.
-/
theorem mem_nonzeroLocus_pullOn (φ : Y ⟶ X) {W : X.Opens} (hW : ∀ y, φ y ∈ W) (θ : ∀ i, Γ(X, W ⊓ L.U i))
    (hθ : θ ∈ secOn L W) {y : Y} {i : L.ι} (hy : φ y ∈ X.basicOpen (θ i)) :
    y ∈ Out.nonzeroLocus (pullOn φ hW θ hθ) := by
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
  exact (Scheme.basicOpen_appLE φ _ _ _ (θ i)).ge ⟨mem_pull.2 (X.basicOpen_le _ hy).2, hy⟩

end Pull

open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

/- English proof (translation)
Introduce `hL R _ _ P hg p`. Take `⟨V, θ, hpV, hθ, hne⟩` from `SecFamily.exists_secOn_nonvanishing hL (Sp R) P p`. Establish `c₁ : IsCommMonObj P.A` using `P.isAb.comm`. Take `⟨r₁, hr₁, v, hv⟩` from `LieLoc.lie_locally_free R P.A P.g P.smoothDim p`. Take `⟨_, ⟨r₂, rfl⟩, hr₂, hsub⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) (u := V.1) hpV V.2`.

Use `⟨r₁ * r₂, fun h => (p.2.mem_or_mem h).elim hr₁ hr₂, fun R' _ f hf => ?_⟩` and prove the remaining obligations. Rewrite `hf` using `[map_mul]`. Establish `u₁` using `isUnit_of_mul_isUnit_left hf`. Establish `u₂` using `isUnit_of_mul_isUnit_right hf`. Establish `hV : ∀ s : Sp R', spMap f s ∈ V` using `fun s => hsub (show f r₂ ∉ s.asIdeal from fun h => s.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h u₂))`.

Establish `h` using `isGrpPullback_pullback P.A (spMap f)`. Set `φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left` to `pullback.fst P.A.hom (spMap f)`. Express the relevant statement in the definitionally equal form `IsGrpPullback _ _ _ φ at h`. Establish `hL'` using `pull_isLB P.isLB φ`. Establish `hw` using `(isGen_iff _).1 (idIso_isGen hL')`.

Set `P' : Out.PolAV (Sp R')` to `{ A := (Over.pullback (spMap f)).obj P.A isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb g := P.g smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim L := P.L.pull φ isLB := hL' rigid := PolBaseChange.rigidified_pull h P.rigid sy …`. Take `⟨rig, hrig⟩` from `P'.rigid`. Establish `hW : ∀ y, φ y ∈ P.A.hom ⁻¹ᵁ V` using `fun y => by`. Establish `e : P.A.hom (φ y) = spMap f (P'.A.hom y)` using `congrArg (fun g => g y) h.1.w`. Express the relevant statement in the definitionally equal form `P.A.hom (φ y) ∈ V`.

Rewrite using `[e]`. Conclude with `hV _`. Set `f' : Localization.Away r₁ →+* R'` to `IsLocalization.Away.lift r₁ u₁`. Establish `hf' : spMap f' ≫ spMap (algebraMap R (Localization.Away r₁)) = spMap f`. Rewrite using `[← IsLocalization.Away.lift_comp (S := Localization.Away r₁) r₁ u₁]`.

Conclude with `(Spec.map_comp _ _).symm`. Establish `h₁` using `isGrpPullback_pullback P.A (spMap (algebraMap R (Localization.Away r₁)))`. Establish `w₁ : φ ≫ P.A.hom = (P'.A.hom ≫ spMap f') ≫ spMap (algebraMap R (Localization.Away r₁))`. Rewrite using `[Category.assoc, hf']`. Conclude with `h.1.w`.

Establish `h₂` using `IsGrpPullback.cancel h₁ (h.congr hf'.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)`. Establish `a₁` using `Out.TLinPf.isAb_pullback (spMap (algebraMap R (Localization.Away r₁))) P.A P.isAb`. Establish `c₂ : IsCommMonObj P'.A` using `P'.isAb.comm`. Establish `c₃` using `a₁.comm`. Take `⟨v', hb', -⟩` from `exists_isLieBasis_baseChange _ R' f' _ P'.A _ h₂ a₁.smooth P.g v hv`.

Use `⟨⟨P', hg, rig, hrig, pullOn φ hW θ hθ, fun s => ?_, v', hb'⟩, φ, rfl, h, idIso _, idIso_isGen hL'⟩` and prove the remaining obligations. Take `⟨z, i, hz, hz'⟩` from `hne _ (hV s)`. Take `⟨y, rfl, hy⟩` from `Scheme.exists_preimage_of_isPullback h.1 z s hz`. Conclude with `⟨y, hy, mem_nonzeroLocus_pullOn φ hW θ hθ hz'⟩`.
-/
theorem main : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)), 1 ≤ P.g → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ r) → ∃ (y : KeyIn R') (π : y.P.A.left ⟶ P.A.left), y.P.g = P.g ∧ IsGrpPullback y.P.A P.A (spMap ρ) π ∧ LBIso y.P.L (P.L.pull π) := by
  intro hL R _ _ P hg p
  obtain ⟨V, θ, hpV, hθ, hne⟩ := SecFamily.exists_secOn_nonvanishing hL (Sp R) P p
  have c₁ : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨r₁, hr₁, v, hv⟩ := LieLoc.lie_locally_free R P.A P.g P.smoothDim p
  obtain ⟨_, ⟨r₂, rfl⟩, hr₂, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) (u := V.1) hpV V.2
  refine ⟨r₁ * r₂, fun h => (p.2.mem_or_mem h).elim hr₁ hr₂, fun R' _ f hf => ?_⟩
  rw [map_mul] at hf
  have u₁ := isUnit_of_mul_isUnit_left hf
  have u₂ := isUnit_of_mul_isUnit_right hf
  have hV : ∀ s : Sp R', spMap f s ∈ V := fun s => hsub (show f r₂ ∉ s.asIdeal from fun h =>
    s.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h u₂))
  have h := isGrpPullback_pullback P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  obtain ⟨rig, hrig⟩ := P'.rigid
  have hW : ∀ y, φ y ∈ P.A.hom ⁻¹ᵁ V := fun y => by
    have e : P.A.hom (φ y) = spMap f (P'.A.hom y) := congrArg (fun g => g y) h.1.w
    change P.A.hom (φ y) ∈ V
    rw [e]
    exact hV _
  let f' : Localization.Away r₁ →+* R' := IsLocalization.Away.lift r₁ u₁
  have hf' : spMap f' ≫ spMap (algebraMap R (Localization.Away r₁)) = spMap f := by
    rw [← IsLocalization.Away.lift_comp (S := Localization.Away r₁) r₁ u₁]
    exact (Spec.map_comp _ _).symm
  have h₁ := isGrpPullback_pullback P.A (spMap (algebraMap R (Localization.Away r₁)))
  have w₁ : φ ≫ P.A.hom = (P'.A.hom ≫ spMap f') ≫ spMap (algebraMap R (Localization.Away r₁)) := by
    rw [Category.assoc, hf']; exact h.1.w
  have h₂ := IsGrpPullback.cancel h₁ (h.congr hf'.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  have a₁ := Out.TLinPf.isAb_pullback (spMap (algebraMap R (Localization.Away r₁))) P.A P.isAb
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  have c₃ := a₁.comm
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange _ R' f' _ P'.A _ h₂ a₁.smooth P.g v hv
  refine ⟨⟨P', hg, rig, hrig, pullOn φ hW θ hθ, fun s => ?_, v', hb'⟩, φ, rfl, h, idIso _, idIso_isGen hL'⟩
  obtain ⟨z, i, hz, hz'⟩ := hne _ (hV s)
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  exact ⟨y, hy, mem_nonzeroLocus_pullOn φ hW θ hθ hz'⟩

end GlobalTheory.KeyNear
