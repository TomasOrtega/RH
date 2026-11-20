import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfFinite
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSpreadsOutFromGenericFibreProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActSpreadFromDenseFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.WeilBound.CoreStatements.TorusUniformisation.SiegelCompactSupport.ExistsSabExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.AbelianSchemeSpreading

section Norm

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.FlatNorm TopologicalSpace GlobalTheory.LB GlobalTheory.LBGerm

/- English proof (translation)
Use `choose V t hx ht using exists_generates π hL`. Use `choose c hc using fun a b : X => Generates.exists_unit_smul hL ((ht a).restrict (π.preimage_mono (inf_le_left : V a ⊓ V b ≤ V a))) ((ht b).restrict (π.preimage_mono (inf_le_right : V a ⊓ V b ≤ V b)))`. Establish `hc' (a b : X) {W : X.Opens} (ha : W ≤ V a) (hb : W ≤ V b) : rs Y (π.preimage_mono (le_inf ha hb)) (c a b).val • SecOn.restrict L (π.preimage_mono ha) (t a) = SecOn.restrict L (π.preimage_mono hb) (t b)`. Establish `e` using `congrArg (SecOn.restrict L (π.preimage_mono (le_inf ha hb))) (hc a b)`. Rewrite `e` using `[map_smulₛₗ, SecOn.restrict_restrict, SecOn.restrict_restrict]`. Then use the resulting hypothesis.

Use `⟨⟨X, V, fun a b => Units.map (norm π _) (c a b)⟩, ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩, fun a => Units.ext ?_, fun a b d => Units.ext ?_⟩, fun s => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `resG X (le_inf le_rfl le_rfl : V a ≤ V a ⊓ V a) (norm π (V a ⊓ V a) (c a a).val) = 1`. Rewrite using `[resG_norm, ← map_one (norm π (V a))]`. Use `congr 1`. Use `((ht a).restrict le_rfl).smul_injective hL ?_` and prove the remaining obligations.

Rewrite using `[one_smul]`. Conclude with `hc' a a le_rfl le_rfl`. Establish `la : V a ⊓ V b ⊓ V d ≤ V a` using `inf_le_left.trans inf_le_left`. Establish `lb : V a ⊓ V b ⊓ V d ≤ V b` using `inf_le_left.trans inf_le_right`. Establish `ld : V a ⊓ V b ⊓ V d ≤ V d` using `inf_le_right`.

Express the relevant statement in the definitionally equal form `resG X (le_inf la lb) (norm π (V a ⊓ V b) (c a b).val) * resG X (le_inf lb ld) (norm π (V b ⊓ V d) (c b d).val) = resG X (le_inf la ld) (norm π (V a ⊓ V d) (c a d).val)`. Rewrite using `[resG_norm, resG_norm, resG_norm, ← map_mul]`. Use `congr 1`. Use `((ht a).restrict (π.preimage_mono la)).smul_injective hL ?_` and prove the remaining obligations. Rewrite using `[_root_.mul_comm, mul_smul, hc' a b la lb, hc' b d lb ld, hc' a d la ld]`.

Use `choose f hf using fun a : X => (ht a).exists_smul hL (ofSec s _)`. Establish `hf' (a : X) {W : X.Opens} (ha : W ≤ V a) : rs Y (π.preimage_mono ha) (f a) • SecOn.restrict L (π.preimage_mono ha) (t a) = ofSec s _`. Establish `e` using `congrArg (SecOn.restrict L (π.preimage_mono ha)) (hf a)`. Rewrite `e` using `[map_smulₛₗ, SecOn.restrict_ofSec]`. Then use the resulting hypothesis. Use `⟨⟨fun a => norm π _ (f a), fun a b => ?_⟩, fun x => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `resG X (inf_le_left : V a ⊓ V b ≤ V a) (norm π _ (f a)) = norm π (V a ⊓ V b) (c a b).val * resG X (inf_le_right : V a ⊓ V b ≤ V b) (norm π _ (f b))`. Rewrite using `[resG_norm, resG_norm, ← map_mul]`. Use `congr 1`. Use `((ht a).restrict (π.preimage_mono (inf_le_left : V a ⊓ V b ≤ V a))).smul_injective hL ?_` and prove the remaining obligations. Rewrite using `[hf' a inf_le_left, _root_.mul_comm, mul_smul, hc, hf' b inf_le_right]`.

Use `(mem_nonzeroLocus_iff_basicOpen _ (k := x) (hx x)).trans ((mem_basicOpen_norm π (f x) (hx x)).trans (forall₂_congr fun y hy => ?_))` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart hL y`. Establish `hy' : y ∈ π ⁻¹ᵁ V x ⊓ L.U i` using `⟨show π y ∈ V x from hy ▸ hx x, hi⟩`. Establish `e` using `congrArg (germAt i y hy') (hf x)`. Establish `e' : germAt i y hy' (ofSec s (π ⁻¹ᵁ V x)) = gs (𝟙 Y) y _ (s.f i)` using `gs_res (𝟙 Y) y inf_le_right hy' _`.

Establish `u : IsUnit (germAt i y hy' (t x))`. Express the relevant statement in the definitionally equal form `IsUnit (gs (𝟙 Y) y _ (coord (t x) i))`. Rewrite using `[gs_eq (𝟙 Y) y _ hy']`. Conclude with `((ht x i).map _).map _`. Rewrite using `[mem_nonzeroLocus_iff_isUnit s hi, ← e', ← e, germAt_smul, IsUnit.mul_iff, and_iff_left u]`.

Conclude with `(isUnit_gs_iff (𝟙 Y) y _ hy'.1 _).symm`.
-/
theorem exists_norm_lb_all (X Y : Scheme.{0}) [IsLocallyNoetherian X] (π : Y ⟶ X) [IsFinite π] [Flat π] (L : LB Y)
    (hL : L.IsLB) : ∃ N : LB X, N.IsLB ∧ ∀ s : LB.Sec L, ∃ n : LB.Sec N,
      ∀ x : X, x ∈ nonzeroLocus n ↔ ∀ y : Y, π y = x → y ∈ nonzeroLocus s := by
  choose V t hx ht using exists_generates π hL
  choose c hc using fun a b : X => Generates.exists_unit_smul hL
    ((ht a).restrict (π.preimage_mono (inf_le_left : V a ⊓ V b ≤ V a)))
    ((ht b).restrict (π.preimage_mono (inf_le_right : V a ⊓ V b ≤ V b)))
  have hc' (a b : X) {W : X.Opens} (ha : W ≤ V a) (hb : W ≤ V b) :
      rs Y (π.preimage_mono (le_inf ha hb)) (c a b).val • SecOn.restrict L (π.preimage_mono ha) (t a) =
        SecOn.restrict L (π.preimage_mono hb) (t b) := by
    have e := congrArg (SecOn.restrict L (π.preimage_mono (le_inf ha hb))) (hc a b)
    rwa [map_smulₛₗ, SecOn.restrict_restrict, SecOn.restrict_restrict] at e
  refine ⟨⟨X, V, fun a b => Units.map (norm π _) (c a b)⟩,
    ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩, fun a => Units.ext ?_, fun a b d => Units.ext ?_⟩,
    fun s => ?_⟩
  · change resG X (le_inf le_rfl le_rfl : V a ≤ V a ⊓ V a) (norm π (V a ⊓ V a) (c a a).val) = 1
    rw [resG_norm, ← map_one (norm π (V a))]
    congr 1
    refine ((ht a).restrict le_rfl).smul_injective hL ?_
    rw [one_smul]
    exact hc' a a le_rfl le_rfl
  · have la : V a ⊓ V b ⊓ V d ≤ V a := inf_le_left.trans inf_le_left
    have lb : V a ⊓ V b ⊓ V d ≤ V b := inf_le_left.trans inf_le_right
    have ld : V a ⊓ V b ⊓ V d ≤ V d := inf_le_right
    change resG X (le_inf la lb) (norm π (V a ⊓ V b) (c a b).val) *
      resG X (le_inf lb ld) (norm π (V b ⊓ V d) (c b d).val) =
      resG X (le_inf la ld) (norm π (V a ⊓ V d) (c a d).val)
    rw [resG_norm, resG_norm, resG_norm, ← map_mul]
    congr 1
    refine ((ht a).restrict (π.preimage_mono la)).smul_injective hL ?_
    rw [_root_.mul_comm, mul_smul, hc' a b la lb, hc' b d lb ld, hc' a d la ld]
  choose f hf using fun a : X => (ht a).exists_smul hL (ofSec s _)
  have hf' (a : X) {W : X.Opens} (ha : W ≤ V a) :
      rs Y (π.preimage_mono ha) (f a) • SecOn.restrict L (π.preimage_mono ha) (t a) = ofSec s _ := by
    have e := congrArg (SecOn.restrict L (π.preimage_mono ha)) (hf a)
    rwa [map_smulₛₗ, SecOn.restrict_ofSec] at e
  refine ⟨⟨fun a => norm π _ (f a), fun a b => ?_⟩, fun x => ?_⟩
  · change resG X (inf_le_left : V a ⊓ V b ≤ V a) (norm π _ (f a)) =
      norm π (V a ⊓ V b) (c a b).val * resG X (inf_le_right : V a ⊓ V b ≤ V b) (norm π _ (f b))
    rw [resG_norm, resG_norm, ← map_mul]
    congr 1
    refine ((ht a).restrict (π.preimage_mono (inf_le_left : V a ⊓ V b ≤ V a))).smul_injective hL ?_
    rw [hf' a inf_le_left, _root_.mul_comm, mul_smul, hc, hf' b inf_le_right]
  · refine (mem_nonzeroLocus_iff_basicOpen _ (k := x) (hx x)).trans
      ((mem_basicOpen_norm π (f x) (hx x)).trans (forall₂_congr fun y hy => ?_))
    obtain ⟨i, hi⟩ := exists_chart hL y
    have hy' : y ∈ π ⁻¹ᵁ V x ⊓ L.U i := ⟨show π y ∈ V x from hy ▸ hx x, hi⟩
    have e := congrArg (germAt i y hy') (hf x)
    have e' : germAt i y hy' (ofSec s (π ⁻¹ᵁ V x)) = gs (𝟙 Y) y _ (s.f i) := gs_res (𝟙 Y) y inf_le_right hy' _
    have u : IsUnit (germAt i y hy' (t x)) := by
      change IsUnit (gs (𝟙 Y) y _ (coord (t x) i))
      rw [gs_eq (𝟙 Y) y _ hy']
      exact ((ht x i).map _).map _
    rw [mem_nonzeroLocus_iff_isUnit s hi, ← e', ← e, germAt_smul, IsUnit.mul_iff, and_iff_left u]
    exact (isUnit_gs_iff (𝟙 Y) y _ hy'.1 _).symm

/- English proof (translation)
Use `hL.compactSpace` as an intermediate fact. Establish `: CompactSpace X` using `π.surjective.compactSpace π.continuous`. Use `choose U hU hxU _hle using fun x : X => exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial`. Use `choose n hn s hS hle _haff using fun x : X => hL.exists_affine_finite_subset (π.finite_preimage_singleton x) (U := π ⁻¹ᵁ U x) (fun y (hy : π y = x) => show π y ∈ U x from hy ▸ hxU x)`. Use `choose O hO hOle using fun x : X => exists_preimage_le π (x := x) (O := nonzeroLocus (s x)) fun y hy => hS x hy`.

Take `⟨T, hT⟩` from `exists_finset_iSup_eq_top O hO`. Take `⟨m, -, t, ht⟩` from `exists_common_pow (fun x : T => n x) (fun x => hn x) (fun x => s x)`. Take `⟨N, hN, H⟩` from `exists_norm_lb_all X Y π (lbPow L m) (isLB_lbPow hL.isLB m)`. Use `choose ν hν using fun x : T => H (t x)`. Use `⟨N, isAmpleLB_of_cover hN le_rfl (fun x => secToPow (ν x) 1) ?_ fun x => ?_⟩` and prove the remaining obligations.

Use `top_le_iff.1 (hT.ge.trans (iSup_mono fun x z hz => ?_))` and prove the remaining obligations. Rewrite using `[nonzeroLocus_secToPow _ le_rfl]`. Use `(hν x z).2 fun y hy => ?_` and prove the remaining obligations. Rewrite using `[ht]`. Conclude with `hOle x (show π y ∈ O x from hy ▸ hz)`.

Rewrite using `[nonzeroLocus_secToPow _ le_rfl]`. Establish `hle' : nonzeroLocus (ν x) ≤ U x` using `fun z hz => by`. Take `⟨y, rfl⟩` from `π.surjective z`. Use `(hν x _).1 hz y rfl` as an intermediate fact. Rewrite `this` using `[ht]`.

Conclude with `hle x this`. Establish `h` using `GlobalTheory.isAffineOpen_nonzeroLocus_inf hN (ν x) (hU x)`. Rewrite `h` using `[inf_eq_left.2 hle']`. Then use the resulting hypothesis.
-/
theorem exists_ample_of_finite {X Y : Scheme.{0}} [IsLocallyNoetherian X] (π : Y ⟶ X) [IsFinite π] [Flat π]
    [Surjective π] {L : LB Y} (hL : IsAmpleLB L) : ∃ N : LB X, IsAmpleLB N := by
  have := hL.compactSpace
  have : CompactSpace X := π.surjective.compactSpace π.continuous
  choose U hU hxU _hle using fun x : X => exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  choose n hn s hS hle _haff using fun x : X => hL.exists_affine_finite_subset (π.finite_preimage_singleton x)
    (U := π ⁻¹ᵁ U x) (fun y (hy : π y = x) => show π y ∈ U x from hy ▸ hxU x)
  choose O hO hOle using fun x : X => exists_preimage_le π (x := x) (O := nonzeroLocus (s x)) fun y hy => hS x hy
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top O hO
  obtain ⟨m, -, t, ht⟩ := exists_common_pow (fun x : T => n x) (fun x => hn x) (fun x => s x)
  obtain ⟨N, hN, H⟩ := exists_norm_lb_all X Y π (lbPow L m) (isLB_lbPow hL.isLB m)
  choose ν hν using fun x : T => H (t x)
  refine ⟨N, isAmpleLB_of_cover hN le_rfl (fun x => secToPow (ν x) 1) ?_ fun x => ?_⟩
  · refine top_le_iff.1 (hT.ge.trans (iSup_mono fun x z hz => ?_))
    rw [nonzeroLocus_secToPow _ le_rfl]
    refine (hν x z).2 fun y hy => ?_
    rw [ht]
    exact hOle x (show π y ∈ O x from hy ▸ hz)
  · rw [nonzeroLocus_secToPow _ le_rfl]
    have hle' : nonzeroLocus (ν x) ≤ U x := fun z hz => by
      obtain ⟨y, rfl⟩ := π.surjective z
      have := (hν x _).1 hz y rfl
      rw [ht] at this
      exact hle x this
    have h := GlobalTheory.isAffineOpen_nonzeroLocus_inf hN (ν x) (hU x)
    rwa [inf_eq_left.2 hle'] at h

/- English proof (translation)
Take `⟨L, _, _, _, h⟩` from `GlobalTheory.ProjFinite.exists_finite_isProjBy K A hA`. Take `⟨M, hM⟩` from `exists_isAmpleLB_of_isProjOver ((ProjSpace.isProjBy_iff_isProjOver _).1 h)`. Use `hA.proper` as an intermediate fact. Establish `: IsLocallyNoetherian A.left` using `LocallyOfFiniteType.isLocallyNoetherian A.hom`. Establish `: Subsingleton (Sp K)` using `inferInstanceAs (Subsingleton (PrimeSpectrum K))`.

Establish `: Nonempty (Sp L)` using `inferInstanceAs (Nonempty (PrimeSpectrum L))`. Establish `h₁ : Flat (spMap (algebraMap K L))` using `inferInstance`. Establish `h₂ : Surjective (spMap (algebraMap K L))` using `inferInstance`. Establish `h₃ : IsFinite (spMap (algebraMap K L))`. Rewrite using `[IsFinite.SpecMap_iff]`.

Conclude with `RingHom.finite_algebraMap.2 inferInstance`. Take `⟨N, hN⟩` from `exists_ample_of_finite (pullback.fst A.hom (spMap (algebraMap K L))) hM`. Conclude with `hN.isProjOver A.hom`.
-/
theorem isProjOver_abelian (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsProjOver A.hom := by
  obtain ⟨L, _, _, _, h⟩ := GlobalTheory.ProjFinite.exists_finite_isProjBy K A hA
  obtain ⟨M, hM⟩ := exists_isAmpleLB_of_isProjOver ((ProjSpace.isProjBy_iff_isProjOver _).1 h)
  have := hA.proper
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Sp L) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  have h₁ : Flat (spMap (algebraMap K L)) := inferInstance
  have h₂ : Surjective (spMap (algebraMap K L)) := inferInstance
  have h₃ : IsFinite (spMap (algebraMap K L)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  obtain ⟨N, hN⟩ := exists_ample_of_finite (pullback.fst A.hom (spMap (algebraMap K L))) hM
  exact hN.isProjOver A.hom

end Norm

open GlobalTheory GlobalTheory.SpreadAb in

/- English proof (translation)
Take `⟨g, hg⟩` from `GlobalTheory.AbelianDim.exists_relDim K A hA`. Take `⟨Z, s, φ, hs, h⟩` from `exists_projModel R K A.hom (isProjOver_abelian K A hA)`. Establish `hpr : IsProper s` using `isProper_of_isProjOver hs`. Establish `hfp : LocallyOfFinitePresentation s` using `inferInstance`. Take `⟨f₀, hf₀, H₀⟩` from `near_smooth_connected R K hs h g hg hA.geomConnected`.

Take `⟨f₁, hf₁, H₁⟩` from `near_hom R K (pullback.fst s s ≫ s) s (isPullback_square h) ((μ[A]).left ≫ φ) (by`. Rewrite using `[(isPullback_square h).w, Category.assoc, h.w, Over.w_assoc]`. Use the proof step `rfl)`. Take `⟨f₂, hf₂, H₂⟩` from `near_hom R K s s h ((ι[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])`. Take `⟨f₃, hf₃, H₃⟩` from `near_hom R K (𝟙 _) s (IsPullback.id_vert (spMap (algebraMap R K))) ((η[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc]; simp)`.

Take `⟨f₄, hf₄, H₄⟩` from `GlobalTheory.GenSpread.exists_lb s h hM`. Use `choose b hb Hb using fun j => near_hom R K s s h ((w j).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])`. Establish `hf₅ : ∏ j, b j ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => hb j`. Establish `hf : f₀ * f₁ * f₂ * f₃ * f₄ * ∏ j, b j ≠ 0` using `by simp only [ne_eq, mul_eq_zero, not_or]; tauto`. Set `R'` to `Localization.Away (f₀ * f₁ * f₂ * f₃ * f₄ * ∏ j, b j)`.

Set `c` to `algebraMap R R'`. Establish `hu : IsUnit (c (f₀ * f₁ * f₂ * f₃ * f₄ * ∏ j, b j))` using `IsLocalization.Away.algebraMap_isUnit _`. Simplify using `only [map_mul, IsUnit.mul_iff] at hu`. Take `⟨⟨⟨⟨⟨u₀, u₁⟩, u₂⟩, u₃⟩, u₄⟩, u₅⟩` from `hu`. Establish `u₆ : ∀ j, IsUnit (c (b j))` using `fun j => isUnit_of_dvd_unit (map_dvd c (Finset.dvd_prod_of_mem b (Finset.mem_univ j))) u₅`.

Set `ψ` to `toFrac R K hf`. Establish `hψ : spMap ψ ≫ spMap c = spMap (algebraMap R K)`. Rewrite using `[← Spec.map_comp, ← toFrac_comp R K hf]`. Both sides reduce to the same expression. Set `G : Over (Sp R')` to `Over.mk (pullback.snd s (spMap c))`.

Set `a : G.left ⟶ Z` to `pullback.fst s (spMap c)`. Establish `hG : IsPullback a G.hom s (spMap c)` using `IsPullback.of_hasPullback _ _`. Set `φ' : A.left ⟶ G.left` to `hG.lift φ (A.hom ≫ spMap ψ) (by rw [h.w, Category.assoc, hψ])`. Establish `hφ₁ : φ' ≫ a = φ` using `hG.lift_fst _ _ _`. Establish `hφ₂ : φ' ≫ G.hom = A.hom ≫ spMap ψ` using `hG.lift_snd _ _ _`.

Establish `hφ : IsPullback φ' A.hom G.hom (spMap ψ)` using `IsPullback.of_right (by rwa [hφ₁, hψ]) hφ₂ hG`. Take `⟨hsm, hgc⟩` from `H₀ R' c u₀`. Establish `hsm' : Smooth G.hom` using `SmoothOfRelativeDimension.smooth g (pullback.snd s (spMap c))`. Establish `hpr' : IsProper G.hom` using `inferInstanceAs (IsProper (pullback.snd s (spMap c)))`. Take `⟨m, hm₁, hm₂⟩` from `H₁ R' c u₁ _ _ _ (isPullback_square hG).w`.

Take `⟨i, hi₁, hi₂⟩` from `H₂ R' c u₂ _ _ _ hG.w`. Take `⟨e, he₁, he₂⟩` from `H₃ R' c u₃ _ (spMap c) (𝟙 _) (by simp)`. Take `⟨N, hN, hMN⟩` from `H₄ R' c u₄ _ _ _ hG.w`. Use `choose v hv₁ hv₂ using fun j => Hb j R' c (u₆ j) _ _ _ hG.w`. Use `ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom ψ) (toFrac_injective R K hf)` as an intermediate fact.

Use `hA.comm` as an intermediate fact. Establish `L : ∀ (Y : Over (Sp R')) (u : Y.left ⟶ Z), u ≫ s = Y.hom ≫ spMap c → ∃ v : Y ⟶ G, v.left ≫ a = u` using `fun Y u w => ⟨Over.homMk (hG.lift u Y.hom w) (hG.lift_snd _ _ _), hG.lift_fst _ _ _⟩`. Take `⟨m', hm'⟩` from `L (G ⊗ G) m (hm₁.trans (isPullback_square hG).w)`. Take `⟨i', hi'⟩` from `L G i (hi₁.trans hG.w)`. Take `⟨e', he'⟩` from `L (𝟙_ _) e (he₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))`.

Use `choose v' hv' using fun j => L G (v j) ((hv₁ j).trans hG.w)`. Take `⟨_, hc, hp⟩` from `grpObj_of_dominant (spMap ψ) G A φ' hφ m' i' e' (fun φ₂ ⟨k₁, k₂⟩ => by`. Apply `hG.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hφ₁, hm']`. Use `hm₂ φ₂ (pullback.hom_ext ?_ ?_)` and prove the remaining obligations.

Rewrite using `[Category.assoc, pullback.lift_fst, pullback.lift_fst, ← hφ₁]`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a) k₁).trans (Category.assoc _ _ _))`. Rewrite using `[Category.assoc, pullback.lift_snd, pullback.lift_snd, ← hφ₁]`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a) k₂).trans (Category.assoc _ _ _))`. Rewrite using `[Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc, ← Over.w (fst G G), reassoc_of% k₁, hφ₂, Over.w_assoc])`.

Use the proof step `(by`. Apply `hG.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hφ₁, hi']`. Conclude with `hi₂ φ' hφ₁`. Rewrite using `[Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc])`.

Use the proof step `(by`. Apply `hG.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hφ₁, he']`. Conclude with `he₂ _ hψ`. Rewrite using `[Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]`.

Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm)`. Use `⟨_, hf, G, inferInstance, φ', v', N, ⟨hc, hsm', hpr', hgc⟩, hp, fun j => ?_, hN, hMN φ' hφ₁⟩` and prove the remaining obligations. Apply `hG.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hφ₁, hv']`. Conclude with `(hv₂ j φ' hφ₁).symm`.

Rewrite using `[Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]`.
-/
theorem exists_model (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) {J : Type} [Fintype J]
    (w : J → (A ⟶ A)) (M : LB A.left) (hM : M.IsLB) :
    ∃ (f : R) (hf : f ≠ 0) (G : Over (Sp (Localization.Away f))) (_ : GrpObj G) (φ : A.left ⟶ G.left)
      (v : J → (G ⟶ G)) (N : LB G.left), IsAbelianScheme G ∧ IsGrpPullback A G (spMap (toFrac R K hf)) φ ∧
      (∀ j, (w j).left ≫ φ = φ ≫ (v j).left) ∧ N.IsLB ∧ LBIso M (N.pull φ) := by
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  obtain ⟨Z, s, φ, hs, h⟩ := exists_projModel R K A.hom (isProjOver_abelian K A hA)
  have hpr : IsProper s := isProper_of_isProjOver hs
  have hfp : LocallyOfFinitePresentation s := inferInstance
  obtain ⟨f₀, hf₀, H₀⟩ := near_smooth_connected R K hs h g hg hA.geomConnected
  obtain ⟨f₁, hf₁, H₁⟩ := near_hom R K (pullback.fst s s ≫ s) s (isPullback_square h) ((μ[A]).left ≫ φ) (by
    rw [(isPullback_square h).w, Category.assoc, h.w, Over.w_assoc]
    rfl)
  obtain ⟨f₂, hf₂, H₂⟩ := near_hom R K s s h ((ι[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])
  obtain ⟨f₃, hf₃, H₃⟩ := near_hom R K (𝟙 _) s (IsPullback.id_vert (spMap (algebraMap R K)))
    ((η[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc]; simp)
  obtain ⟨f₄, hf₄, H₄⟩ := GlobalTheory.GenSpread.exists_lb s h hM
  choose b hb Hb using fun j => near_hom R K s s h ((w j).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])
  have hf₅ : ∏ j, b j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hb j
  have hf : f₀ * f₁ * f₂ * f₃ * f₄ * ∏ j, b j ≠ 0 := by simp only [ne_eq, mul_eq_zero, not_or]; tauto
  let R' := Localization.Away (f₀ * f₁ * f₂ * f₃ * f₄ * ∏ j, b j)
  let c := algebraMap R R'
  have hu : IsUnit (c (f₀ * f₁ * f₂ * f₃ * f₄ * ∏ j, b j)) := IsLocalization.Away.algebraMap_isUnit _
  simp only [map_mul, IsUnit.mul_iff] at hu
  obtain ⟨⟨⟨⟨⟨u₀, u₁⟩, u₂⟩, u₃⟩, u₄⟩, u₅⟩ := hu
  have u₆ : ∀ j, IsUnit (c (b j)) := fun j =>
    isUnit_of_dvd_unit (map_dvd c (Finset.dvd_prod_of_mem b (Finset.mem_univ j))) u₅
  let ψ := toFrac R K hf
  have hψ : spMap ψ ≫ spMap c = spMap (algebraMap R K) := by
    rw [← Spec.map_comp, ← toFrac_comp R K hf]; rfl
  let G : Over (Sp R') := Over.mk (pullback.snd s (spMap c))
  let a : G.left ⟶ Z := pullback.fst s (spMap c)
  have hG : IsPullback a G.hom s (spMap c) := IsPullback.of_hasPullback _ _
  let φ' : A.left ⟶ G.left := hG.lift φ (A.hom ≫ spMap ψ) (by rw [h.w, Category.assoc, hψ])
  have hφ₁ : φ' ≫ a = φ := hG.lift_fst _ _ _
  have hφ₂ : φ' ≫ G.hom = A.hom ≫ spMap ψ := hG.lift_snd _ _ _
  have hφ : IsPullback φ' A.hom G.hom (spMap ψ) := IsPullback.of_right (by rwa [hφ₁, hψ]) hφ₂ hG
  obtain ⟨hsm, hgc⟩ := H₀ R' c u₀
  have hsm' : Smooth G.hom := SmoothOfRelativeDimension.smooth g (pullback.snd s (spMap c))
  have hpr' : IsProper G.hom := inferInstanceAs (IsProper (pullback.snd s (spMap c)))
  obtain ⟨m, hm₁, hm₂⟩ := H₁ R' c u₁ _ _ _ (isPullback_square hG).w
  obtain ⟨i, hi₁, hi₂⟩ := H₂ R' c u₂ _ _ _ hG.w
  obtain ⟨e, he₁, he₂⟩ := H₃ R' c u₃ _ (spMap c) (𝟙 _) (by simp)
  obtain ⟨N, hN, hMN⟩ := H₄ R' c u₄ _ _ _ hG.w
  choose v hv₁ hv₂ using fun j => Hb j R' c (u₆ j) _ _ _ hG.w
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom ψ) (toFrac_injective R K hf)
  have := hA.comm
  have L : ∀ (Y : Over (Sp R')) (u : Y.left ⟶ Z), u ≫ s = Y.hom ≫ spMap c → ∃ v : Y ⟶ G, v.left ≫ a = u :=
    fun Y u w => ⟨Over.homMk (hG.lift u Y.hom w) (hG.lift_snd _ _ _), hG.lift_fst _ _ _⟩
  obtain ⟨m', hm'⟩ := L (G ⊗ G) m (hm₁.trans (isPullback_square hG).w)
  obtain ⟨i', hi'⟩ := L G i (hi₁.trans hG.w)
  obtain ⟨e', he'⟩ := L (𝟙_ _) e (he₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  choose v' hv' using fun j => L G (v j) ((hv₁ j).trans hG.w)
  obtain ⟨_, hc, hp⟩ := grpObj_of_dominant (spMap ψ) G A φ' hφ m' i' e'
    (fun φ₂ ⟨k₁, k₂⟩ => by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hm']
        refine hm₂ φ₂ (pullback.hom_ext ?_ ?_)
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a) k₁).trans (Category.assoc _ _ _))
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a) k₂).trans (Category.assoc _ _ _))
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc, ← Over.w (fst G G), reassoc_of% k₁, hφ₂,
          Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hi']
        exact hi₂ φ' hφ₁
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, he']
        exact he₂ _ hψ
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]
        exact (Category.comp_id _).trans (Category.id_comp _).symm)
  refine ⟨_, hf, G, inferInstance, φ', v', N, ⟨hc, hsm', hpr', hgc⟩, hp, fun j => ?_, hN, hMN φ' hφ₁⟩
  apply hG.hom_ext
  · rw [Category.assoc, Category.assoc, hφ₁, hv']
    exact (hv₂ j φ' hφ₁).symm
  · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]

end PositivityTheory.Xgn.AbelianSchemeSpreading

open PositivityTheory.Xgn.AbelianSchemeSpreading GlobalTheory GlobalTheory.SpreadAb in
/- English proof (translation)
Introduce `E _ _ _ H L _ _ tL hp`. Establish `hA : IsAbelianScheme tL.G` using `⟨tL.comm, tL.semi.smooth, hp, tL.semi.geomConnected⟩`. Take `⟨k, a, ha⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)`. Establish `hcl : Subring.closure (Set.range a) = ⊤`. Use `top_le_iff.1 fun x _ => ?_` and prove the remaining obligations.

Establish `hx : x ∈ Submodule.span ℤ (Set.range a)` using `ha ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Subring.subset_closure hy`. Consider the case `zero => exact zero_mem _`. Consider the case `add y z _ _ hy hz => exact add_mem (hy trivial) (hz trivial)`.

Consider the case `smul c y _ hy => exact zsmul_mem (hy trivial) c`. Take `⟨n, hn, G, _, φ, v, N, hG, gp, hv, hN, hMN⟩` from `exists_model (𝓞 L) L tL.G hA (fun j => tL.act.act (a j)) tL.PP.L tL.PP.isLB`. Set `R` to `Localization.Away n`. Set `ψ : R →+* L` to `toFrac (𝓞 L) L hn`. Establish `hpw : Submonoid.powers n ≤ nonZeroDivisors (𝓞 L)` using `powers_le_nonZeroDivisors_of_noZeroDivisors hn`.

Set `: Algebra R L` to `ψ.toAlgebra`. Establish `: IsScalarTower (𝓞 L) R L` using `IsScalarTower.of_algebraMap_eq' (toFrac_comp (𝓞 L) L hn).symm`. Establish `: IsDomain R` using `IsLocalization.isDomain_localization hpw`. Establish `: IsFractionRing R L` using `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers n) _ L`. Establish `: IsIntegrallyClosed R` using `isIntegrallyClosed_of_isLocalization R (Submonoid.powers n) hpw`.

Establish `hX : Geo.Tor.IsNormalScheme (Sp R)` using `GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R`. Take `⟨_, _⟩ : QuasiCompact (spMap (algebraMap R L)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap R L))` from `ExtUnique.spec_fractionRing R L`. Establish `: Flat (spMap (algebraMap R L))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 (IsLocalization.flat L (nonZeroDivisors R))`.

Establish `: IsPreimmersion (spMap (algebraMap R L))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors R)`. Establish `hd : IsDominant (spMap (algebraMap R L))` using `inferInstance`. Use `replace gp : IsGrpPullback tL.G G (spMap (algebraMap R L)) φ := gp`. Use `hG.smooth` as an intermediate fact. Use `hG.proper` as an intermediate fact.

Use `hG.comm` as an intermediate fact. Establish `hm : ∀ j, IsMonHom (v j)` using `fun j => by`. Use `tL.act.hom (a j)` as an intermediate fact. Conclude with `ExtUnique.isMonHom_of_isGrpPullback gp gp (tL.act.act (a j)) (v j) (hv j)`. Take `⟨r, -, hr⟩` from `oAct_spread_of_dense_fibres (𝓞 E) _ a (Sp R) G v hcl hG hm (hd.denseRange.mono fun p hp => ⟨L, inferInstance, _, tL.G, inferInstance, φ, tL.act, hp, gp, hv⟩)`.

Take `⟨PP, cub, h₁, h₂, h₃, m, -⟩` from `PositivityTheory.Member.SiegelModularCharts.K6.exists_sab_extension hX (spMap (algebraMap R L)) H G (isSemiAbelian_of_isAbelianScheme G hG) r tL φ gp (hr _ _ tL.G φ tL.act gp hv) N hN hMN.symm`. Conclude with `⟨n, hn, _, ψ, fun x => RingHom.congr_fun (toFrac_comp (𝓞 L) L hn) x, ⟨m⟩⟩`.
-/
theorem PositivityTheory.Xgn.abelian_scheme_spreads_over_localization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (tL : SAB H (Sp L)), IsProper tL.G.hom → ∃ (n : 𝓞 L) (_ : n ≠ 0) (T : SAB H (Sp (Localization.Away n))) (f : Localization.Away n →+* L), (∀ x : 𝓞 L, f (algebraMap _ _ x) = (x : L)) ∧ Nonempty (SABMap tL T (spMap f)) := by
  intro E _ _ _ H L _ _ tL hp
  have hA : IsAbelianScheme tL.G := ⟨tL.comm, tL.semi.smooth, hp, tL.semi.geomConnected⟩
  obtain ⟨k, a, ha⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  have hcl : Subring.closure (Set.range a) = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    have hx : x ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Subring.subset_closure hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem (hy trivial) (hz trivial)
    | smul c y _ hy => exact zsmul_mem (hy trivial) c
  obtain ⟨n, hn, G, _, φ, v, N, hG, gp, hv, hN, hMN⟩ :=
    exists_model (𝓞 L) L tL.G hA (fun j => tL.act.act (a j)) tL.PP.L tL.PP.isLB
  let R := Localization.Away n
  let ψ : R →+* L := toFrac (𝓞 L) L hn
  have hpw : Submonoid.powers n ≤ nonZeroDivisors (𝓞 L) := powers_le_nonZeroDivisors_of_noZeroDivisors hn
  let : Algebra R L := ψ.toAlgebra
  have : IsScalarTower (𝓞 L) R L := IsScalarTower.of_algebraMap_eq' (toFrac_comp (𝓞 L) L hn).symm
  have : IsDomain R := IsLocalization.isDomain_localization hpw
  have : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers n) _ L
  have : IsIntegrallyClosed R := isIntegrallyClosed_of_isLocalization R (Submonoid.powers n) hpw
  have hX : Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap R L)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap R L)) :=
    ExtUnique.spec_fractionRing R L
  have : Flat (spMap (algebraMap R L)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat L (nonZeroDivisors R))
  have : IsPreimmersion (spMap (algebraMap R L)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hd : IsDominant (spMap (algebraMap R L)) := inferInstance
  replace gp : IsGrpPullback tL.G G (spMap (algebraMap R L)) φ := gp
  have := hG.smooth
  have := hG.proper
  have := hG.comm
  have hm : ∀ j, IsMonHom (v j) := fun j => by
    have := tL.act.hom (a j)
    exact ExtUnique.isMonHom_of_isGrpPullback gp gp (tL.act.act (a j)) (v j) (hv j)
  obtain ⟨r, -, hr⟩ := oAct_spread_of_dense_fibres (𝓞 E) _ a (Sp R) G v hcl hG hm
    (hd.denseRange.mono fun p hp => ⟨L, inferInstance, _, tL.G, inferInstance, φ, tL.act, hp, gp, hv⟩)
  obtain ⟨PP, cub, h₁, h₂, h₃, m, -⟩ := PositivityTheory.Member.SiegelModularCharts.K6.exists_sab_extension hX (spMap (algebraMap R L)) H G
    (isSemiAbelian_of_isAbelianScheme G hG) r tL φ gp (hr _ _ tL.G φ tL.act gp hv) N hN hMN.symm
  exact ⟨n, hn, _, ψ, fun x => RingHom.congr_fun (toFrac_comp (𝓞 L) L hn) x, ⟨m⟩⟩
