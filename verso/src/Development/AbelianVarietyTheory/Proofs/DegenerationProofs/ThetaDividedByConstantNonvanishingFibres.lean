import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomOfTest
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecGenericEqMulThetaStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericFibreSectionOfModelSectionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorNormalisedMulByNIsoStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSectionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointFactorLargeModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelEqPullbackGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoPullbackUniformisedThetaModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointSpecialFibreSectionNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPadicLiftTorsionPointInvertibleOrderStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralTorsionPointDescendsToModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionSectionEqIntegralPointAtTestStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionRestrictionUnitTwistStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RestrictEqOfSameThetaMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlueSectionsSameThetaMultipleStatement
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ZHPre
open GlobalTheory.Points
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

/- English proof (translation)
Establish `hpt : Set.range M.pt ⊆ Set.range U₀.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `(top_le_preimage_iff M.pt U₀).1 (M.top_le_preimage_pt ov.ne) ⟨w, rfl⟩`. Establish `heta : IsOpenImmersion.lift U₀.ι M.pt hpt ≫ U₀.ι = M.pt` using `IsOpenImmersion.lift_fac _ _ _`.

Take `⟨s, hs⟩` from `GlobalTheory.T.exists_genericFibre_section_of_model_section o Ω S ρ M U₀ Q N σ _ hσ hN heta`. Take `⟨c, hc⟩` from `GlobalTheory.T.sec_generic_eq_mul_theta_alt h1 h2 o Ω S ρ s`. Use `⟨c, ?_⟩` and prove the remaining obligations. Introduce `K _ β g r jP jL hg hr hP hL _`. Establish `hg' : g ≫ pullback.snd _ _ = spMap β ≫ IsOpenImmersion.lift U₀.ι M.pt hpt`.

Rewrite using `[← cancel_mono U₀.ι, Category.assoc, Category.assoc, heta]`. Conclude with `hg`. Establish `hcomm : spMap β ≫ spMap S.R.val.toRingHom = (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ≫ ρ.P.A.hom`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hg', Category.assoc, Q.u₀_gen _ heta]`. Set `q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left` to `pullback.lift (spMap β) (g ≫ pullback.fst _ _) hcomm`.

Establish `hq1 : q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β` using `pullback.lift_fst _ _ _`. Establish `hq2 : q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _` using `pullback.lift_snd _ _ _`. Establish `e1` using `hs K β q g jP jL hq1 hq2.symm hg' hP hL`. Establish `e2` using `hc K β q r jP hq1 (hr.trans hq2.symm) (by rw [hq2]; exact hP)`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton, zpow_one]`.

Rewrite using `[← e2, e1]`.
-/
theorem exists_thMul (h1 : Laws) (h2 : Laws2) (ov : S.Over₀ M U₀) (N : M.Z.Opens) (σ : Q.SecFam N)
    (hσ : σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N)) (hN : (N : Set M.Z).Nonempty) : ∃ c, Q.ThMul c N σ := by
  have hpt : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact (top_le_preimage_iff M.pt U₀).1 (M.top_le_preimage_pt ov.ne) ⟨w, rfl⟩
  have heta : IsOpenImmersion.lift U₀.ι M.pt hpt ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_genericFibre_section_of_model_section o Ω S ρ M U₀ Q N σ _ hσ hN heta
  obtain ⟨c, hc⟩ := GlobalTheory.T.sec_generic_eq_mul_theta_alt h1 h2 o Ω S ρ s
  refine ⟨c, ?_⟩
  intro K _ β g r jP jL hg hr hP hL _
  have hg' : g ≫ pullback.snd _ _ = spMap β ≫ IsOpenImmersion.lift U₀.ι M.pt hpt := by
    rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, heta]
    exact hg
  have hcomm : spMap β ≫ spMap S.R.val.toRingHom = (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ≫ ρ.P.A.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg', Category.assoc, Q.u₀_gen _ heta]
  let q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left :=
    pullback.lift (spMap β) (g ≫ pullback.fst _ _) hcomm
  have hq1 : q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β :=
    pullback.lift_fst _ _ _
  have hq2 : q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left =
      g ≫ pullback.fst _ _ :=
    pullback.lift_snd _ _ _
  have e1 := hs K β q g jP jL hq1 hq2.symm hg' hP hL
  have e2 := hc K β q r jP hq1 (hr.trans hq2.symm) (by rw [hq2]; exact hP)
  simp only [Finset.univ_unique, Finset.sum_singleton, zpow_one]
  rw [← e2, e1]

/- English proof (translation)
Use `haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)`. Use `haveI : CharZero Ω := ArithBase.char (o := o)`. Take `⟨⟨p, hp, y, hy⟩, -⟩` from `(classical_points_and_local_regularity o Ω M U₀ ov.normal).1 U₀ le_rfl ov.ne z hz`. Take `⟨y₀, Fs, hAt, hint, hfac⟩` from `GlobalTheory.T.exists_classical_point_factor_large_model o Ω S ρ M U₀ Q ov z p y hy`. Take `⟨u, l, τ, hmatch, hFs⟩` from `(GlobalTheory.T.thetaSystem_hasTests_of_real_point hs hU h1 h2 hT o Ω S ρ).2 p y₀ Fs hint`.

Take `⟨jV, yV, yK, hTF⟩` from `hfac u hFs`. Take `⟨F, ψ, hTM⟩` from `GlobalTheory.T.exists_testMap_of_testFac h0 o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF`. Establish `hLB` using `GlobalTheory.T.lineBundleIso_pullback_uniformisedThetaModel o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM`. Establish `hyN : y (cPt p) ∈ N` using `by rw [hy.1]; exact hzN`. Take `⟨t, ht, j, hj⟩` from `GlobalTheory.T.exists_torsionPoint_specialFibre_section_ne_zero h1 h2 o Ω S ρ M U₀ Q big p y y₀ u jV yV yK hTF F ψ hTM hLB N σ hσ hne hyN`.

Establish `hn : IsUnit ((S.r * S.N : ℕ) : Γ(Sp u.V, ⊤))`. Establish `hv : IsUnit ((S.r * S.N : ℕ) : u.V)`. Establish `he : ((S.r * S.N : ℕ) : o) * ↑(S.unit.unit⁻¹) = 1` using `S.unit.mul_val_inv`. Establish `hnorm : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (u.yK (algebraMap o S.R ↑(S.unit.unit⁻¹)))‖ ≤ 1`. Establish `hf` using `RingHom.congr_fun u.fac (algebraMap o S.R ↑(S.unit.unit⁻¹))`.

Rewrite `hf` using `[RingHom.comp_apply]`. Rewrite using `[hf]`. Conclude with `hint _`. Take `⟨v, hvE⟩` from `(u.norm_le _).1 hnorm`. Establish `hmul : ((S.r * S.N : ℕ) : u.V) * v = 1`.

Apply `IsFractionRing.injective u.V (FractionRing u.V)` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, hvE, map_natCast, ← map_natCast u.yK, ← map_natCast (algebraMap o S.R), ← map_mul, ← map_mul, he, map_one, map_one]`. Conclude with `⟨⟨_, v, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩`. Simplify using `using hv.map (Scheme.ΓSpecIso (CommRingCat.of u.V)).inv.hom`. Take `⟨b, hb, hbt⟩` from `GlobalTheory.T.exists_padicLift_torsionPoint_invertibleOrder p (Sp u.V) u.G u.semi (spMap jV) (S.r * S.N) hn t ht`.

Take `⟨a, hV, x, ⟨hV1, hx1, hx2, hx3⟩, hbV⟩` from `GlobalTheory.T.integral_torsion_point_descends_to_model o Ω S ρ p y₀ u jV hTF.1 b hb`. Establish `hker : a ∈ τ.yy.ker`. Take `⟨e, -, he⟩` from `hmatch`. Establish `hl : l.yy a = 0` using `(AddMonoidHom.mem_ker).1 ((l.ker_iff a).2 ⟨hV, x, hV1, hx1, hx2, hx3⟩)`. Establish `h0' : τ.yy a = QuotientAddGroup.mk 0` using `(he a 0).2 (by rw [hl, map_zero]; rfl)`.

Rewrite using `[AddMonoidHom.mem_ker, h0']`. Both sides reduce to the same expression. Establish `hHH` using `(ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ ov z p y y₀ τ hy hAt).2`. Use `⟨a, by rw [hHH]; exact hker, ?_⟩` and prove the remaining obligations. Introduce `W h w hExt hwz`.

Use `haveI := isLocalHom_of_test u jV hTF.1`. Establish `hzW : z ∈ W`. Establish `hr : z ∈ Set.range W.ι` using `⟨w, hwz⟩`. Rewrite `hr` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis. Establish `hVz : yV (IsLocalRing.closedPoint u.V) = z`.

Rewrite using `[← hy.1, ← hTF.2.1, Scheme.Hom.comp_apply]`. Use `congr 1`. Conclude with `(IsLocalRing.comap_closedPoint jV).symm`. Establish `hsp : ∀ v, yV v ⤳ z` using `fun v => hVz ▸ (IsLocalRing.specializes_closedPoint v).map yV.continuous`. Establish `hrange : Set.range yV ⊆ Set.range W.ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `(top_le_preimage_iff yV W).1 (top_le_preimage_of_specializes hsp hzW)`. Establish `hyW : IsOpenImmersion.lift W.ι yV hrange ≫ W.ι = yV` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hcomp` using `GlobalTheory.T.torsionSection_eq_integral_point_at_test o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM a W h hExt hV x ⟨hV1, hx1, hx2, hx3⟩ _ hyW`. Use `⟨IsLocalRing.ResidueField (OO p), inferInstance, spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange, j, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.range_unique]`. Use `congr 1`. Apply `W.ι.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[hwz, ← Scheme.Hom.comp_apply]`. Simplify using `only [Category.assoc, hyW, hTF.2.1]`.

Rewrite using `[Scheme.Hom.comp_apply, ← hy.1]`. Use `congr 1`. Rewrite using `[show (default : Sp (IsLocalRing.ResidueField (OO p))) = IsLocalRing.closedPoint _ from Subsingleton.elim _ _]`. Conclude with `IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))`. Establish `hx : (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange) ≫ h = t.left ≫ F`.

Rewrite using `[Category.assoc, Category.assoc, hcomp, ← Category.assoc (spMap jV), hbV, ← Category.assoc, hbt]`. Rewrite using `[hx]`. Conclude with `hj`.
-/
theorem exists_good_label (h0 : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)) (hs : GlobalTheory.Published.SemistableReductionSt) (hU : ThmUSt) (h1 : Laws) (h2 : Laws2)
    (hT : UTorsSt) (big : S.Big) (ov : S.Over₀ M U₀) (N : M.Z.Opens) (σ : Q.SecFam N)
    (hσ : σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N)) (hne : Q.FibNe N σ) (z : M.Z) (hz : IsClosed ({z} : Set M.Z))
    (hzN : z ∈ N) : ∃ a ∈ S.HH M z, ∀ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme),
      Q.ExtPt a W h → W.ι w = z → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι),
        Set.range x = {w} ∧ valF (x ≫ h) _ (σ j) ≠ 0 := by
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)
  haveI : CharZero Ω := ArithBase.char (o := o)
  obtain ⟨⟨p, hp, y, hy⟩, -⟩ := (classical_points_and_local_regularity o Ω M U₀ ov.normal).1 U₀ le_rfl ov.ne z hz
  obtain ⟨y₀, Fs, hAt, hint, hfac⟩ := GlobalTheory.T.exists_classical_point_factor_large_model o Ω S ρ M U₀ Q ov z p y hy
  obtain ⟨u, l, τ, hmatch, hFs⟩ := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hs hU h1 h2 hT o Ω S ρ).2 p y₀ Fs hint
  obtain ⟨jV, yV, yK, hTF⟩ := hfac u hFs
  obtain ⟨F, ψ, hTM⟩ := GlobalTheory.T.exists_testMap_of_testFac h0 o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF
  have hLB := GlobalTheory.T.lineBundleIso_pullback_uniformisedThetaModel o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM
  have hyN : y (cPt p) ∈ N := by rw [hy.1]; exact hzN
  obtain ⟨t, ht, j, hj⟩ := GlobalTheory.T.exists_torsionPoint_specialFibre_section_ne_zero h1 h2 o Ω S ρ M U₀ Q big p y y₀ u jV yV yK hTF F ψ hTM hLB N σ hσ hne hyN
  have hn : IsUnit ((S.r * S.N : ℕ) : Γ(Sp u.V, ⊤)) := by
    have hv : IsUnit ((S.r * S.N : ℕ) : u.V) := by
      have he : ((S.r * S.N : ℕ) : o) * ↑(S.unit.unit⁻¹) = 1 := S.unit.mul_val_inv
      have hnorm : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (u.yK (algebraMap o S.R ↑(S.unit.unit⁻¹)))‖ ≤ 1 := by
        have hf := RingHom.congr_fun u.fac (algebraMap o S.R ↑(S.unit.unit⁻¹))
        rw [RingHom.comp_apply] at hf
        rw [hf]
        exact hint _
      obtain ⟨v, hvE⟩ := (u.norm_le _).1 hnorm
      have hmul : ((S.r * S.N : ℕ) : u.V) * v = 1 := by
        apply IsFractionRing.injective u.V (FractionRing u.V)
        rw [map_mul, map_one, hvE, map_natCast, ← map_natCast u.yK, ← map_natCast (algebraMap o S.R),
          ← map_mul, ← map_mul, he, map_one, map_one]
      exact ⟨⟨_, v, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
    simpa using hv.map (Scheme.ΓSpecIso (CommRingCat.of u.V)).inv.hom
  obtain ⟨b, hb, hbt⟩ := GlobalTheory.T.exists_padicLift_torsionPoint_invertibleOrder p (Sp u.V) u.G u.semi (spMap jV) (S.r * S.N) hn t ht
  obtain ⟨a, hV, x, ⟨hV1, hx1, hx2, hx3⟩, hbV⟩ := GlobalTheory.T.integral_torsion_point_descends_to_model o Ω S ρ p y₀ u jV hTF.1 b hb
  have hker : a ∈ τ.yy.ker := by
    obtain ⟨e, -, he⟩ := hmatch
    have hl : l.yy a = 0 := (AddMonoidHom.mem_ker).1 ((l.ker_iff a).2 ⟨hV, x, hV1, hx1, hx2, hx3⟩)
    have h0' : τ.yy a = QuotientAddGroup.mk 0 := (he a 0).2 (by rw [hl, map_zero]; rfl)
    rw [AddMonoidHom.mem_ker, h0']
    rfl
  have hHH := (ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ ov z p y y₀ τ hy hAt).2
  refine ⟨a, by rw [hHH]; exact hker, ?_⟩
  intro W h w hExt hwz
  haveI := isLocalHom_of_test u jV hTF.1
  have hzW : z ∈ W := by
    have hr : z ∈ Set.range W.ι := ⟨w, hwz⟩
    rwa [Scheme.Opens.range_ι] at hr
  have hVz : yV (IsLocalRing.closedPoint u.V) = z := by
    rw [← hy.1, ← hTF.2.1, Scheme.Hom.comp_apply]
    congr 1
    exact (IsLocalRing.comap_closedPoint jV).symm
  have hsp : ∀ v, yV v ⤳ z := fun v => hVz ▸ (IsLocalRing.specializes_closedPoint v).map yV.continuous
  have hrange : Set.range yV ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff yV W).1 (top_le_preimage_of_specializes hsp hzW)
  have hyW : IsOpenImmersion.lift W.ι yV hrange ≫ W.ι = yV := IsOpenImmersion.lift_fac _ _ _
  have hcomp := GlobalTheory.T.torsionSection_eq_integral_point_at_test o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM a W h hExt hV x
    ⟨hV1, hx1, hx2, hx3⟩ _ hyW
  refine ⟨IsLocalRing.ResidueField (OO p), inferInstance,
    spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange, j, ?_, ?_⟩
  · rw [Set.range_unique]
    congr 1
    apply W.ι.isOpenEmbedding.injective
    rw [hwz, ← Scheme.Hom.comp_apply]
    simp only [Category.assoc, hyW, hTF.2.1]
    rw [Scheme.Hom.comp_apply, ← hy.1]
    congr 1
    rw [show (default : Sp (IsLocalRing.ResidueField (OO p))) = IsLocalRing.closedPoint _ from
      Subsingleton.elim _ _]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  · have hx : (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange) ≫ h =
        t.left ≫ F := by
      rw [Category.assoc, Category.assoc, hcomp, ← Category.assoc (spMap jV), hbV, ← Category.assoc, hbt]
    rw [hx]
    exact hj

/- English proof (translation)
Introduce `h0 hs hU h1 h2 hT o Ω _ _ _ _ S ρ M U₀ Q big ov hSec hLoc W x₀ hx₀`. Use `GlobalTheory.T.exists_glue_sections_same_theta_multiple o Ω S ρ M U₀ Q (S.th x₀)⁻¹ (fun N N' σ σ' hσ hσ' j O h h' => GlobalTheory.T.restrict_eq_of_same_theta_multiple o Ω S ρ M U₀ Q ov N N' σ σ' _ hσ hσ' j O h h') W ?_` and prove the remaining obligations. Introduce `z hzW`. Use `haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)`. Use `haveI : CharZero Ω := ArithBase.char (o := o)`.

Use `haveI : JacobsonSpace M.Z := (classical_points_and_local_regularity o Ω M U₀ ov.normal).2`. Take `⟨N₀, σ₀, hzN₀, hσ₀, hne₀⟩` from `GlobalTheory.T.exists_localThetaSection_fibreNonzero o Ω S ρ M U₀ Q hLoc z`. Take `⟨c₀, hc₀⟩` from `Q.exists_thMul h1 h2 ov N₀ σ₀ hσ₀ ⟨z, hzN₀⟩`. Establish `hext : ∀ (z' : M.Z), ∀ b ∈ S.HH M z', ∃ (Wb : M.Z.Opens) (hb : Wb.toScheme ⟶ Q.G.left) (wb : Wb.toScheme), Q.ExtPt b Wb hb ∧ Wb.ι wb = z' ∧ Q.FrameUnit b Wb hb wb`. Introduce `z' b hb`.

Take `⟨Wb, hb', hz'Wb, hb1, hb2⟩` from `hSec z' b hb`. Take `⟨wb, hwb⟩ : z' ∈ Set.range Wb.ι` from `by rw [Scheme.Opens.range_ι]; exact hz'Wb`. Establish `hE : Q.ExtPt b Wb hb'` using `⟨hb1, hb2⟩`. Conclude with `⟨Wb, hb', wb, hE, hwb, GlobalTheory.T.torsionFrame_isUnit_along_section o Ω S ρ M U₀ Q ov (fun α hα hn => GlobalTheory.T.exists_generator_normalised_mulByN_iso o Ω S ρ M U₀ Q ov (S.r * S.N) α hα hn) b Wb hb' wb hE⟩`. Establish `hcl : ∀ z' : M.Z, IsClosed ({z'} : Set M.Z) → z' ∈ N₀ → z' ∈ W → c₀ * S.th x₀ ≠ 0 ∧ c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'`.

Introduce `z' hz' hz'N hz'W`. Take `⟨a, ha, hgood⟩` from `Q.exists_good_label h0 hs hU h1 h2 hT big ov N₀ σ₀ hσ₀ hne₀ z' hz' hz'N`. Take `⟨Wa, ha', wa, hEa, hwa, hFa⟩` from `hext z' a ha`. Establish `hwaN : Wa.ι wa ∈ N₀` using `by rw [hwa]; exact hz'N`. Establish `hxa` using `GlobalTheory.T.theta_mul_regular_and_unit_along_torsion o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ a Wa ha' wa hEa hFa hwaN`.

Take `⟨K, _, x, j, hx, hv⟩` from `hgood Wa ha' wa hEa hwa`. Take `⟨hne, hinv⟩` from `hxa.2 K x j hx hv`. Establish `hx₀' : x₀ ∈ S.supI M z'` using `hx₀ z' hz'W`. Take `⟨Wb, hb', wb, hEb, hwb, hFb⟩` from `hext z' x₀ (AddSubgroup.subset_closure hx₀')`. Establish `hwbN : Wb.ι wb ∈ N₀` using `by rw [hwb]; exact hz'N`.

Establish `hxb` using `(GlobalTheory.T.theta_mul_regular_and_unit_along_torsion o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ x₀ Wb hb' wb hEb hFb hwbN).1`. Rewrite `hinv` using `[hwa]`. Rewrite `hxb` using `[hwb]`. Establish `hdiv : M.Div S.th x₀ z'` using `hx₀'`. Take `⟨hth, hdivs⟩` from `hdiv`.

Establish `hc : c₀ ≠ 0` using `left_ne_zero_of_mul hne`. Establish `hta : S.th a ≠ 0` using `right_ne_zero_of_mul hne`. Use `⟨mul_ne_zero hc hth, hxb, ?_⟩` and prove the remaining obligations. Establish `heq : (c₀ * S.th x₀)⁻¹ = S.th a / S.th x₀ * (c₀ * S.th a)⁻¹`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[heq]`. Conclude with `Subalgebra.mul_mem _ (hdivs a) hinv`. Establish `hopen : IsOpen {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'}` using `(M.isOpen_setOf_mem_O _).inter (M.isOpen_setOf_mem_O _)`. Establish `hall : ∀ z' : M.Z, z' ∈ N₀ → z' ∈ W → c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Take `⟨z₂, hz₂N, hz₂W, hbad⟩` from `hcon`. Establish `hZ : (((N₀ : Set M.Z) ∩ (W : Set M.Z)) ∩ {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'}ᶜ).Nonempty` using `⟨z₂, ⟨hz₂N, hz₂W⟩, fun h => hbad h.1 h.2⟩`. Take `⟨z', ⟨⟨hz'N, hz'W⟩, hz'bad⟩, hz'c⟩` from `nonempty_inter_closedPoints hZ ⟨_, _, N₀.isOpen.inter W.isOpen, hopen.isClosed_compl, rfl⟩`. Take `⟨-, h1', h2'⟩` from `hcl z' hz'c hz'N hz'W`.

Conclude with `hz'bad ⟨h1', h2'⟩`. Take `⟨z₁, ⟨hz₁N, hz₁W⟩, hz₁c⟩` from `nonempty_inter_closedPoints (⟨z, hzN₀, hzW⟩ : ((N₀ : Set M.Z) ∩ (W : Set M.Z)).Nonempty) (N₀.isOpen.inter W.isOpen).isLocallyClosed`. Establish `hf0 : c₀ * S.th x₀ ≠ 0` using `(hcl z₁ hz₁c hz₁N hz₁W).1`. Take `⟨σ', hσ', hth', hne'⟩` from `GlobalTheory.T.theta_section_restriction_unit_twist o Ω S ρ M U₀ Q N₀ (N₀ ⊓ W) σ₀ c₀ (c₀ * S.th x₀)⁻¹ inf_le_left (fun z' hz' => by`. Take `⟨hz'N, hz'W⟩` from `hz'`.

Take `⟨h1', h2'⟩` from `hall z' hz'N hz'W`. Conclude with `⟨inv_ne_zero hf0, h2', by rw [inv_inv]; exact h1'⟩) hσ₀ hc₀ hne₀`. Establish `hc₀0 : c₀ ≠ 0` using `left_ne_zero_of_mul hf0`. Establish `hth0 : S.th x₀ ≠ 0` using `right_ne_zero_of_mul hf0`. Establish `hfc : (c₀ * S.th x₀)⁻¹ * c₀ = (S.th x₀)⁻¹`.

Clear the denominators using the available nonvanishing facts. Rewrite `hth'` using `[hfc]`. Conclude with `⟨N₀ ⊓ W, σ', ⟨hzN₀, hzW⟩, inf_le_right, hσ', hth', hne'⟩`.
-/
theorem exists_theta_div : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → S.Over₀ M U₀ → Q.Sec → Q.LocTheta → ∀ (W : M.Z.Opens) (x₀ : S.Gam), (∀ z ∈ W, x₀ ∈ S.supI M z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th x₀)⁻¹) _ σ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0 := by
  intro h0 hs hU h1 h2 hT o Ω _ _ _ _ S ρ M U₀ Q big ov hSec hLoc W x₀ hx₀
  refine GlobalTheory.T.exists_glue_sections_same_theta_multiple o Ω S ρ M U₀ Q (S.th x₀)⁻¹
    (fun N N' σ σ' hσ hσ' j O h h' => GlobalTheory.T.restrict_eq_of_same_theta_multiple o Ω S ρ M U₀ Q ov N N' σ σ' _ hσ hσ' j O h h') W ?_
  intro z hzW
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : JacobsonSpace M.Z := (classical_points_and_local_regularity o Ω M U₀ ov.normal).2
  obtain ⟨N₀, σ₀, hzN₀, hσ₀, hne₀⟩ := GlobalTheory.T.exists_localThetaSection_fibreNonzero o Ω S ρ M U₀ Q hLoc z
  obtain ⟨c₀, hc₀⟩ := Q.exists_thMul h1 h2 ov N₀ σ₀ hσ₀ ⟨z, hzN₀⟩
  have hext : ∀ (z' : M.Z), ∀ b ∈ S.HH M z', ∃ (Wb : M.Z.Opens) (hb : Wb.toScheme ⟶ Q.G.left) (wb : Wb.toScheme),
      Q.ExtPt b Wb hb ∧ Wb.ι wb = z' ∧ Q.FrameUnit b Wb hb wb := by
    intro z' b hb
    obtain ⟨Wb, hb', hz'Wb, hb1, hb2⟩ := hSec z' b hb
    obtain ⟨wb, hwb⟩ : z' ∈ Set.range Wb.ι := by rw [Scheme.Opens.range_ι]; exact hz'Wb
    have hE : Q.ExtPt b Wb hb' := ⟨hb1, hb2⟩
    exact ⟨Wb, hb', wb, hE, hwb, GlobalTheory.T.torsionFrame_isUnit_along_section o Ω S ρ M U₀ Q ov
      (fun α hα hn => GlobalTheory.T.exists_generator_normalised_mulByN_iso o Ω S ρ M U₀ Q ov (S.r * S.N) α hα hn) b Wb hb' wb hE⟩
  have hcl : ∀ z' : M.Z, IsClosed ({z'} : Set M.Z) → z' ∈ N₀ → z' ∈ W →
      c₀ * S.th x₀ ≠ 0 ∧ c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z' := by
    intro z' hz' hz'N hz'W
    obtain ⟨a, ha, hgood⟩ := Q.exists_good_label h0 hs hU h1 h2 hT big ov N₀ σ₀ hσ₀ hne₀ z' hz' hz'N
    obtain ⟨Wa, ha', wa, hEa, hwa, hFa⟩ := hext z' a ha
    have hwaN : Wa.ι wa ∈ N₀ := by rw [hwa]; exact hz'N
    have hxa := GlobalTheory.T.theta_mul_regular_and_unit_along_torsion o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ a Wa ha' wa hEa hFa hwaN
    obtain ⟨K, _, x, j, hx, hv⟩ := hgood Wa ha' wa hEa hwa
    obtain ⟨hne, hinv⟩ := hxa.2 K x j hx hv
    have hx₀' : x₀ ∈ S.supI M z' := hx₀ z' hz'W
    obtain ⟨Wb, hb', wb, hEb, hwb, hFb⟩ := hext z' x₀ (AddSubgroup.subset_closure hx₀')
    have hwbN : Wb.ι wb ∈ N₀ := by rw [hwb]; exact hz'N
    have hxb := (GlobalTheory.T.theta_mul_regular_and_unit_along_torsion o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ x₀ Wb hb' wb hEb hFb hwbN).1
    rw [hwa] at hinv
    rw [hwb] at hxb
    have hdiv : M.Div S.th x₀ z' := hx₀'
    obtain ⟨hth, hdivs⟩ := hdiv
    have hc : c₀ ≠ 0 := left_ne_zero_of_mul hne
    have hta : S.th a ≠ 0 := right_ne_zero_of_mul hne
    refine ⟨mul_ne_zero hc hth, hxb, ?_⟩
    have heq : (c₀ * S.th x₀)⁻¹ = S.th a / S.th x₀ * (c₀ * S.th a)⁻¹ := by
      field_simp
    rw [heq]
    exact Subalgebra.mul_mem _ (hdivs a) hinv
  have hopen : IsOpen {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'} :=
    (M.isOpen_setOf_mem_O _).inter (M.isOpen_setOf_mem_O _)
  have hall : ∀ z' : M.Z, z' ∈ N₀ → z' ∈ W → c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z' := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₂, hz₂N, hz₂W, hbad⟩ := hcon
    have hZ : (((N₀ : Set M.Z) ∩ (W : Set M.Z)) ∩
        {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'}ᶜ).Nonempty :=
      ⟨z₂, ⟨hz₂N, hz₂W⟩, fun h => hbad h.1 h.2⟩
    obtain ⟨z', ⟨⟨hz'N, hz'W⟩, hz'bad⟩, hz'c⟩ := nonempty_inter_closedPoints hZ
      ⟨_, _, N₀.isOpen.inter W.isOpen, hopen.isClosed_compl, rfl⟩
    obtain ⟨-, h1', h2'⟩ := hcl z' hz'c hz'N hz'W
    exact hz'bad ⟨h1', h2'⟩
  obtain ⟨z₁, ⟨hz₁N, hz₁W⟩, hz₁c⟩ := nonempty_inter_closedPoints
    (⟨z, hzN₀, hzW⟩ : ((N₀ : Set M.Z) ∩ (W : Set M.Z)).Nonempty) (N₀.isOpen.inter W.isOpen).isLocallyClosed
  have hf0 : c₀ * S.th x₀ ≠ 0 := (hcl z₁ hz₁c hz₁N hz₁W).1
  obtain ⟨σ', hσ', hth', hne'⟩ := GlobalTheory.T.theta_section_restriction_unit_twist o Ω S ρ M U₀ Q N₀ (N₀ ⊓ W) σ₀ c₀ (c₀ * S.th x₀)⁻¹ inf_le_left
    (fun z' hz' => by
      obtain ⟨hz'N, hz'W⟩ := hz'
      obtain ⟨h1', h2'⟩ := hall z' hz'N hz'W
      exact ⟨inv_ne_zero hf0, h2', by rw [inv_inv]; exact h1'⟩) hσ₀ hc₀ hne₀
  have hc₀0 : c₀ ≠ 0 := left_ne_zero_of_mul hf0
  have hth0 : S.th x₀ ≠ 0 := right_ne_zero_of_mul hf0
  have hfc : (c₀ * S.th x₀)⁻¹ * c₀ = (S.th x₀)⁻¹ := by
    field_simp
  rw [hfc] at hth'
  exact ⟨N₀ ⊓ W, σ', ⟨hzN₀, hzW⟩, inf_le_right, hσ', hth', hne'⟩

end GlobalTheory.ZH.ZHPre
end
