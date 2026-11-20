import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.ThetaExt

open TopologicalSpace

noncomputable def invMul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) (c : Γ(X, ⊤)ˣ) : LB.Iso B A :=
  ⟨fun p => res (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) c *
    (res (fun _ hy => ⟨hy.2, hy.1⟩ : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹⟩

/- English proof (translation)
The claim follows from `have hp : (𝟙 X : X ⟶ X) y ∈ A.U a ⊓ B.U b := ⟨ha, hb⟩ (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _) ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))))`.
-/
theorem gm_invMul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) (c : Γ(X, ⊤)ˣ) (y : X) (a : A.ι) (b : B.ι)
    (ha : y ∈ A.U a) (hb : y ∈ B.U b) : gm (𝟙 X) y (A.U a ⊓ B.U b) ((invMul w c).s (a, b)) =
      gm (𝟙 X) y ⊤ c * (gm (𝟙 X) y (B.U b ⊓ A.U a) (w.s (b, a)))⁻¹ :=
  have hp : (𝟙 X : X ⟶ X) y ∈ A.U a ⊓ B.U b := ⟨ha, hb⟩
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))))

/- English proof (translation)
Introduce and unpack `⟨a, b⟩ ⟨a', b'⟩`. Use `unit_ext fun y hy => ?_` and prove the remaining obligations. Establish `hm : (𝟙 X : X ⟶ X) y ∈ B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a')` using `⟨⟨hy.1.2, hy.1.1⟩, hy.2.2, hy.2.1⟩`. Establish `e` using `congrArg (gm (𝟙 X) y (B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a'))) (hw (b, a) (b', a'))`. Establish `e'` using `(gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 X) y (b, a) (b', a') hm) (gm_res _ y _ hm _))))`.

Establish `alg : ∀ {a b t s u : (X.presheaf.stalk y)ˣ}, u = b * a⁻¹ * s → t * u⁻¹ = a * b⁻¹ * (t * s⁻¹)`. Introduce and unpack `a b t s _ rfl`. Rewrite using `[mul_inv, mul_inv, inv_inv, mul_comm a, mul_left_comm]`. Conclude with `((gm_res _ y _ hy _).trans (gm_invMul w c y a b hy.1.1 hy.1.2)).trans ((alg e').trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y (a, b) (a', b') hy) ((gm_res _ y _ hy _).trans (gm_invMul w c y a' b' hy.2.1 hy.2.2)))).symm)`.
-/
theorem isGen_invMul {X : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (c : Γ(X, ⊤)ˣ) :
    (invMul w c).IsGen := by
  rintro ⟨a, b⟩ ⟨a', b'⟩
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a') := ⟨⟨hy.1.2, hy.1.1⟩, hy.2.2, hy.2.1⟩
  have e := congrArg (gm (𝟙 X) y (B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a'))) (hw (b, a) (b', a'))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (b, a) (b', a') hm) (gm_res _ y _ hm _))))
  have alg : ∀ {a b t s u : (X.presheaf.stalk y)ˣ}, u = b * a⁻¹ * s → t * u⁻¹ = a * b⁻¹ * (t * s⁻¹) := by
    rintro a b t s _ rfl
    rw [mul_inv, mul_inv, inv_inv, mul_comm a, mul_left_comm]
  exact ((gm_res _ y _ hy _).trans (gm_invMul w c y a b hy.1.1 hy.1.2)).trans ((alg e').trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y (a, b) (a', b') hy)
      ((gm_res _ y _ hy _).trans (gm_invMul w c y a' b' hy.2.1 hy.2.2)))).symm)

variable {C : Core} (T : C.Theta) {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)

/- English proof (translation)
Use `τ.j_loc` as an intermediate fact. Establish `h : spMap τ.j (cPt p) = IsLocalRing.closedPoint τ.V` using `IsLocalRing.comap_closedPoint τ.j`. Establish `e : y (cPt p) = τ.y₀ (IsLocalRing.closedPoint τ.V)`. Rewrite using `[← h]`. Conclude with `(congrArg (fun g => g (cPt p)) τ.fac).symm`.

Rewrite using `[← e]`. Conclude with `GlobalTheory.ZH.isClosed_singleton_cPt y`.
-/
theorem isClosed_closedPoint : IsClosed ({τ.y₀ (IsLocalRing.closedPoint τ.V)} : Set C.Z) := by
  have := τ.j_loc
  have h : spMap τ.j (cPt p) = IsLocalRing.closedPoint τ.V := IsLocalRing.comap_closedPoint τ.j
  have e : y (cPt p) = τ.y₀ (IsLocalRing.closedPoint τ.V) := by
    rw [← h]
    exact (congrArg (fun g => g (cPt p)) τ.fac).symm
  rw [← e]
  exact GlobalTheory.ZH.isClosed_singleton_cPt y

/- English proof (translation)
Take `⟨x₀, hx₀, e₀⟩` from `T.s_ne _ (isClosed_closedPoint τ)`. Take `⟨x₁, e₁, -⟩` from `Scheme.exists_preimage_of_isPullback h x₀ _ e₀`. Take `⟨_, hx₂, x₂, rfl⟩` from `nonempty_preirreducible_inter (τ.f ⁻¹ᵁ Out.nonzeroLocus T.s).isOpen (pullback.fst τ.H.hom (Out.jK τ.V)).isOpenEmbedding.isOpen_range ⟨x₁, show τ.f x₁ ∈ _ by rw [e₁]; exact hx₀⟩ (Set.range_nonempty _)`. Establish `e₂ : C.a (τ.φ x₂) = τ.f (pullback.fst τ.H.hom (Out.jK τ.V) x₂)` using `congrArg (fun g => g x₂) τ.φ_f`. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (show C.a (τ.φ x₂) ∈ Out.nonzeroLocus T.s by rw [e₂]; exact hx₂)`.

Establish `hi'` using `C.G.toScheme.basicOpen_le _ hi`. Take `⟨k, hk⟩` from `exists_chart T.L.isLB ((mulN C.A T.m).left (τ.φ x₂))`. Establish `u` using `(SecPullIso.isUnit_gs_iff C.a _ hi' _).2 hi`. Rewrite `u` using `[T.w_sec _ i k hi' hk]`. Establish `u'` using `(SecPullIso.isUnit_gs_iff _ _ hk _).1 (isUnit_of_mul_isUnit_right u)`.

Take `⟨x₃, e₃, -⟩` from `Scheme.exists_preimage_of_isPullback τ.φ_cart.1 ((mulN C.A T.m).left (τ.φ x₂)) (((Over.pullback (Out.jK τ.V)).obj τ.H).hom x₂) ((congrArg (fun g => g (τ.φ x₂)) (Over.w (mulN C.A T.m))).trans (congrArg (fun g => g x₂) τ.φ_cart.1.w))`. Conclude with `⟨x₃, k, by rw [← e₃] at u'; exact u'⟩`.
-/
theorem exists_mem_basicOpen [IsIntegral τ.H.left] [Nonempty (pullback τ.H.hom (Out.jK τ.V) :)]
    [IsOpenImmersion (pullback.fst τ.H.hom (Out.jK τ.V))] (h : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) :
    ∃ (x : (pullback τ.H.hom (Out.jK τ.V) :)) (k : T.L.L.ι), τ.φ x ∈ C.A.left.basicOpen (T.θ.f k) := by
  obtain ⟨x₀, hx₀, e₀⟩ := T.s_ne _ (isClosed_closedPoint τ)
  obtain ⟨x₁, e₁, -⟩ := Scheme.exists_preimage_of_isPullback h x₀ _ e₀
  obtain ⟨_, hx₂, x₂, rfl⟩ := nonempty_preirreducible_inter (τ.f ⁻¹ᵁ Out.nonzeroLocus T.s).isOpen
    (pullback.fst τ.H.hom (Out.jK τ.V)).isOpenEmbedding.isOpen_range ⟨x₁, show τ.f x₁ ∈ _ by rw [e₁]; exact hx₀⟩
    (Set.range_nonempty _)
  have e₂ : C.a (τ.φ x₂) = τ.f (pullback.fst τ.H.hom (Out.jK τ.V) x₂) := congrArg (fun g => g x₂) τ.φ_f
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show C.a (τ.φ x₂) ∈ Out.nonzeroLocus T.s by rw [e₂]; exact hx₂)
  have hi' := C.G.toScheme.basicOpen_le _ hi
  obtain ⟨k, hk⟩ := exists_chart T.L.isLB ((mulN C.A T.m).left (τ.φ x₂))
  have u := (SecPullIso.isUnit_gs_iff C.a _ hi' _).2 hi
  rw [T.w_sec _ i k hi' hk] at u
  have u' := (SecPullIso.isUnit_gs_iff _ _ hk _).1 (isUnit_of_mul_isUnit_right u)
  obtain ⟨x₃, e₃, -⟩ := Scheme.exists_preimage_of_isPullback τ.φ_cart.1 ((mulN C.A T.m).left (τ.φ x₂))
    (((Over.pullback (Out.jK τ.V)).obj τ.H).hom x₂)
    ((congrArg (fun g => g (τ.φ x₂)) (Over.w (mulN C.A T.m))).trans (congrArg (fun g => g x₂) τ.φ_cart.1.w))
  exact ⟨x₃, k, by rw [← e₃] at u'; exact u'⟩

end GlobalTheory.ZJ.ThetaExt

namespace GlobalTheory.ZJ

open ThetaExt TopologicalSpace

/- English proof (translation)
Introduce `hE C T p _ y τ hC`. Establish `hG` using `τ.isSemiAbelian`. Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact.

Use `hG.geomConnected` as an intermediate fact. Use `grpObj_geometricallyIntegral_of_smooth _ τ.H` as an intermediate fact. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible τ.V`. Establish `hK` using `IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V)`. Establish `hs` using `IsPullback.of_hasPullback τ.H.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue τ.V)))`.

Use `DvrModel.isIntegral_of_geometricallyIntegral hK` as an intermediate fact. Use `DvrModel.isIntegral_of_geometricallyIntegral hs` as an intermediate fact. Use `DvrModel.isOpenImmersion_generic hK` as an intermediate fact. Use `DvrModel.isIntegral hK` as an intermediate fact. Establish `: IsCommMonObj ((Over.pullback (Out.jK τ.V)).obj τ.H)` using `Functor.isCommMonObj_obj`.

Take `⟨ρ, hρ⟩` from `gen_chartPull (chartPullLinComb T.L.L τ.φ (K := PUnit) (fun _ => eSec ((Over.pullback (Out.jK τ.V)).obj τ.H)) (fun _ => eSec C.A) (fun _ => 1) τ.yK fun _ => (cubeMapOf τ.φ_cart).e_comm) T.L.rig T.L.rigGen`. Take `⟨L, w₀, hw₀⟩` from `hE τ.V (FractionRing τ.V) τ.H (eSec ((Over.pullback (Out.jK τ.V)).obj τ.H)) (cubeMapOf (isGrpPullback_pullback τ.H (Out.jK τ.V))).e_comm (T.L.L.pull τ.φ) (pull_isLB T.L.isLB _) ρ hρ`. Take `⟨r, hr⟩` from `SecPullIso.exists_pull τ.φ T.L.L (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) w₀ T.L.isLB (pull_isLB L.isLB _) hw₀ T.θ`. Take `⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩` from `DvrModel.existsUnique_zpow_mul_sec hK hs hϖ L.isLB r (by`. Take `⟨x, k, hk⟩` from `exists_mem_basicOpen T τ (hC p y τ)`.

Take `⟨a, ha⟩` from `exists_chart (pull_isLB L.isLB (pullback.fst τ.H.hom (Out.jK τ.V))) x`. Establish `hk'` using `C.A.left.basicOpen_le _ hk`. Establish `u` using `(SecPullIso.isUnit_gs_iff τ.φ x hk' _).2 hk`. Rewrite `u` using `[hr x k a hk' ha]`. Establish `u'` using `(SecPullIso.isUnit_gs_iff (𝟙 _) x ha _).1 (isUnit_of_mul_isUnit_right u)`.

Conclude with `⟨a, fun h => by rw [h, Scheme.basicOpen_zero] at u'; exact u'⟩)`. Establish `h0 : algebraMap τ.V (FractionRing τ.V) ϖ ^ n ≠ 0` using `zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective τ.V _)).2 hϖ.ne_zero)`. Establish `hc` using `(h0.isUnit.map (Scheme.ΓSpecIso (.of (FractionRing τ.V))).inv.hom).map (pullback.snd τ.H.hom (Out.jK τ.V)).appTop.hom`. Use `⟨⟨L, invMul w₀ hc.unit, isGen_invMul hw₀ _, σ, fun x i k hi hk => ?_, x₀, Opens.mem_iSup.2 ⟨b, hb⟩, hx₀⟩⟩` and prove the remaining obligations. Establish `hi' : x ∈ (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))).U fun _ => i` using `mem_pull.2 hi`.

Establish `hk' : x ∈ (T.L.L.pull τ.φ).U fun _ => k` using `mem_pull.2 hk`. Establish `e₁` using `congrArg (gs (𝟙 _) x _) (hσ fun _ => i)`. Establish `e₂` using `(gs_appLE _ _ _ _ (𝟙 _) x hi' _).symm.trans (e₁.trans ((gs_mul (𝟙 _) x _ hi' _ _).trans (congrArg (· * _) ((gs_res (𝟙 _) x le_top hi' _).trans (gs_unit (𝟙 _) x ⊤ trivial hc.unit)))))`. Rewrite `e₂` using `[Category.id_comp]`. Use `e₂.trans (Eq.symm ?_)` and prove the remaining obligations.

Use `(congrArg₂ (· * ·) ((gs_unit (𝟙 _) x _ (show _ ∈ _ ⊓ _ from ⟨hi', hk'⟩) _).trans (congrArg Units.val (gm_invMul w₀ hc.unit x _ _ hi' hk'))) (hr x k _ hk hi')).trans ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, _root_.mul_assoc]`. Conclude with `congrArg (_ * ·) (Units.inv_mul_cancel_left _ _)`.
-/
theorem Core.Theta.nonempty_ext : Semi.extend_existsSt.{0} → ∀ (C : Core) (T : C.Theta) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.TestCart → Nonempty (T.Ext τ) := by
  intro hE C T p _ y τ hC
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ τ.H
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible τ.V
  have hK := IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V)
  have hs := IsPullback.of_hasPullback τ.H.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue τ.V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := DvrModel.isOpenImmersion_generic hK
  have := DvrModel.isIntegral hK
  have : IsCommMonObj ((Over.pullback (Out.jK τ.V)).obj τ.H) := Functor.isCommMonObj_obj
  obtain ⟨ρ, hρ⟩ := gen_chartPull (chartPullLinComb T.L.L τ.φ (K := PUnit)
    (fun _ => eSec ((Over.pullback (Out.jK τ.V)).obj τ.H)) (fun _ => eSec C.A) (fun _ => 1) τ.yK
    fun _ => (cubeMapOf τ.φ_cart).e_comm) T.L.rig T.L.rigGen
  obtain ⟨L, w₀, hw₀⟩ := hE τ.V (FractionRing τ.V) τ.H (eSec ((Over.pullback (Out.jK τ.V)).obj τ.H))
    (cubeMapOf (isGrpPullback_pullback τ.H (Out.jK τ.V))).e_comm (T.L.L.pull τ.φ) (pull_isLB T.L.isLB _) ρ hρ
  obtain ⟨r, hr⟩ := SecPullIso.exists_pull τ.φ T.L.L (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) w₀ T.L.isLB
    (pull_isLB L.isLB _) hw₀ T.θ
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ L.isLB r (by
    obtain ⟨x, k, hk⟩ := exists_mem_basicOpen T τ (hC p y τ)
    obtain ⟨a, ha⟩ := exists_chart (pull_isLB L.isLB (pullback.fst τ.H.hom (Out.jK τ.V))) x
    have hk' := C.A.left.basicOpen_le _ hk
    have u := (SecPullIso.isUnit_gs_iff τ.φ x hk' _).2 hk
    rw [hr x k a hk' ha] at u
    have u' := (SecPullIso.isUnit_gs_iff (𝟙 _) x ha _).1 (isUnit_of_mul_isUnit_right u)
    exact ⟨a, fun h => by rw [h, Scheme.basicOpen_zero] at u'; exact u'⟩)
  have h0 : algebraMap τ.V (FractionRing τ.V) ϖ ^ n ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective τ.V _)).2 hϖ.ne_zero)
  have hc := (h0.isUnit.map (Scheme.ΓSpecIso (.of (FractionRing τ.V))).inv.hom).map
    (pullback.snd τ.H.hom (Out.jK τ.V)).appTop.hom
  refine ⟨⟨L, invMul w₀ hc.unit, isGen_invMul hw₀ _, σ, fun x i k hi hk => ?_, x₀, Opens.mem_iSup.2 ⟨b, hb⟩, hx₀⟩⟩
  have hi' : x ∈ (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))).U fun _ => i := mem_pull.2 hi
  have hk' : x ∈ (T.L.L.pull τ.φ).U fun _ => k := mem_pull.2 hk
  have e₁ := congrArg (gs (𝟙 _) x _) (hσ fun _ => i)
  have e₂ := (gs_appLE _ _ _ _ (𝟙 _) x hi' _).symm.trans (e₁.trans ((gs_mul (𝟙 _) x _ hi' _ _).trans
    (congrArg (· * _) ((gs_res (𝟙 _) x le_top hi' _).trans (gs_unit (𝟙 _) x ⊤ trivial hc.unit)))))
  rw [Category.id_comp] at e₂
  refine e₂.trans (Eq.symm ?_)
  refine (congrArg₂ (· * ·) ((gs_unit (𝟙 _) x _ (show _ ∈ _ ⊓ _ from ⟨hi', hk'⟩) _).trans
    (congrArg Units.val (gm_invMul w₀ hc.unit x _ _ hi' hk'))) (hr x k _ hk hi')).trans ?_
  rw [Units.val_mul, _root_.mul_assoc]
  exact congrArg (_ * ·) (Units.inv_mul_cancel_left _ _)

end GlobalTheory.ZJ
