import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoIsMonHomOfIsGtOfRangeEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTestOfGeometricTestStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory

/- English proof (translation)
Establish `w : (pullback.fst τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ≫ τ.f) ≫ C.GG.hom = pullback.snd τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ≫ ZJ.rPt p ≫ y`. Rewrite using `[Category.assoc, τ.f_over, pullback.condition_assoc, Category.assoc, τ.fac]`. Set `h` to `pullback.lift _ _ w`. Establish `h₁ : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f` using `pullback.lift_fst _ _ _`. Establish `h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _` using `pullback.lift_snd _ _ _`.

Establish `hc` using `τ.imm h h₁ h₂`. Use `⟨h, h₁, h₂, hc, ?_⟩` and prove the remaining obligations. Use `(ZJ.kb_isAlgClosed_and_conj p).1` as an intermediate fact. Use `(ZJ.core_basic C).2.1` as an intermediate fact. Set `s` to `pullback.snd C.GG.hom (ZJ.rPt p ≫ y)`.

Establish `: JacobsonSpace ↥(pullback C.GG.hom (ZJ.rPt p ≫ y))` using `LocallyOfFiniteType.jacobsonSpace s`. Rewrite using `[← Set.univ_subset_iff, ← closure_closedPoints, h.isClosedEmbedding.isClosed_range.closure_subset_iff]`. Introduce `x hx`. Take `⟨z, hz, hzx⟩ : ∃ z : Sp (ZJ.kb p) ⟶ pullback C.GG.hom (ZJ.rPt p ≫ y), z ≫ pullback.snd _ _ = 𝟙 _ ∧ ∀ q, z q = x` from `⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx, pointOfClosedPoint_apply s x hx⟩`. Take `⟨c, hc₁, hc₂⟩` from `hF p y τ (z ≫ pullback.fst _ _) (by`.

Rewrite using `[Category.assoc, pullback.condition, reassoc_of% hz])`. Establish `e : pullback.lift c (𝟙 _) (hc₁.trans (Category.id_comp _).symm) ≫ h = z`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, h₁, pullback.lift_fst_assoc, hc₂]`. Rewrite using `[Category.assoc, h₂, pullback.lift_snd, hz]`.

Conclude with `⟨pullback.lift c (𝟙 _) (hc₁.trans (Category.id_comp _).symm) (IsLocalRing.closedPoint (ZJ.kb p)), (congrArg (fun g => g (IsLocalRing.closedPoint (ZJ.kb p))) e).trans (hzx _)⟩`.
-/
theorem ZJ.Core.Test.exists_fibre_immersion {C : ZJ.Core} (hF : C.Fib) {p : ℕ} [Fact p.Prime]
    {y : Sp (ZJ.OO p) ⟶ C.Z} (τ : C.Test y) :
    ∃ h : pullback τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom (ZJ.rPt p ≫ y),
      h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f ∧ h ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      IsClosedImmersion h ∧ Set.range h = Set.univ := by
  have w : (pullback.fst τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ≫ τ.f) ≫ C.GG.hom =
      pullback.snd τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ≫ ZJ.rPt p ≫ y := by
    rw [Category.assoc, τ.f_over, pullback.condition_assoc, Category.assoc, τ.fac]
  let h := pullback.lift _ _ w
  have h₁ : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hc := τ.imm h h₁ h₂
  refine ⟨h, h₁, h₂, hc, ?_⟩
  have := (ZJ.kb_isAlgClosed_and_conj p).1
  have := (ZJ.core_basic C).2.1
  let s := pullback.snd C.GG.hom (ZJ.rPt p ≫ y)
  have : JacobsonSpace ↥(pullback C.GG.hom (ZJ.rPt p ≫ y)) := LocallyOfFiniteType.jacobsonSpace s
  rw [← Set.univ_subset_iff, ← closure_closedPoints, h.isClosedEmbedding.isClosed_range.closure_subset_iff]
  intro x hx
  obtain ⟨z, hz, hzx⟩ : ∃ z : Sp (ZJ.kb p) ⟶ pullback C.GG.hom (ZJ.rPt p ≫ y),
      z ≫ pullback.snd _ _ = 𝟙 _ ∧ ∀ q, z q = x :=
    ⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx, pointOfClosedPoint_apply s x hx⟩
  obtain ⟨c, hc₁, hc₂⟩ := hF p y τ (z ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, reassoc_of% hz])
  have e : pullback.lift c (𝟙 _) (hc₁.trans (Category.id_comp _).symm) ≫ h = z := by
    apply pullback.hom_ext
    · rw [Category.assoc, h₁, pullback.lift_fst_assoc, hc₂]
    · rw [Category.assoc, h₂, pullback.lift_snd, hz]
  exact ⟨pullback.lift c (𝟙 _) (hc₁.trans (Category.id_comp _).symm) (IsLocalRing.closedPoint (ZJ.kb p)),
    (congrArg (fun g => g (IsLocalRing.closedPoint (ZJ.kb p))) e).trans (hzx _)⟩

/- English proof (translation)
Use `τ.j_loc` as an intermediate fact. Establish `hr : Set.range (ZJ.rPt p ≫ spMap τ.j) = {IsLocalRing.closedPoint τ.V}`. Establish `h : ∀ q, (ZJ.rPt p ≫ spMap τ.j) q = IsLocalRing.closedPoint τ.V` using `fun q => by`. Rewrite using `[Subsingleton.elim q (IsLocalRing.closedPoint (ZJ.kb p))]`. Conclude with `(congrArg (PrimeSpectrum.comap τ.j) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (ZJ.OO p)))).trans (IsLocalRing.comap_closedPoint τ.j)`.

Conclude with `Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint (ZJ.kb p), h _⟩, by`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `h q⟩`. Take `⟨G₁, _, _, E, φ, hE, hφ⟩` from `τ.exists_isGt_fibre _ _ hr`. Take `⟨e, he, -⟩` from `grpPullback_iso hφ (isGrpPullback_pullback τ.H _)`.

Conclude with `⟨E, isGt_of_iso e hE⟩`.
-/
theorem ZJ.Core.Test.exists_isGt_special {C : ZJ.Core} {p : ℕ} [Fact p.Prime]
    {y : Sp (ZJ.OO p) ⟶ C.Z} (τ : C.Test y) :
    ∃ E : SplitExt (Sp (ZJ.kb p)), E.IsGt ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) := by
  have := τ.j_loc
  have hr : Set.range (ZJ.rPt p ≫ spMap τ.j) = {IsLocalRing.closedPoint τ.V} := by
    have h : ∀ q, (ZJ.rPt p ≫ spMap τ.j) q = IsLocalRing.closedPoint τ.V := fun q => by
      rw [Subsingleton.elim q (IsLocalRing.closedPoint (ZJ.kb p))]
      exact (congrArg (PrimeSpectrum.comap τ.j)
        (IsLocalRing.comap_closedPoint (IsLocalRing.residue (ZJ.OO p)))).trans (IsLocalRing.comap_closedPoint τ.j)
    exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint (ZJ.kb p), h _⟩, by
      rintro _ ⟨q, rfl⟩
      exact h q⟩
  obtain ⟨G₁, _, _, E, φ, hE, hφ⟩ := τ.exists_isGt_fibre _ _ hr
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback τ.H _)
  exact ⟨E, isGt_of_iso e hE⟩

/- English proof (translation)
Use `Q.proper` as an intermediate fact. Establish `: IsDominant (Out.jK t.u.V)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by`. Rewrite using `[CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective t.u.V _)]`. Conclude with `bot_le)⟩`. Take `⟨e₁, he₁, s₁⟩ : ∃ e₁ : Sp t.u.V ⟶ t.u.G.left, e₁ = eSec t.u.G ∧ e₁ ≫ t.u.G.hom = 𝟙 _` from `⟨_, rfl, Over.w η[t.u.G]⟩`.

Take `⟨e₂, he₂, s₂⟩ : ∃ e₂ : Sp (FractionRing t.u.V) ⟶ pullback t.u.G.hom (jK t.u.V), e₂ = eSec ((Over.pullback (jK t.u.V)).obj t.u.G) ∧ e₂ ≫ pullback.snd _ _ = 𝟙 _` from `⟨_, rfl, Over.w η[(Over.pullback (jK t.u.V)).obj t.u.G]⟩`. Take `⟨e₃, he₃, s₃⟩ : ∃ e₃ : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀, e₃ = eSec ((Over.pullback Q.u₀).obj ρ.P.A) ∧ e₃ ≫ pullback.snd _ _ = 𝟙 _` from `⟨_, rfl, Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]⟩`. Take `⟨e₄, he₄⟩ : ∃ e₄ : Sp S.R ⟶ ρ.P.A.left, e₄ = eSec ρ.P.A` from `⟨_, rfl⟩`. Establish `h₂ : e₂ ≫ pullback.fst _ _ = jK t.u.V ≫ e₁`. Substitute `he₁ he₂` using the available equality.

Conclude with `ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback t.u.G (jK t.u.V))`. Establish `h₃ : e₃ ≫ pullback.fst _ _ = Q.u₀ ≫ e₄`. Substitute `he₃ he₄` using the available equality. Conclude with `ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback ρ.P.A Q.u₀)`. Establish `h₄ : e₂ ≫ t.u.U.gen.hom.left ≫ t.u.φ = spMap t.u.yK ≫ e₄`.

Substitute `he₂ he₄` using the available equality. Use `t.u.U.gen_hom` as an intermediate fact. Conclude with `ZJ.eSec_comp_of_isGrpPullback (((isGrpPullback_of_iso t.u.U.gen).comp t.u.cart).congr (Category.id_comp _) rfl)`. Establish `h₅ : U₀.ι ≫ ex.e = e₃ ≫ ex.a` using `he₃ ▸ ex.e_zero`. Establish `h₆ : e₂ ≫ tm.φ = c.yK ≫ e₃`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, tm.φ_fst, h₃, reassoc_of% c.yK_u]`. Conclude with `h₄`. Rewrite using `[Category.assoc, Category.assoc, tm.φ_snd, s₃, reassoc_of% s₂, Category.comp_id]`. Rewrite using `[← he₁]`.

Use `ext_of_isDominant_of_isSeparated Q.P.hom ?_ (Out.jK t.u.V) ?_` and prove the remaining obligations. Simplify using `only [Category.assoc]`. Rewrite using `[tm.f_over, ex.e_sec, reassoc_of% s₁, Category.comp_id]`. Rewrite using `[← reassoc_of% c.yK_fac, reassoc_of% h₅, ex.a_eq, ← reassoc_of% h₆, tm.φ_f, reassoc_of% h₂]`.
-/
theorem ZH.Clos.TMap.eSec_comp_f {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} (ex : Q.Ext) {p : ℕ} [Fact p.Prime]
    {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c) :
    (eSec t.u.G ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι : Sp t.u.V ⟶ Q.P.left) = c.yV ≫ ex.e ≫ Q.G.ι := by
  have := Q.proper
  have : IsDominant (Out.jK t.u.V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective t.u.V _)]
    exact bot_le)⟩
  obtain ⟨e₁, he₁, s₁⟩ : ∃ e₁ : Sp t.u.V ⟶ t.u.G.left, e₁ = eSec t.u.G ∧ e₁ ≫ t.u.G.hom = 𝟙 _ :=
    ⟨_, rfl, Over.w η[t.u.G]⟩
  obtain ⟨e₂, he₂, s₂⟩ : ∃ e₂ : Sp (FractionRing t.u.V) ⟶ pullback t.u.G.hom (jK t.u.V),
      e₂ = eSec ((Over.pullback (jK t.u.V)).obj t.u.G) ∧ e₂ ≫ pullback.snd _ _ = 𝟙 _ :=
    ⟨_, rfl, Over.w η[(Over.pullback (jK t.u.V)).obj t.u.G]⟩
  obtain ⟨e₃, he₃, s₃⟩ : ∃ e₃ : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀,
      e₃ = eSec ((Over.pullback Q.u₀).obj ρ.P.A) ∧ e₃ ≫ pullback.snd _ _ = 𝟙 _ :=
    ⟨_, rfl, Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]⟩
  obtain ⟨e₄, he₄⟩ : ∃ e₄ : Sp S.R ⟶ ρ.P.A.left, e₄ = eSec ρ.P.A := ⟨_, rfl⟩
  have h₂ : e₂ ≫ pullback.fst _ _ = jK t.u.V ≫ e₁ := by
    subst he₁ he₂
    exact ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback t.u.G (jK t.u.V))
  have h₃ : e₃ ≫ pullback.fst _ _ = Q.u₀ ≫ e₄ := by
    subst he₃ he₄
    exact ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback ρ.P.A Q.u₀)
  have h₄ : e₂ ≫ t.u.U.gen.hom.left ≫ t.u.φ = spMap t.u.yK ≫ e₄ := by
    subst he₂ he₄
    have := t.u.U.gen_hom
    exact ZJ.eSec_comp_of_isGrpPullback
      (((isGrpPullback_of_iso t.u.U.gen).comp t.u.cart).congr (Category.id_comp _) rfl)
  have h₅ : U₀.ι ≫ ex.e = e₃ ≫ ex.a := he₃ ▸ ex.e_zero
  have h₆ : e₂ ≫ tm.φ = c.yK ≫ e₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, tm.φ_fst, h₃, reassoc_of% c.yK_u]
      exact h₄
    · rw [Category.assoc, Category.assoc, tm.φ_snd, s₃, reassoc_of% s₂, Category.comp_id]
  rw [← he₁]
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (Out.jK t.u.V) ?_
  · simp only [Category.assoc]
    rw [tm.f_over, ex.e_sec, reassoc_of% s₁, Category.comp_id]
  · rw [← reassoc_of% c.yK_fac, reassoc_of% h₅, ex.a_eq, ← reassoc_of% h₆, tm.φ_f, reassoc_of% h₂]

/- English proof (translation)
Introduce `hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex p _ y y₀ t c tm τ hS hF`. Take `⟨τ₀, e₀, he₁, he₂⟩` from `GlobalTheory.T.exists_uniformisationTest_of_geometricTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hS`. Take `⟨h, h₁, h₂, hc, hr⟩` from `τ.exists_fibre_immersion hF`. Take `⟨h₀, h₀₁, h₀₂, hc₀, hr₀⟩` from `τ₀.exists_fibre_immersion hF`. Take `⟨E, hE⟩` from `τ.exists_isGt_special`.

Use `(ZJ.kb_isAlgClosed_and_conj p).1` as an intermediate fact. Establish `: IsCommMonObj ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H)` using `Functor.isCommMonObj_obj`. Set `Y : Over (Sp (ZJ.kb p))` to `Over.mk (pullback.snd ex.core.GG.hom (ZJ.rPt p ≫ y))`. Set `f : (Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H ⟶ Y` to `Over.homMk h h₂`. Establish `w : (e₀.inv ≫ h₀) ≫ pullback.snd _ _ = t.mod.Φ.G.hom`.

Rewrite using `[Category.assoc, h₀₂, ← he₁, Iso.inv_hom_id_assoc]`. Set `f' : t.mod.Φ.G ⟶ Y` to `Over.homMk (e₀.inv ≫ h₀) w`. Establish `k : (e₀.inv ≫ h₀) ≫ pullback.fst _ _ ≫ Q.G.ι = t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι`. Rewrite using `[Category.assoc, Iso.inv_comp_eq, he₂]`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h₀₁).trans (Category.assoc _ _ _))`.

Establish `k' : h ≫ pullback.fst _ _ ≫ Q.G.ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι` using `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h₁).trans (Category.assoc _ _ _))`. Establish `hr' : Set.range (e₀.inv ≫ h₀) = Set.univ`. Rewrite `hr₀`, the goal using `[Set.range_eq_univ]`. Conclude with `hr₀.comp e₀.inv.surjective`. Establish `hone : η[(Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H] ≫ f = η[t.mod.Φ.G] ≫ f'`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Use `(cancel_mono Q.G.ι).1 ?_` and prove the remaining obligations. Establish `u₁` using `ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback τ.H (ZJ.rPt p ≫ spMap τ.j))`. Establish `u₂` using `ZJ.eSec_comp_of_isGrpPullback t.mod.cart`.

Establish `v₁ : eSec ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) ≫ pullback.fst _ _ ≫ τ.f ≫ Q.G.ι = (ZJ.rPt p ≫ y ≫ ex.e ≫ Q.G.ι : Sp (ZJ.kb p) ⟶ Q.P.left)`. Use `((Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ.f ≫ Q.G.ι) u₁)).trans ?_` and prove the remaining obligations. Establish `a` using `congrArg (fun g => ZJ.rPt p ≫ spMap τ.j ≫ g ≫ Q.G.ι) τ.eSec_comp_f`. Conclude with `a.trans (congrArg (fun g => ZJ.rPt p ≫ g ≫ ex.e ≫ Q.G.ι) τ.fac)`. Establish `v₂ : eSec t.mod.Φ.G ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = (ZJ.rPt p ≫ y ≫ ex.e ≫ Q.G.ι : Sp (ZJ.kb p) ⟶ Q.P.left)`.

Use `((Category.assoc _ _ _).symm.trans (congrArg (· ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) u₂)).trans ?_` and prove the remaining obligations. Establish `a` using `congrArg (fun g => ZJ.rPt p ≫ spMap t.u.j ≫ g) (tm.eSec_comp_f ex)`. Simplify using `only [Category.assoc] at a ⊢`. Rewrite `a` using `[reassoc_of% c.fac]`. Conclude with `a`.

Rewrite `v₁` using `[← k']`. Rewrite `v₂` using `[← k]`. Conclude with `v₁.trans v₂.symm`. Conclude with `(Over.w _).trans (Over.w _).symm`. Take `⟨e, he, hef⟩` from `exists_iso_isMonHom_of_isGt_of_range_eq (ZJ.kb p) Y E t.mod.Φ.E _ _ f f' hE ⟨t.mod.Φ.D⟩ hc (inferInstanceAs (IsClosedImmersion (e₀.inv ≫ h₀))) (hr.trans hr'.symm) hone`.

Use `⟨e, he, ?_⟩` and prove the remaining obligations. Establish `hl : e.hom.left ≫ e₀.inv ≫ h₀ = h` using `congrArg (fun g => g.left) hef`. Rewrite using `[← k, ← k', ← hl]`. Simplify using `only [Category.assoc]`.
-/
theorem ZH.exists_iso_special_fibre_of_test : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c) (τ : ex.core.Test y), S.Big → ex.core.Fib → ∃ e : (Over.pullback (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)).obj τ.H ≅ t.mod.Φ.G, IsMonHom e.hom ∧ e.hom.left ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex p _ y y₀ t c tm τ hS hF
  obtain ⟨τ₀, e₀, he₁, he₂⟩ := GlobalTheory.T.exists_uniformisationTest_of_geometricTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hS
  obtain ⟨h, h₁, h₂, hc, hr⟩ := τ.exists_fibre_immersion hF
  obtain ⟨h₀, h₀₁, h₀₂, hc₀, hr₀⟩ := τ₀.exists_fibre_immersion hF
  obtain ⟨E, hE⟩ := τ.exists_isGt_special
  have := (ZJ.kb_isAlgClosed_and_conj p).1
  have : IsCommMonObj ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) := Functor.isCommMonObj_obj
  let Y : Over (Sp (ZJ.kb p)) := Over.mk (pullback.snd ex.core.GG.hom (ZJ.rPt p ≫ y))
  let f : (Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H ⟶ Y := Over.homMk h h₂
  have w : (e₀.inv ≫ h₀) ≫ pullback.snd _ _ = t.mod.Φ.G.hom := by
    rw [Category.assoc, h₀₂, ← he₁, Iso.inv_hom_id_assoc]
  let f' : t.mod.Φ.G ⟶ Y := Over.homMk (e₀.inv ≫ h₀) w
  have k : (e₀.inv ≫ h₀) ≫ pullback.fst _ _ ≫ Q.G.ι = t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
    rw [Category.assoc, Iso.inv_comp_eq, he₂]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h₀₁).trans (Category.assoc _ _ _))
  have k' : h ≫ pullback.fst _ _ ≫ Q.G.ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h₁).trans (Category.assoc _ _ _))
  have hr' : Set.range (e₀.inv ≫ h₀) = Set.univ := by
    rw [Set.range_eq_univ] at hr₀ ⊢
    exact hr₀.comp e₀.inv.surjective
  have hone : η[(Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H] ≫ f = η[t.mod.Φ.G] ≫ f' := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · refine (cancel_mono Q.G.ι).1 ?_
      have u₁ := ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback τ.H (ZJ.rPt p ≫ spMap τ.j))
      have u₂ := ZJ.eSec_comp_of_isGrpPullback t.mod.cart
      have v₁ : eSec ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) ≫ pullback.fst _ _ ≫ τ.f ≫ Q.G.ι =
          (ZJ.rPt p ≫ y ≫ ex.e ≫ Q.G.ι : Sp (ZJ.kb p) ⟶ Q.P.left) := by
        refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ.f ≫ Q.G.ι) u₁)).trans ?_
        have a := congrArg (fun g => ZJ.rPt p ≫ spMap τ.j ≫ g ≫ Q.G.ι) τ.eSec_comp_f
        exact a.trans (congrArg (fun g => ZJ.rPt p ≫ g ≫ ex.e ≫ Q.G.ι) τ.fac)
      have v₂ : eSec t.mod.Φ.G ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι =
          (ZJ.rPt p ≫ y ≫ ex.e ≫ Q.G.ι : Sp (ZJ.kb p) ⟶ Q.P.left) := by
        refine ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) u₂)).trans ?_
        have a := congrArg (fun g => ZJ.rPt p ≫ spMap t.u.j ≫ g) (tm.eSec_comp_f ex)
        simp only [Category.assoc] at a ⊢
        rw [reassoc_of% c.fac] at a
        exact a
      rw [← k'] at v₁
      rw [← k] at v₂
      exact v₁.trans v₂.symm
    · exact (Over.w _).trans (Over.w _).symm
  obtain ⟨e, he, hef⟩ := exists_iso_isMonHom_of_isGt_of_range_eq (ZJ.kb p) Y E t.mod.Φ.E _ _ f f' hE ⟨t.mod.Φ.D⟩ hc
    (inferInstanceAs (IsClosedImmersion (e₀.inv ≫ h₀))) (hr.trans hr'.symm) hone
  refine ⟨e, he, ?_⟩
  have hl : e.hom.left ≫ e₀.inv ≫ h₀ = h := congrArg (fun g => g.left) hef
  rw [← k, ← k', ← hl]
  simp only [Category.assoc]

end GlobalTheory
