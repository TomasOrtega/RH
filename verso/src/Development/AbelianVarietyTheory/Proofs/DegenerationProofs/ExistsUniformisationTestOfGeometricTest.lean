import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionTestSpecialFibreOpenPartStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestModelMapsIntoOpenPartStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftIntegralPointClosureTestModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadicStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

/- English proof (translation)
Introduce `hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex p _ y y₀ t c tm hbig`. Establish `hin` using `GlobalTheory.T.testModel_maps_into_openPart hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig`. Establish `hrange : Set.range (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⊆ Set.range Q.G.ι`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `hin (Set.mem_univ x)`. Set `f' : t.u.G.left ⟶ Q.G.toScheme` to `IsOpenImmersion.lift Q.G.ι _ hrange`. Establish `hf' : f' ≫ Q.G.ι = tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι` using `IsOpenImmersion.lift_fac _ _ _`. Take `⟨-, hloc, hinj, -⟩` from `GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ t.u`. Take `⟨-, -, hsm, -, hsplit⟩` from `GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ t.u`.

Establish `hgen` using `t.u.U.gen_hom`. Establish `g1 : IsGrpPullback ((Over.pullback (jK t.u.V)).obj t.u.G) ρ.P.A (c.yK ≫ Q.u₀) (tm.φ ≫ pullback.fst ρ.P.A.hom Q.u₀)` using `((isGrpPullback_of_iso t.u.U.gen).comp t.u.cart).congr ((Category.id_comp _).trans c.yK_u.symm) tm.φ_fst.symm`. Establish `g2 : IsGrpPullback ((Over.pullback (jK t.u.V)).obj t.u.G) ((Over.pullback Q.u₀).obj ρ.P.A) c.yK tm.φ` using `(isGrpPullback_pullback ρ.P.A Q.u₀).cancel g1 tm.φ_snd`. Set `τ : ex.core.Test y` to `{ V := t.u.V complete := t.u.complete j := t.u.j j_inj := hinj j_loc := hloc y₀ := c.yV fac := c.fac H := t.u.G smooth := hsm sep := t.u.U.separated qc := t.u.semi.quasiCompact split := hsplit f := f' f_over := by`. Express the relevant statement in the definitionally equal form `f' ≫ Q.G.ι ≫ Q.P.hom = _`.

Rewrite using `[← Category.assoc, hf', Category.assoc]`. Conclude with `tm.f_over`. Use `yK := c.yK`. Use `yK_fac := c.yK_fac`. Use `φ := tm.φ`.

Use `φ_cart := g2`. Use `φ_f := by`. Express the relevant statement in the definitionally equal form `tm.φ ≫ ex.a = pullback.fst t.u.G.hom (jK t.u.V) ≫ f'`. Rewrite using `[← cancel_mono Q.G.ι, Category.assoc, ex.a_eq, Category.assoc, hf']`. Conclude with `tm.φ_f`.

Use `imm := GlobalTheory.T.isClosedImmersion_testSpecialFibre_openPart hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig f' hf'`. Use `lift := by`. Introduce `b hb`. Express the relevant statement in the definitionally equal form `Sp (OO p) ⟶ Q.G.toScheme at b`. Take `⟨c', h1, h2⟩` from `GlobalTheory.T.exists_lift_integralPoint_closure_testModel hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig (b ≫ Q.G.ι) ((Category.assoc _ _ _).trans hb) (by`.

Introduce `x _`. Express the relevant statement in the definitionally equal form `(b ≫ Q.G.ι) x ∈ Q.G`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `(b x).2)`. Use `⟨c', h1, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `c' ≫ f' = b`. Rewrite using `[← cancel_mono Q.G.ι, Category.assoc, hf']`. Conclude with `h2 }`. Establish `hc : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j)` using `t.mod.cart.1`. Use `⟨τ, hc.isoPullback.symm, hc.isoPullback_inv_snd, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `hc.isoPullback.inv ≫ _ = pullback.fst t.u.G.hom (rPt p ≫ spMap t.u.j) ≫ f' ≫ Q.G.ι`. Rewrite using `[hf', ← Category.assoc, hc.isoPullback_inv_fst]`.
-/
theorem Clos.exists_core_test_of_geoTest : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∃ (τ : ex.core.Test y) (e : pullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j) ≅ t.mod.Φ.G.left), e.hom ≫ t.mod.Φ.G.hom = pullback.snd _ _ ∧ e.hom ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex p _ y y₀ t c tm hbig
  have hin := GlobalTheory.T.testModel_maps_into_openPart hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig
  have hrange : Set.range (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⊆ Set.range Q.G.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hin (Set.mem_univ x)
  let f' : t.u.G.left ⟶ Q.G.toScheme := IsOpenImmersion.lift Q.G.ι _ hrange
  have hf' : f' ≫ Q.G.ι = tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨-, hloc, hinj, -⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ t.u
  obtain ⟨-, -, hsm, -, hsplit⟩ := GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ t.u
  have hgen := t.u.U.gen_hom
  have g1 : IsGrpPullback ((Over.pullback (jK t.u.V)).obj t.u.G) ρ.P.A (c.yK ≫ Q.u₀)
      (tm.φ ≫ pullback.fst ρ.P.A.hom Q.u₀) :=
    ((isGrpPullback_of_iso t.u.U.gen).comp t.u.cart).congr
      ((Category.id_comp _).trans c.yK_u.symm) tm.φ_fst.symm
  have g2 : IsGrpPullback ((Over.pullback (jK t.u.V)).obj t.u.G) ((Over.pullback Q.u₀).obj ρ.P.A) c.yK tm.φ :=
    (isGrpPullback_pullback ρ.P.A Q.u₀).cancel g1 tm.φ_snd
  let τ : ex.core.Test y :=
    { V := t.u.V
      complete := t.u.complete
      j := t.u.j
      j_inj := hinj
      j_loc := hloc
      y₀ := c.yV
      fac := c.fac
      H := t.u.G
      smooth := hsm
      sep := t.u.U.separated
      qc := t.u.semi.quasiCompact
      split := hsplit
      f := f'
      f_over := by
        change f' ≫ Q.G.ι ≫ Q.P.hom = _
        rw [← Category.assoc, hf', Category.assoc]
        exact tm.f_over
      yK := c.yK
      yK_fac := c.yK_fac
      φ := tm.φ
      φ_cart := g2
      φ_f := by
        change tm.φ ≫ ex.a = pullback.fst t.u.G.hom (jK t.u.V) ≫ f'
        rw [← cancel_mono Q.G.ι, Category.assoc, ex.a_eq, Category.assoc, hf']
        exact tm.φ_f
      imm := GlobalTheory.T.isClosedImmersion_testSpecialFibre_openPart hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig f' hf'
      lift := by
        intro b hb
        change Sp (OO p) ⟶ Q.G.toScheme at b
        obtain ⟨c', h1, h2⟩ := GlobalTheory.T.exists_lift_integralPoint_closure_testModel hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig (b ≫ Q.G.ι)
          ((Category.assoc _ _ _).trans hb) (by
            intro x _
            change (b ≫ Q.G.ι) x ∈ Q.G
            rw [Scheme.Hom.comp_apply]
            exact (b x).2)
        refine ⟨c', h1, ?_⟩
        change c' ≫ f' = b
        rw [← cancel_mono Q.G.ι, Category.assoc, hf']
        exact h2 }
  have hc : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  refine ⟨τ, hc.isoPullback.symm, hc.isoPullback_inv_snd, ?_⟩
  change hc.isoPullback.inv ≫ _ = pullback.fst t.u.G.hom (rPt p ≫ spMap t.u.j) ≫ f' ≫ Q.G.ι
  rw [hf', ← Category.assoc, hc.isoPullback_inv_fst]

end GlobalTheory.ZH
