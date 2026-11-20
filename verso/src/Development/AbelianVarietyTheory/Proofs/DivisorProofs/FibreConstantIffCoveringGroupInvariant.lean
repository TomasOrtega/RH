import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverFibreTorsorTrivialLevelChanges
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevOfLiftsOfEqOne
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

open CategoryTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevInv

/- English proof (translation)
Take `⟨p, φ, w, hw⟩` from `GlobalTheory.TransferCompare.allTest_framed Xo c k y`. Establish `hact : actLev c lev γ g ∈ sec Xo c a n` using `Formalism.L2.Pj.actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ hg`. Rewrite using `[GlobalTheory.FlatLine.evR_of_frMap_test hact.1 hw]`. Establish `hm` using `Formalism.L2.Pj.mvPt_spec hL.total γ w`. Establish `hw'` using `hL.nat γ p.R k φ w _ y y' hw hm h`.

Rewrite using `[GlobalTheory.FlatLine.evR_of_frMap_test hg.1 hw']`. Both sides reduce to the same expression.
-/
theorem evR_actLev {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {G : Type} [Group G]
    {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (hL : ActLev (Xo := Xo) c lev) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c} (hg : g ∈ sec Xo c a n)
    (γ : G) {k : Type} [Field k] [IsAlgClosed k] [Algebra c.F k] (y y' : FrPt Xo c k)
    (h : levR (Xo := Xo) (c := c) (lev γ) y y') :
    evR Xo c (actLev c lev γ g) y = evR Xo c g y' := by
  obtain ⟨p, φ, w, hw⟩ := GlobalTheory.TransferCompare.allTest_framed Xo c k y
  have hact : actLev c lev γ g ∈ sec Xo c a n :=
    Formalism.L2.Pj.actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ hg
  rw [GlobalTheory.FlatLine.evR_of_frMap_test hact.1 hw]
  have hm := Formalism.L2.Pj.mvPt_spec hL.total γ w
  have hw' := hL.nat γ p.R k φ w _ y y' hw hm h
  rw [GlobalTheory.FlatLine.evR_of_frMap_test hg.1 hw']
  rfl

/- English proof (translation)
Introduce `D j H Dw l Xo c d hpq hlev hA hB lift hlift a n g hg`. Take `⟨hd, -, -, -, -, -, -, -, -⟩` from `id hlev`. Establish `hOB : GlobalTheory.ClsVal.Cmp.OverBase d`. Break down `hB with ⟨hne, hA'⟩ | h` into its components or cases. Conclude with `GlobalTheory.ClsVal.Cmp.overBase_of_ne hne hA' d`.

Conclude with `h`. Establish `hO : GlobalTheory.CoverSec.AllOver d` using `GlobalTheory.CoverSec.allOver_of_overBase d hd.2.2 hOB`. Establish `hq : ∀ (γ : Gam Dw d.l₂) (x : Dw.La), (Submodule.Quotient.mk (lift γ x) : LaQ Dw d.l₂) = γ (Submodule.Quotient.mk x)` using `fun γ x => by`. Establish `e` using `congrArg (fun f => f x) (hlift γ)`. Simplify using `using e`.

Establish `h1 : ∀ x, lift 1 x - x ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)` using `fun x => (Submodule.Quotient.eq _).1 ((hq 1 x).trans rfl)`. Establish `hm : ∀ γ δ x, lift (γ * δ) x - lift γ (lift δ x) ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)` using `fun γ δ x => (Submodule.Quotient.eq _).1 (by rw [hq, hq, LinearEquiv.mul_apply, ← hq])`. Establish `hL` using `GlobalTheory.LevelActionOfLifts.actLev_of_lifts_of_eq_one D H Dw d.l₂ d.Xo₂ d.c₂ (Gam Dw d.l₂) lift hpq hA h1 hm`. Establish `hact : ∀ γ, actLev d.c₂ (fun γ => (lift γ, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) γ g ∈ sec d.Xo₂ d.c₂ a n` using `fun γ => Formalism.L2.Pj.actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ hg`. Prove the components needed by the constructor for the conclusion.

Introduce `hF γ hγ`. Use `GlobalTheory.CoverSec.eq_of_geometric (hact γ).1 hg.1 fun k _ _ _ y₂ => ?_` and prove the remaining obligations. Use `letI := GlobalTheory.CoverSec.algBelow d k`. Establish `hk : ∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t` using `fun _ => rfl`. Take `⟨y₂', hy₂'⟩` from `hL.total γ k y₂`.

Take `⟨y, hy⟩` from `GlobalTheory.CoverSec.exists_frOver_below d hk y₂ (hO k hk y₂)`. Establish `ho` using `(GlobalTheory.LevOrbit.fibre_torsor D.host.E H Dw l Xo c d hpq hlev hA hOB lift hlift k hk y₂ y₂' y hy).1.2 ⟨γ, hγ, hy₂'⟩`. Rewrite using `[evR_actLev hL hg γ y₂ y₂' hy₂']`. Conclude with `(hF k hk y₂ y₂' y hy ho).symm`. Introduce `hI k _ _ _ _ hk y₂ y₂' y hy hy'`.

Take `⟨γ, hγ, hr⟩` from `(GlobalTheory.LevOrbit.fibre_torsor D.host.E H Dw l Xo c d hpq hlev hA hOB lift hlift k hk y₂ y₂' y hy).1.1 hy'`. Rewrite using `[← evR_actLev hL hg γ y₂ y₂' hr, hI γ hγ]`.
-/
theorem fibConst_iff_invariant : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → ((Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d) → ∀ (lift : Gam Dw d.l₂ → Dw.La →ₗ[𝓞 D.host.E] Dw.La), IsLift lift → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec d.Xo₂ d.c₂ a n, (FibConst d g ↔ ∀ γ, CongMod l.Mb (lift γ) LinearMap.id → actLev d.c₂ (fun γ => (lift γ, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) γ g = g) := by
  intro D j H Dw l Xo c d hpq hlev hA hB lift hlift a n g hg
  obtain ⟨hd, -, -, -, -, -, -, -, -⟩ := id hlev
  have hOB : GlobalTheory.ClsVal.Cmp.OverBase d := by
    rcases hB with ⟨hne, hA'⟩ | h
    · exact GlobalTheory.ClsVal.Cmp.overBase_of_ne hne hA' d
    · exact h
  have hO : GlobalTheory.CoverSec.AllOver d := GlobalTheory.CoverSec.allOver_of_overBase d hd.2.2 hOB
  have hq : ∀ (γ : Gam Dw d.l₂) (x : Dw.La),
      (Submodule.Quotient.mk (lift γ x) : LaQ Dw d.l₂) = γ (Submodule.Quotient.mk x) := fun γ x => by
    have e := congrArg (fun f => f x) (hlift γ)
    simpa using e
  have h1 : ∀ x, lift 1 x - x ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := fun x =>
    (Submodule.Quotient.eq _).1 ((hq 1 x).trans rfl)
  have hm : ∀ γ δ x, lift (γ * δ) x - lift γ (lift δ x) ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
    fun γ δ x => (Submodule.Quotient.eq _).1 (by rw [hq, hq, LinearEquiv.mul_apply, ← hq])
  have hL := GlobalTheory.LevelActionOfLifts.actLev_of_lifts_of_eq_one D H Dw d.l₂ d.Xo₂ d.c₂ (Gam Dw d.l₂) lift hpq hA h1 hm
  have hact : ∀ γ, actLev d.c₂ (fun γ => (lift γ, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) γ g ∈
      sec d.Xo₂ d.c₂ a n := fun γ => Formalism.L2.Pj.actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ hg
  constructor
  · intro hF γ hγ
    refine GlobalTheory.CoverSec.eq_of_geometric (hact γ).1 hg.1 fun k _ _ _ y₂ => ?_
    letI := GlobalTheory.CoverSec.algBelow d k
    have hk : ∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t := fun _ => rfl
    obtain ⟨y₂', hy₂'⟩ := hL.total γ k y₂
    obtain ⟨y, hy⟩ := GlobalTheory.CoverSec.exists_frOver_below d hk y₂ (hO k hk y₂)
    have ho := (GlobalTheory.LevOrbit.fibre_torsor D.host.E H Dw l Xo c d hpq hlev hA hOB lift hlift k hk y₂ y₂' y hy).1.2
      ⟨γ, hγ, hy₂'⟩
    rw [evR_actLev hL hg γ y₂ y₂' hy₂']
    exact (hF k hk y₂ y₂' y hy ho).symm
  · intro hI k _ _ _ _ hk y₂ y₂' y hy hy'
    obtain ⟨γ, hγ, hr⟩ :=
      (GlobalTheory.LevOrbit.fibre_torsor D.host.E H Dw l Xo c d hpq hlev hA hOB lift hlift k hk y₂ y₂' y hy).1.1 hy'
    rw [← evR_actLev hL hg γ y₂ y₂' hr, hI γ hγ]

end GlobalTheory.LevInv
