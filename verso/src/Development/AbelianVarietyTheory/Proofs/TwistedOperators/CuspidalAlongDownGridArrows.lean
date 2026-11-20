import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardArrowLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardTestGridEqSenderGridStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspTypedTestGridIffSenderGridConjStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridMeasureDomainDownwardEqSenderStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

/- English proof (translation)
Take `⟨L, h1, h2, e⟩` from `(hM.1.vert i j hi hj).sp`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem ga_eq_of_match {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} {W : G'.Weil} {G : GlobalTheory.Grid.GridPre R} (hM : GlobalTheory.GridJoin.Match G W) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : GA D (G.V i j).V = GA D (G'.V (.grid i j)) := by
  obtain ⟨L, h1, h2, e⟩ := (hM.1.vert i j hi hj).sp
  rw [e]; rfl

/- English proof (translation)
Introduce `hS hP`. Use `⟨0, fun ε CF _ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Introduce `D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc t M hMt a ha hdown e he φ f hf Q Fn hFn`. Take `⟨i, j, rfl⟩` from `hdown`. Establish `hgap : ch.sc.cGap = 1` using `by rw [hsc]`.

Choose the witnesses or unpack the hypotheses as in `⟨hi, hj⟩ : i ≤ D.R.m ∧ j < D.R.m := by`. Break down `ha with ⟨_, _, _, _, h⟩ | ⟨i', j', h1, h2, h⟩` into its components or cases. Consider the cases of `h`. Consider the cases of `h`. Conclude with `⟨h1, h2⟩`.

Take `⟨G, hG, hMa⟩` from `GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover hP.harishChandraModules hset.host hset.size hset.core hgap ch.W hch.weil`. Establish `hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R` using `⟨hset.core.lev, hset.core.models.inf, hset.core.models.νY, hset.core.models.νY', hset.core.models.νX⟩`. Establish `hCS` using `hS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hset.size) Γ Pl0 T A Ks R G hRB hG`. Establish `eA` using `ga_eq_of_match hMa hi (Nat.succ_le_of_lt hj)`. Establish `eB` using `ga_eq_of_match hMa hi hj.le`.

Establish `hΨ` using `GlobalTheory.T.isThetaFunction_fock_vector_downward_arrow ch.rm t i j hi hj he hf Q`. Take `⟨Φ, hΦ, hK⟩` from `GlobalTheory.T.thetaKernel_downward_testGrid_eq_sender_grid ch.W hch.weil G hG hMa t i j hi hj eA eB _ hΨ`. Establish `hF'` using `(GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i (j + 1) hi (Nat.succ_le_of_lt hj) eA Fn).1 hFn`. Take `⟨hint, hcusp⟩` from `hCS.th t i j hi hj Φ hΦ _ hF'`. Establish `hθ : ch.W.θ = R.θ` using `hch.weil.θ`.

Establish `hinv : ∀ h, ∀ γ ∈ GQ (ch.G.V (.grid i (j + 1))), ∀ g, (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (γ * g) = (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) g` using `fun h γ hγ g => by`. Simplify using `only [GlobalTheory.T.thetaKernel_downward_arrow_left_invariant ch.W t i j hi hj _ hΨ h γ hγ g, hFn.1.toIsAutFun.left γ hγ g]`. Establish `key` using `fun h => GlobalTheory.T.testGrid_measure_domain_downward_eq_sender hset hgap ch.W hch.weil G hG hMa M t hMt i j hi hj eA (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (hinv h)`. Establish `hcb : ∀ h : GA D (ch.G.V (.grid i j)), cast eB (cast eB.symm h) = h` using `fun h => cast_cast _ _ h`. Use `⟨fun h => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hcb h]`. Use `(key _).1.1 ?_` and prove the remaining obligations. Simplify `hint (cast eB.symm h)` using `only [hK]`. Use `(GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i j hi hj.le eB _).2 ?_` and prove the remaining obligations. Use `hcusp using 2 with h` and compare the differences between its conclusion and the goal.

Rewrite using `[liftA_apply, ← (key _).2]`. Simplify using `only [hK]`.
-/
theorem cuspStep_down_big : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.down t i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  intro hS hP
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc t M hMt a ha hdown e he φ f hf Q Fn hFn
  obtain ⟨i, j, rfl⟩ := hdown
  have hgap : ch.sc.cGap = 1 := by rw [hsc]
  obtain ⟨hi, hj⟩ : i ≤ D.R.m ∧ j < D.R.m := by
    rcases ha with ⟨_, _, _, _, h⟩ | ⟨i', j', h1, h2, h⟩
    · cases h
    · cases h; exact ⟨h1, h2⟩
  obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
    hP.harishChandraModules hset.host hset.size hset.core hgap ch.W hch.weil
  have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
    ⟨hset.core.lev, hset.core.models.inf, hset.core.models.νY, hset.core.models.νY', hset.core.models.νX⟩
  have hCS := hS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hset.size) Γ Pl0 T A Ks R G hRB hG
  have eA := ga_eq_of_match hMa hi (Nat.succ_le_of_lt hj)
  have eB := ga_eq_of_match hMa hi hj.le
  have hΨ := GlobalTheory.T.isThetaFunction_fock_vector_downward_arrow ch.rm t i j hi hj he hf Q
  obtain ⟨Φ, hΦ, hK⟩ := GlobalTheory.T.thetaKernel_downward_testGrid_eq_sender_grid ch.W hch.weil G hG hMa t i j hi hj eA eB _ hΨ
  have hF' := (GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i (j + 1) hi (Nat.succ_le_of_lt hj) eA Fn).1 hFn
  obtain ⟨hint, hcusp⟩ := hCS.th t i j hi hj Φ hΦ _ hF'
  have hθ : ch.W.θ = R.θ := hch.weil.θ
  have hinv : ∀ h, ∀ γ ∈ GQ (ch.G.V (.grid i (j + 1))), ∀ g,
      (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (γ * g) =
      (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) g := fun h γ hγ g => by
    simp only [GlobalTheory.T.thetaKernel_downward_arrow_left_invariant ch.W t i j hi hj _ hΨ h γ hγ g, hFn.1.toIsAutFun.left γ hγ g]
  have key := fun h => GlobalTheory.T.testGrid_measure_domain_downward_eq_sender hset hgap ch.W hch.weil G hG hMa M t hMt i j hi hj eA
    (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (hinv h)
  have hcb : ∀ h : GA D (ch.G.V (.grid i j)), cast eB (cast eB.symm h) = h := fun h => cast_cast _ _ h
  refine ⟨fun h => ?_, ?_⟩
  · rw [← hcb h]
    refine (key _).1.1 ?_
    simpa only [hK] using hint (cast eB.symm h)
  · refine (GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i j hi hj.le eB _).2 ?_
    convert hcusp using 2 with h
    rw [liftA_apply, ← (key _).2]
    simp only [hK]

end GlobalTheory.FlipRun
