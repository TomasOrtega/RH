import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridCommonDataPropertiesHoldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityValuesContinuousBoundedHeckeConjStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeLawsThetaHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainPreStepsExistOfDepthCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLawsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridStageLatticesPropertiesProofStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainWeilDatumExtendsToStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate

namespace GlobalTheory.ChainLifts

/- English proof (translation)
Introduce `D hq hsz T L μ0 hL sc hgap G W Mv hM v r₀ M₀ hr₀`. Establish `hCom : (gridCom W).Is` using `GlobalTheory.T.testGridCommonData_properties_hold D hq hsz T L μ0 hL sc hgap G W Mv hM`. Establish `hStage` using `GlobalTheory.T.testGridStageLatticesProperties_proof D hq T L μ0 hL sc G W Mv hM`. Establish `hPre` using `GlobalTheory.T.core_chain_pre_steps_exist_of_depth_congruence hDF D hq hsz T L μ0 hL sc hgap G W Mv hM`. Establish `hCM'` using `hCM D hq T L μ0 hL sc G W Mv hM`.

Establish `hStep` using `GlobalTheory.T.evenRankThetaChain_weilDatum_extends_to_step hDS hHC hCR hCW D`. Establish `hConj` using `GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCR D`. Establish `hEx` using `GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D`. Establish `hRL` using `GlobalTheory.T.selfDualLattice_changeOfLattice_laws D`. Establish `rapid : ∀ i, i ≤ D.R.m → ∀ r, IsCoreLat G i r → ∀ M (y : (gridStage G v i r M).CC (gridCom W)) w, GlobalTheory.Grow.RapidDec (G.V (.core i)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w)`.

Introduce `i hi r hr M y w`. Establish `hs` using `(hStage i hi).2 r hr v M`. Establish `h1` using `(hConj (gridCom W) hCom i hi _ hs).1 y w`. Conclude with `((hRL.2.1 _ r W.θ _ M ∅).2.2.2.2 _).1 h1.2.2.2.2`. Establish `ext : ∀ k (F₀ : Fn G (.core 0)) (F : Fn G (.core (k + 1))) (f : Sch G (.coreDown k)), Dep W (.core k) f → GlobalTheory.Grow.RapidDec (G.V (.core (k + 1))) F → F₀ ∈ Below W v k (dn W v k f F) → F₀ ∈ Below W v (k + 1) F`.

Introduce and unpack `k F₀ F f hf hF ⟨Ψ, h1, h2, h3, h4⟩`. Use `⟨Function.update Ψ (k + 1) F, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Break down `eq_or_ne i (k + 1) with rfl | hne` into its components or cases. Rewrite using `[Function.update_self]`.

Conclude with `hF`. Rewrite using `[Function.update_of_ne hne]; exact h1 i (by omega)`. Introduce `i hi`. Break down `Nat.lt_or_ge i k with hik | hik` into its components or cases. Take `⟨f', hf', e⟩` from `h2 i hik`.

Use `⟨f', hf', ?_⟩` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (by omega), Function.update_of_ne (by omega)]`. Conclude with `e`. Take `rfl : i = k` from `by omega`. Use `⟨f, hf, ?_⟩` and prove the remaining obligations.

Rewrite using `[Function.update_of_ne (by omega), Function.update_self]`. Conclude with `h4`. Rewrite using `[Function.update_of_ne (by omega)]; exact h3`. Conclude with `Function.update_self _ _ _`. Establish `key : ∀ k, k ≤ D.R.m → ∃ r M, IsCoreLat G k r ∧ ∃ Θ, GlobalTheory.EvenOnto.Reach (gridCom W) (gridStage G v 0 r₀ M₀) k (gridStage G v k r M) Θ ∧ ∃ (I : Type) (N : I → SmT (gridStage G v k r M).M →ₗ[ℂ] SmT (gridStage G v 0 r₀ M₀).M), (∀ ι y w, GlobalTheory.EvenOnto.PiLocalization₂ …`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`. Use `⟨r₀, M₀, hr₀, LinearMap.id, GlobalTheory.EvenOnto.Reach.zero, PUnit, fun _ => LinearMap.id, ?_, ?_⟩` and prove the remaining obligations.

Introduce `_ y w`. Use `⟨Function.update (fun i => (0 : Fn G (.core i))) 0 (GlobalTheory.EvenOnto.PiLocalization₂.val y w), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Take `rfl : i = 0` from `by omega`. Use `show GlobalTheory.Grow.RapidDec _ (GlobalTheory.EvenOnto.PiLocalization₂.val y w)`.

Conclude with `rapid 0 (Nat.zero_le _) r₀ hr₀ M₀ y w`. Introduce `i hi`. Use linear arithmetic over natural numbers and integers. Conclude with `Function.update_self _ _ _`. Conclude with `Function.update_self _ _ _`.

Introduce `x hx`. Conclude with `Submodule.subset_span ⟨PUnit.unit, x, hx, rfl⟩`. Consider the case `succ k ih`. Introduce `hk`. Take `⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩` from `ih (by omega)`.

Take `⟨r', hr'⟩` from `(hStage (k + 1) hk).1`. Take `⟨M', -⟩` from `hCM' (k + 1) hk`. Establish `hs` using `(hStage k (by omega)).2 r hr v M`. Establish `hs'` using `(hStage (k + 1) hk).2 r' hr' v M'`. Take `⟨ω, f, hpre, hexch, hdep⟩` from `hPre k (by omega) r r' hr hr' v M M'`.

Establish `hkm : k < (gridCom W).m` using `by show k < D.R.m; omega`. Take `⟨p, hpω, hpf, hp⟩` from `hStep (gridCom W) hCom k hkm _ _ hs hs' ω f hpre`. Substitute `hpω hpf` using the available equality. Use `⟨r', M', hr', Θ ∘ₗ p.io, GlobalTheory.EvenOnto.Reach.step hΘ hs' p hp, I × PolF D _ _, fun q => N q.1 ∘ₗ p.It q.2, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨ι, P⟩ y w`.

Establish `h1` using `ha ι (p.io y) (p.It P w)`. Establish `hth : IsThetaFunO W.ψ (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P)` using `((hEx W.ψ (G.V (.core k)) (G.V (.core (k + 1))) W.ψ_std).1 _).2 (hdep P).1`. Establish `heq : GlobalTheory.EvenOnto.PiLocalization₂.val (p.io y) (p.It P w) = dn W v k (exch (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w)`. Use function extensionality and compare the values at `g`. Use `(hp.io.eq y P w g).symm.trans ?_` and prove the remaining obligations.

Simplify using `only [Formalism.IndefR.Lift.liftInt, dn]`. Use `congr 1`. Use function extensionality and compare the values at `h`. Use `congr 1`. Use `show _ = thetaKO (W.om (.core k)) (negGA _ h) g _`.

Unfold `thetaKO`. Rewrite using `[hexch _ hth g h]`. Establish `hadj : GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0 = 0`. Simplify using `[GlobalTheory.PairLift.adjO]`. Use `show _ = (p.ω (g, h) (p.pt P)) (GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0)`.

Rewrite using `[hadj]`. Rewrite `h1` using `[heq]`. Conclude with `ext k _ _ _ (hdep P) (rapid (k + 1) hk r' hr' M' y w) h1`. Introduce `x hx`. Establish `hx'` using `hb hx`.

Use `(Submodule.span_le.2 ?_) hx'` and prove the remaining obligations. Introduce and unpack `_ ⟨ι, w, hw, rfl⟩`. Establish `hon` using `GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ _ _ W.θ W.ψ ((gridCom W).a k) ((gridCom W).a k) p.ω p.f p.It hCom.inf ⟨(gridCom W).χ k, (gridCom W).χ k, hp.pre.weil, fun τ => ⟨hCom.exp k hkm τ, hCom.exp k hkm τ⟩⟩ hp.pre.vac hp.it hw`. Establish `hmap : (Submodule.span ℂ {w' | ∃ P, ∃ v' ∈ (gridStage G v (k + 1) r' M').KF, w' = p.It P v'}).map (N ι) ≤ Submodule.span ℂ {x | ∃ q : I × PolF D _ _, ∃ w ∈ (gridStage G v (k + 1) r' M').KF, x = (N q.1 ∘ₗ p.It q.2) w}`. Rewrite using `[Submodule.map_span]`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨P, v', hv', rfl⟩, rfl⟩`. Conclude with `Submodule.subset_span ⟨(ι, P), v', hv', rfl⟩`. Conclude with `hmap (Submodule.mem_map_of_mem hon)`. Introduce `k hk`.

Take `⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩` from `key k hk`. Use `⟨r, M, hr, Θ, hΘ, fun y x hx => ?_⟩` and prove the remaining obligations. Set `φ : SmT (gridStage G v 0 r₀ M₀).M →ₗ[ℂ] Fn G (.core 0)` to `(Θ y).1`. Establish `hmap : (Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w}).map φ ≤ Submodule.span ℂ {F₀ : Fn G (.core 0) | ∃ w, F₀ ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)}`. Rewrite using `[Submodule.map_span]`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨ι, w, -, rfl⟩, rfl⟩`. Conclude with `Submodule.subset_span ⟨w, ha ι y w⟩`. Conclude with `hmap (Submodule.mem_map_of_mem (hb hx))`.
-/
theorem chainEx (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules)
    (hCR : GlobalTheory.Published.CuspRapidDecay) (hCW : GlobalTheory.Published.CasselmanWallach) (hDF : DepFixed) (hCM : CoreModels) : ChainEx := by
  intro D hq hsz T L μ0 hL sc hgap G W Mv hM v r₀ M₀ hr₀
  have hCom : (gridCom W).Is := GlobalTheory.T.testGridCommonData_properties_hold D hq hsz T L μ0 hL sc hgap G W Mv hM
  have hStage := GlobalTheory.T.testGridStageLatticesProperties_proof D hq T L μ0 hL sc G W Mv hM
  have hPre := GlobalTheory.T.core_chain_pre_steps_exist_of_depth_congruence hDF D hq hsz T L μ0 hL sc hgap G W Mv hM
  have hCM' := hCM D hq T L μ0 hL sc G W Mv hM
  have hStep := GlobalTheory.T.evenRankThetaChain_weilDatum_extends_to_step hDS hHC hCR hCW D
  have hConj := GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCR D
  have hEx := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D

  have rapid : ∀ i, i ≤ D.R.m → ∀ r, IsCoreLat G i r → ∀ M (y : (gridStage G v i r M).CC (gridCom W)) w,
      GlobalTheory.Grow.RapidDec (G.V (.core i)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w) := by
    intro i hi r hr M y w
    have hs := (hStage i hi).2 r hr v M
    have h1 := (hConj (gridCom W) hCom i hi _ hs).1 y w
    exact ((hRL.2.1 _ r W.θ _ M ∅).2.2.2.2 _).1 h1.2.2.2.2

  have ext : ∀ k (F₀ : Fn G (.core 0)) (F : Fn G (.core (k + 1))) (f : Sch G (.coreDown k)), Dep W (.core k) f →
      GlobalTheory.Grow.RapidDec (G.V (.core (k + 1))) F → F₀ ∈ Below W v k (dn W v k f F) → F₀ ∈ Below W v (k + 1) F := by
    rintro k F₀ F f hf hF ⟨Ψ, h1, h2, h3, h4⟩
    refine ⟨Function.update Ψ (k + 1) F, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases eq_or_ne i (k + 1) with rfl | hne
      · rw [Function.update_self]; exact hF
      · rw [Function.update_of_ne hne]; exact h1 i (by omega)
    · intro i hi
      rcases Nat.lt_or_ge i k with hik | hik
      · obtain ⟨f', hf', e⟩ := h2 i hik
        refine ⟨f', hf', ?_⟩
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact e
      · obtain rfl : i = k := by omega
        refine ⟨f, hf, ?_⟩
        rw [Function.update_of_ne (by omega), Function.update_self]
        exact h4
    · rw [Function.update_of_ne (by omega)]; exact h3
    · exact Function.update_self _ _ _
  have key : ∀ k, k ≤ D.R.m → ∃ r M, IsCoreLat G k r ∧ ∃ Θ, GlobalTheory.EvenOnto.Reach (gridCom W) (gridStage G v 0 r₀ M₀) k
      (gridStage G v k r M) Θ ∧ ∃ (I : Type) (N : I → SmT (gridStage G v k r M).M →ₗ[ℂ] SmT (gridStage G v 0 r₀ M₀).M),
      (∀ ι y w, GlobalTheory.EvenOnto.PiLocalization₂.val (Θ y) (N ι w) ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)) ∧
      (gridStage G v 0 r₀ M₀).KF ≤ Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w} := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨r₀, M₀, hr₀, LinearMap.id, GlobalTheory.EvenOnto.Reach.zero, PUnit, fun _ => LinearMap.id, ?_, ?_⟩
      · intro _ y w
        refine ⟨Function.update (fun i => (0 : Fn G (.core i))) 0 (GlobalTheory.EvenOnto.PiLocalization₂.val y w), ?_, ?_, ?_, ?_⟩
        · intro i hi
          obtain rfl : i = 0 := by omega
          show GlobalTheory.Grow.RapidDec _ (GlobalTheory.EvenOnto.PiLocalization₂.val y w)
          exact rapid 0 (Nat.zero_le _) r₀ hr₀ M₀ y w
        · intro i hi; omega
        · exact Function.update_self _ _ _
        · exact Function.update_self _ _ _
      · intro x hx
        exact Submodule.subset_span ⟨PUnit.unit, x, hx, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩ := ih (by omega)
      obtain ⟨r', hr'⟩ := (hStage (k + 1) hk).1
      obtain ⟨M', -⟩ := hCM' (k + 1) hk
      have hs := (hStage k (by omega)).2 r hr v M
      have hs' := (hStage (k + 1) hk).2 r' hr' v M'
      obtain ⟨ω, f, hpre, hexch, hdep⟩ := hPre k (by omega) r r' hr hr' v M M'
      have hkm : k < (gridCom W).m := by show k < D.R.m; omega
      obtain ⟨p, hpω, hpf, hp⟩ := hStep (gridCom W) hCom k hkm _ _ hs hs' ω f hpre
      subst hpω hpf
      refine ⟨r', M', hr', Θ ∘ₗ p.io, GlobalTheory.EvenOnto.Reach.step hΘ hs' p hp, I × PolF D _ _,
        fun q => N q.1 ∘ₗ p.It q.2, ?_, ?_⟩
      · rintro ⟨ι, P⟩ y w
        have h1 := ha ι (p.io y) (p.It P w)
        have hth : IsThetaFunO W.ψ (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P) :=
          ((hEx W.ψ (G.V (.core k)) (G.V (.core (k + 1))) W.ψ_std).1 _).2 (hdep P).1
        have heq : GlobalTheory.EvenOnto.PiLocalization₂.val (p.io y) (p.It P w) =
            dn W v k (exch (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w) := by
          funext g
          refine (hp.io.eq y P w g).symm.trans ?_
          simp only [Formalism.IndefR.Lift.liftInt, dn]
          congr 1
          funext h
          congr 1
          show _ = thetaKO (W.om (.core k)) (negGA _ h) g _
          unfold thetaKO
          rw [hexch _ hth g h]
          have hadj : GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0 = 0 := by
            simp [GlobalTheory.PairLift.adjO]
          show _ = (p.ω (g, h) (p.pt P)) (GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0)
          rw [hadj]
        rw [heq] at h1
        exact ext k _ _ _ (hdep P) (rapid (k + 1) hk r' hr' M' y w) h1
      · intro x hx
        have hx' := hb hx
        refine (Submodule.span_le.2 ?_) hx'
        rintro _ ⟨ι, w, hw, rfl⟩
        have hon := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ _ _ W.θ W.ψ ((gridCom W).a k) ((gridCom W).a k) p.ω p.f p.It
          hCom.inf ⟨(gridCom W).χ k, (gridCom W).χ k, hp.pre.weil, fun τ => ⟨hCom.exp k hkm τ, hCom.exp k hkm τ⟩⟩
          hp.pre.vac hp.it hw
        have hmap : (Submodule.span ℂ {w' | ∃ P, ∃ v' ∈ (gridStage G v (k + 1) r' M').KF, w' = p.It P v'}).map (N ι) ≤
            Submodule.span ℂ {x | ∃ q : I × PolF D _ _, ∃ w ∈ (gridStage G v (k + 1) r' M').KF, x = (N q.1 ∘ₗ p.It q.2) w} := by
          rw [Submodule.map_span]
          refine Submodule.span_le.2 ?_
          rintro _ ⟨_, ⟨P, v', hv', rfl⟩, rfl⟩
          exact Submodule.subset_span ⟨(ι, P), v', hv', rfl⟩
        exact hmap (Submodule.mem_map_of_mem hon)
  intro k hk
  obtain ⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩ := key k hk
  refine ⟨r, M, hr, Θ, hΘ, fun y x hx => ?_⟩
  let φ : SmT (gridStage G v 0 r₀ M₀).M →ₗ[ℂ] Fn G (.core 0) := (Θ y).1
  have hmap : (Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w}).map φ ≤
      Submodule.span ℂ {F₀ : Fn G (.core 0) | ∃ w, F₀ ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)} := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨ι, w, -, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨w, ha ι y w⟩
  exact hmap (Submodule.mem_map_of_mem (hb hx))

end GlobalTheory.ChainLifts
