import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SmallRoute

/- English proof (translation)
Establish `hmp : MeasurePreserving (· * k) ν ν` using `measurePreserving_mul_right ν k`. Establish `hme : MeasurableEmbedding (· * k)` using `(MeasurableEquiv.mulRight k).measurableEmbedding`. Establish `hfd' : IsFundamentalDomain Γ ((· * k⁻¹) ⁻¹' fd) ν`. Use `hfd.preimage_of_equiv (measurePreserving_mul_right ν k⁻¹).quasiMeasurePreserving (e := id) Function.bijective_id ?_` and prove the remaining obligations. Introduce `g x`.

Simplify using `only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]`. Establish `hinv : ∀ g : Γ, ∀ x, φ (g • x) = φ x` using `fun g x => hφ g g.2 x`. Establish `hpre : (· * k) ⁻¹' ((· * k⁻¹) ⁻¹' fd) = fd`. Use extensionality with `u`. Simplify using the standard rewrite rules.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1 : IntegrableOn φ ((· * k⁻¹) ⁻¹' fd) ν` using `(hfd'.integrableOn_iff hfd hinv).2 hi`. Establish `h2` using `(hmp.integrableOn_comp_preimage hme (f := φ) (s := (· * k⁻¹) ⁻¹' fd)).2 h1`. Rewrite `h2` using `[hpre]`. Conclude with `h2`.

Establish `h3` using `hmp.setIntegral_preimage_emb hme φ ((· * k⁻¹) ⁻¹' fd)`. Rewrite `h3` using `[hpre]`. Rewrite using `[h3]`. Conclude with `hfd'.setIntegral_eq hfd hinv`.
-/
theorem setIntegral_mul_right_of_left_inv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] (Γ : Subgroup H) [Countable Γ] (ν : Measure H)
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] {fd : Set H} (hfd : IsFundamentalDomain Γ fd ν) {φ : H → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ u, φ (γ * u) = φ u) (hi : IntegrableOn φ fd ν) (k : H) :
    IntegrableOn (fun u => φ (u * k)) fd ν ∧ ∫ u in fd, φ (u * k) ∂ν = ∫ u in fd, φ u ∂ν := by
  have hmp : MeasurePreserving (· * k) ν ν := measurePreserving_mul_right ν k
  have hme : MeasurableEmbedding (· * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd' : IsFundamentalDomain Γ ((· * k⁻¹) ⁻¹' fd) ν := by
    refine hfd.preimage_of_equiv (measurePreserving_mul_right ν k⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ g : Γ, ∀ x, φ (g • x) = φ x := fun g x => hφ g g.2 x
  have hpre : (· * k) ⁻¹' ((· * k⁻¹) ⁻¹' fd) = fd := by
    ext u; simp
  refine ⟨?_, ?_⟩
  · have h1 : IntegrableOn φ ((· * k⁻¹) ⁻¹' fd) ν := (hfd'.integrableOn_iff hfd hinv).2 hi
    have h2 := (hmp.integrableOn_comp_preimage hme (f := φ) (s := (· * k⁻¹) ⁻¹' fd)).2 h1
    rw [hpre] at h2
    exact h2
  · have h3 := hmp.setIntegral_preimage_emb hme φ ((· * k⁻¹) ⁻¹' fd)
    rw [hpre] at h3
    rw [h3]
    exact hfd'.setIntegral_eq hfd hinv

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Unfold `tensT at hd`. Take `⟨P, -, hP⟩` from `Finset.mem_biUnion.1 (Finsupp.support_sum hd)`. Take `⟨d₀, hd₀, h⟩` from `Finset.mem_biUnion.1 (Finsupp.support_sum hP)`. Conclude with `⟨d₀, hd₀, P, Finset.mem_singleton.1 (Finsupp.support_single_subset h)⟩`.
-/
theorem mem_support_tensT (W : G.Weil) {X Y : Node} {p : Path T X Y} {τi : PolT G p →₀ ℂ} {τf : TotT G p} {d : PureT G p}
    (hd : d ∈ (tensT W τi τf).support) :
    ∃ d₀ ∈ τf.support, ∃ P, d = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d₀ P := by
  classical
  unfold tensT at hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d₀, hd₀, h⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  exact ⟨d₀, hd₀, P, Finset.mem_singleton.1 (Finsupp.support_single_subset h)⟩

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Take `⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩` from `hΘ`. Take `⟨d₀, hd₀, P, rfl⟩` from `mem_support_tensT W hd`. Take `⟨h1, h2⟩` from `hloc d₀ hd₀`. Establish `v1` using `ρ.vT_is t i j i.2.le j.2`. Establish `v2` using `ρ.vX_is i j i.2 j.2.le`.

Establish `t1` using `GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta`. Establish `t2` using `GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta`. Conclude with `⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _, GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _⟩`.
-/
theorem theta_of_matched {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (hΘ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeSmall t i j)} (hd : d ∈ Θ'.support) :
    IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vT_is t i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _,
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _⟩

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Establish `hc` using `W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩`. Establish `hm` using `W.om_is (.mu t (i : ℕ) j) ⟨i.2.le, j.2⟩`. Unfold `outer`. Use `congr 1`. Use `show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (γ * u) d.2 = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u d.2`.

Unfold `thetaKO`. Establish `e : ((negGA _ g₁, γ * u) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) = (1, γ) * (negGA _ g₁, u)` using `by simp`. Rewrite using `[e, map_mul, Module.End.mul_apply]`. Conclude with `hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h2)`. Use `integral_congr_ae (.of_forall fun g => ?_) show thetaKO (W.om (.mu t (i : ℕ) j)) (γ * u) g d.1.2 * F g = thetaKO (W.om (.mu t (i : ℕ) j)) u g d.1.2 * F g` and prove the remaining obligations.

Unfold `thetaKO`. Establish `e : ((γ * u, g) : GA D (G.pS (.mu t (i : ℕ) j)) × GA D (G.pT (.mu t (i : ℕ) j))) = (γ, 1) * (u, g)` using `by simp`. Rewrite using `[e, map_mul, Module.End.mul_apply, hm.om_aut γ hγ 1 (one_mem _) _ (hm.om_pres _ _ h1)]`.
-/
theorem outer_left (W : G.Weil) (M : Vol G) {t : T} {i j : Fin D.R.m} {d : PureT G (routeSmall t i j)}
    (h2 : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2)
    (h1 : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2) (F : Fn G (.grid i (j + 1)))
    (g₁ : GA D (G.V (.grid (i + 1) j))) {γ : GA D (G.V (.grid i j))} (hγ : γ ∈ GQ (G.V (.grid i j)))
    (u : GA D (G.V (.grid i j))) : outer W M d F g₁ (γ * u) = outer W M d F g₁ u := by
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have hm := W.om_is (.mu t (i : ℕ) j) ⟨i.2.le, j.2⟩
  unfold outer
  congr 1
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (γ * u) d.2 = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u d.2
    unfold thetaKO
    have e : ((negGA _ g₁, γ * u) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (1, γ) * (negGA _ g₁, u) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h2)
  · refine integral_congr_ae (.of_forall fun g => ?_)
    show thetaKO (W.om (.mu t (i : ℕ) j)) (γ * u) g d.1.2 * F g = thetaKO (W.om (.mu t (i : ℕ) j)) u g d.1.2 * F g
    unfold thetaKO
    have e : ((γ * u, g) : GA D (G.pS (.mu t (i : ℕ) j)) × GA D (G.pT (.mu t (i : ℕ) j))) = (γ, 1) * (u, g) := by simp
    rw [e, map_mul, Module.End.mul_apply, hm.om_aut γ hγ 1 (one_mem _) _ (hm.om_pres _ _ h1)]

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

/- English proof (translation)
Introduce `D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ F hF hB g₁ z`. Take `⟨hH, hfd⟩` from `(hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund`. Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid i j))`. Use `haveI := hH`. Use `haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ (M.ν (.grid i j)) hH`.

Establish `key : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)) ∧ ∫ u in M.fd (.grid i j), outer W M d F g₁ (u * k) ∂M.ν (.grid i j) = ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j)` using `fun d hd k => by`. Take `⟨h2, h1⟩` from `theta_of_matched hΘ hd`. Use `setIntegral_mul_right_of_left_inv (GQ (G.V (.grid i j))) (M.ν (.grid i j)) hfd (fun γ hγ u => outer_left W M h2 h1 F g₁ hγ u) ?_ k` and prove the remaining obligations. Conclude with `(hB d hd).2 g₁`. Use `⟨fun d hd k => (key d hd k).1, ?_⟩` and prove the remaining obligations.

Rewrite using `[liftT_routeSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `e : ∫ u in M.fd (.grid i j), translates z (outer W M d F g₁) u ∂M.ν (.grid i j) = zdeg z * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j)`. Unfold `translates zdeg`. Simplify using `only [Finsupp.sum]`.

Rewrite using `[integral_finset_sum _ fun k _ => ((key d hd k).1.integrable.const_mul _), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul, (key d hd k).2]`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zdeg_mul_liftT : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j)))
    (z : GA D (G.V (.grid i j)) →₀ ℂ),
    (∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    zdeg z * liftT W M (routeSmall t i j) Θ' F g₁ =
      Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ F hF hB g₁ z
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid i j))
  haveI := hH
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ (M.ν (.grid i j)) hH
  have key : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)) ∧
      ∫ u in M.fd (.grid i j), outer W M d F g₁ (u * k) ∂M.ν (.grid i j) =
        ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := fun d hd k => by
    obtain ⟨h2, h1⟩ := theta_of_matched hΘ hd
    refine setIntegral_mul_right_of_left_inv (GQ (G.V (.grid i j))) (M.ν (.grid i j)) hfd
      (fun γ hγ u => outer_left W M h2 h1 F g₁ hγ u) ?_ k
    exact (hB d hd).2 g₁
  refine ⟨fun d hd k => (key d hd k).1, ?_⟩
  rw [liftT_routeSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : ∫ u in M.fd (.grid i j), translates z (outer W M d F g₁) u ∂M.ν (.grid i j) =
      zdeg z * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := by
    unfold translates zdeg
    simp only [Finsupp.sum]
    rw [integral_finset_sum _ fun k _ => ((key d hd k).1.integrable.const_mul _),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, (key d hd k).2]
  rw [e]
  ring

end GlobalTheory.SmallRoute
