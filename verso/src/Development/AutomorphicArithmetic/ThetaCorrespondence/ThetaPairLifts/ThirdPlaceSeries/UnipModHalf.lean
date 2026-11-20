import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowWeightGramAlgebraic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.LevelUnip
section Res
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
end Res
variable {D : D7}
end GlobalTheory.LevelUnip
open GlobalTheory.LevelUnip in
/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF g z hz`. Take `⟨κ, hk, hf⟩` from `(p.pins i).2.lift.lev g`. Establish `hB` using `p.charW.base`. Take `⟨ψ0, -, hlev, -⟩` from `hB.grp.levels`. Establish `hL` using `hB.lev`.

Establish `hu : p.R.eG g ∈ (p.R.levR p.F.lv2 false).H` using `by show p.R.eG.symm.toMonoidHom (p.R.eG g) ∈ (p.F.lv2.lvl false).P`. Simplify using the standard rewrite rules. Establish `hun : ∀ PP, p.R.eG g PP ∈ unip (kP PP.1) D.R.r`. Rewrite `hu` using `[hlev]`. Conclude with `fun PP => (Subgroup.mem_pi _).1 hu PP (Set.mem_univ _)`.

Establish `hhalf` using `((p.pins i).2.tuple ()).half.1`. Establish `hemb` using `GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i`. Establish `hβ` using `hL.βW i`. Establish `hr` using `rank_Wc (D := D) i`. Establish `hkSt` using `parLev_St hk.2.1`.

Establish `hred : ∀ P ∈ p.R.Pg, (((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) - 1) ^ D.R.r = 0`. Introduce `P hP`. Establish `hb` using `blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)`. Establish `e : upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) = p.R.eG g ⟨P, hP⟩` using `congrFun hk.2.2 ⟨P, hP⟩`. Establish `hU` using `hun ⟨P, hP⟩`.

Rewrite `hU` using `[← e]`. Establish `hv` using `upper_block_val_submatrix (p.R.datWp i p.R.triv).hr hb`. Establish `hent : ∀ a c : Fin (Wc D i).rank, ((upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) : GL (Fin D.R.r) (kP P)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP P)) (Fin.cast hr a) (Fin.cast hr c) = ((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i …`. Introduce `a c`. Conclude with `(congrFun (congrFun hv (Fin.cast hr a)) (Fin.cast hr c)).trans rfl`.

Rewrite using `[← hr]`. Apply `sub_one_pow_eq_zero'` to reduce the goal to its premises. Introduce `a c hca`. Rewrite using `[← hent]`. Conclude with `hU.1 (show ((Fin.cast hr c : Fin D.R.r) : ℕ) < (Fin.cast hr a : Fin D.R.r) from hca)`.

Introduce `a`. Rewrite using `[← hent]`. Conclude with `hU.2 _`. Establish `hp : p.T.Q.l.Mb * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)}` using `p.T.Q.l.prod`. Establish `hp' : (∏ P ∈ p.R.Pg, P.asIdeal) * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)}`.

Rewrite using `[← hhalf]`. Conclude with `hp`. Establish `hI : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb` using `(hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)`. Establish `hc : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤` using `p.T.Q.l.coprime`. Establish `hcong` using `fun b (hb : b ∈ Mfr p.T.Q.l) => exists_pow_cong hβ p.R.Pg hp' hkSt hred hb`.

Establish `hpow` using `approx_pow hemb (sub_one_mulVec_mem hβ hkSt) hf D.R.r`. Establish `h0 : ∀ a ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1, finVec (Wc D i) (iotaW p.T i ((0 : (p.T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] _) a)) - (0 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (Af D.host.F ⊗[D.host.F] D.host. …`. Introduce `a _`. Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`.

Simplify using `[finVec]`. Use `GlobalTheory.LevelUnique.sub_mem_of_approx hemb (lt_of_lt_of_le (by norm_num) p.T.Q.l.three_le) hI hc hcong hpow h0 z` as an intermediate fact. Simplify using `using this`.
-/
theorem GlobalTheory.LevelUnip.unip_mod_half_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∀ (g : (p.F.lv2.lvl false).P) (z : (p.T.Q.Dw ((i : ℕ) + 1)).La), z ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) → (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) z ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF g z hz
  obtain ⟨κ, hk, hf⟩ := (p.pins i).2.lift.lev g
  have hB := p.charW.base
  obtain ⟨ψ0, -, hlev, -⟩ := hB.grp.levels
  have hL := hB.lev
  have hu : p.R.eG g ∈ (p.R.levR p.F.lv2 false).H := by
    show p.R.eG.symm.toMonoidHom (p.R.eG g) ∈ (p.F.lv2.lvl false).P
    simp
  have hun : ∀ PP, p.R.eG g PP ∈ unip (kP PP.1) D.R.r := by
    rw [hlev] at hu
    exact fun PP => (Subgroup.mem_pi _).1 hu PP (Set.mem_univ _)
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hemb := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hβ := hL.βW i
  have hr := rank_Wc (D := D) i
  have hkSt := parLev_St hk.2.1
  have hred : ∀ P ∈ p.R.Pg, (((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
      Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) - 1) ^ D.R.r = 0 := by
    intro P hP
    have hb := blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)
    have e : upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) = p.R.eG g ⟨P, hP⟩ :=
      congrFun hk.2.2 ⟨P, hP⟩
    have hU := hun ⟨P, hP⟩
    rw [← e] at hU
    have hv := upper_block_val_submatrix (p.R.datWp i p.R.triv).hr hb
    have hent : ∀ a c : Fin (Wc D i).rank,
        ((upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) : GL (Fin D.R.r) (kP P)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP P)) (Fin.cast hr a) (Fin.cast hr c) =
        ((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
          Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) a c := by
      intro a c
      exact (congrFun (congrFun hv (Fin.cast hr a)) (Fin.cast hr c)).trans rfl
    rw [← hr]
    apply sub_one_pow_eq_zero'
    · intro a c hca
      rw [← hent]
      exact hU.1 (show ((Fin.cast hr c : Fin D.R.r) : ℕ) < (Fin.cast hr a : Fin D.R.r) from hca)
    · intro a
      rw [← hent]
      exact hU.2 _
  have hp : p.T.Q.l.Mb * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := p.T.Q.l.prod
  have hp' : (∏ P ∈ p.R.Pg, P.asIdeal) * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by
    rw [← hhalf]; exact hp
  have hI : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb :=
    (hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)
  have hc : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤ := p.T.Q.l.coprime
  have hcong := fun b (hb : b ∈ Mfr p.T.Q.l) => exists_pow_cong hβ p.R.Pg hp' hkSt hred hb
  have hpow := approx_pow hemb (sub_one_mulVec_mem hβ hkSt) hf D.R.r
  have h0 : ∀ a ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La),
      ∃ w ∈ latGHat (Wc D i) 1, finVec (Wc D i) (iotaW p.T i ((0 : (p.T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] _) a)) -
        (0 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
          finVec (Wc D i) (iotaW p.T i a) = p.T.Q.l.M • w := by
    intro a _
    refine ⟨0, zero_mem _, ?_⟩
    funext j
    simp [finVec]
  have := GlobalTheory.LevelUnique.sub_mem_of_approx hemb (lt_of_lt_of_le (by norm_num) p.T.Q.l.three_le) hI hc hcong hpow h0 z
  simpa using this
end
end
