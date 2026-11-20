import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparates

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols Separates rowForm)

noncomputable section

namespace GlobalTheory.RowEx

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `hmem : R.HE.e u ∈ R.EEat R.triv` using `hM.HE.2.1 ▸ LinearMap.mem_range_self _ u`. Establish `hne : R.HE.e u ≠ 0` using `fun h => h0 (hM.HE.1 (h.trans (map_zero _).symm))`. Take `⟨Ψ, hΨ, Φ, -, hf⟩` from `hsep _ hmem hne`. Apply `hf` to reduce the goal to its premises.

Rewrite `hΨ` using `[← span_col_eq_cols ch Φ]`. Establish `key : ∀ x ∈ Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}), BplusConv ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x) (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) ∧ Bplus ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x) (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R …`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, ha, rfl⟩` from `hx`. Establish `ha' : ch.Phi a = Φ` using `ha`. Establish `h1 : FConv ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u)` using `hconv a u`. Establish `h2 : fPsiPhi ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) = 0` using `hu a`. Rewrite `h1`, `h2` using `[ha']`.

Conclude with `⟨h1.2, h2⟩`. Consider the case `zero`. Rewrite using `[LinearMap.map_zero (pairVec (coefPlus ch.G ch.W.θ) ch.ξ)]`. Conclude with `bplusConv_zero ch.W ch.M _`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[LinearMap.map_add (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) x y]`. Take `⟨hc, he⟩` from `bplusConv_add ch.W ch.M hx.1 hy.1`. Conclude with `⟨hc, by rw [he, hx.2, hy.2, add_zero]⟩`. Consider the case `smul c x _ hx`. Rewrite using `[LinearMap.map_smul (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) c x]`.

Take `⟨hc, he⟩` from `bplusConv_smul ch.W ch.M c hx.1`. Conclude with `⟨hc, by rw [he, hx.2, mul_zero]⟩`. Conclude with `(key Ψ hΨ).2`.
-/
theorem inj_of_sep_conv {ch : Choice R} (hM : R.IsModels) (hsep : Separates R ch.W ch.M ch.w ch.ρ ch.ξ)
    (hconv : ∀ a u, ConvK ch a u) (u : R.HE.H) (hu : ∀ a, psiK ch a u = 0) : u = 0 := by
  by_contra h0
  have hmem : R.HE.e u ∈ R.EEat R.triv := hM.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have hne : R.HE.e u ≠ 0 := fun h => h0 (hM.HE.1 (h.trans (map_zero _).symm))
  obtain ⟨Ψ, hΨ, Φ, -, hf⟩ := hsep _ hmem hne
  apply hf
  rw [← span_col_eq_cols ch Φ] at hΨ
  have key : ∀ x ∈ Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}),
      BplusConv ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x)
          (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) ∧
        Bplus ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x)
          (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : ch.Phi a = Φ := ha
      have h1 : FConv ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) := hconv a u
      have h2 : fPsiPhi ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) = 0 := hu a
      rw [ha'] at h1 h2
      exact ⟨h1.2, h2⟩
    | zero =>
      rw [LinearMap.map_zero (pairVec (coefPlus ch.G ch.W.θ) ch.ξ)]; exact bplusConv_zero ch.W ch.M _
    | add x y _ _ hx hy =>
      rw [LinearMap.map_add (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) x y]
      obtain ⟨hc, he⟩ := bplusConv_add ch.W ch.M hx.1 hy.1
      exact ⟨hc, by rw [he, hx.2, hy.2, add_zero]⟩
    | smul c x _ hx =>
      rw [LinearMap.map_smul (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) c x]
      obtain ⟨hc, he⟩ := bplusConv_smul ch.W ch.M c hx.1
      exact ⟨hc, by rw [he, hx.2, mul_zero]⟩
  exact (key Ψ hΨ).2

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨C1, hL⟩` from `hL`. Take `⟨C2, hB⟩` from `hB`. Use `⟨max 6510 (max C1 C2), fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨x1, hS⟩` from `hS ε CF (le_of_max_le_left hCF)`. Take `⟨x2, hL⟩` from `hL ε CF (le_trans (le_max_left _ _) (le_of_max_le_right hCF))`.

Take `⟨x3, hB⟩` from `hB ε CF (le_trans (le_max_right _ _) (le_of_max_le_right hCF))`. Use `⟨max x1 (max x2 x3), fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset G W hW S₀ => ?_⟩` and prove the remaining obligations. Establish `hx1 : x1 ≤ large₂.sc.x` using `le_of_max_le_left hx`. Establish `hx2 : x2 ≤ large₂.sc.x` using `le_trans (le_max_left _ _) (le_of_max_le_right hx)`. Establish `hx3 : x3 ≤ large₂.sc.x` using `le_trans (le_max_right _ _) (le_of_max_le_right hx)`.

Take `⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS0, hbase⟩` from `hB D large₂ hε hx3 Γ Pl0 T A Ks R F hset G W hW S₀`. Take `⟨ρ', ξ', hsep⟩` from `hS D large₂ hε hx1 hset.size hset.eser Γ Pl0 T A Ks R hset.core.lev hset.grp G W hbase.weil M hbase.vol _ hbase.w_ne`. Establish `hconv` using `hL D large₂ hε hx2 Γ Pl0 T A Ks R F hset _ rfl (hbase.withReal ρ' ξ')`. Conclude with `⟨M, ρ', ξ', cv, rm, S, rp, n, e, c, hS0, hbase.is_withReal (inj_of_sep_conv hset.core.models hsep hconv)⟩`.
-/
theorem isEx_of_separates (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate) (hL : LinB) (hB : BaseEx) : IsEx := by
  obtain ⟨C1, hL⟩ := hL
  obtain ⟨C2, hB⟩ := hB
  refine ⟨max 6510 (max C1 C2), fun ε CF hCF => ?_⟩
  obtain ⟨x1, hS⟩ := hS ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, hL⟩ := hL ε CF (le_trans (le_max_left _ _) (le_of_max_le_right hCF))
  obtain ⟨x3, hB⟩ := hB ε CF (le_trans (le_max_right _ _) (le_of_max_le_right hCF))
  refine ⟨max x1 (max x2 x3), fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset G W hW S₀ => ?_⟩
  have hx1 : x1 ≤ large₂.sc.x := le_of_max_le_left hx
  have hx2 : x2 ≤ large₂.sc.x := le_trans (le_max_left _ _) (le_of_max_le_right hx)
  have hx3 : x3 ≤ large₂.sc.x := le_trans (le_max_right _ _) (le_of_max_le_right hx)
  obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS0, hbase⟩ := hB D large₂ hε hx3 Γ Pl0 T A Ks R F hset G W hW S₀
  obtain ⟨ρ', ξ', hsep⟩ := hS D large₂ hε hx1 hset.size hset.eser Γ Pl0 T A Ks R hset.core.lev hset.grp G W hbase.weil M
    hbase.vol _ hbase.w_ne
  have hconv := hL D large₂ hε hx2 Γ Pl0 T A Ks R F hset _ rfl (hbase.withReal ρ' ξ')
  exact ⟨M, ρ', ξ', cv, rm, S, rp, n, e, c, hS0,
    hbase.is_withReal (inj_of_sep_conv hset.core.models hsep hconv)⟩

/- English proof (translation)
The claim follows from `isEx_of_separates`.
-/
example : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → LinB → BaseEx → IsEx := isEx_of_separates

end GlobalTheory.RowEx

end
