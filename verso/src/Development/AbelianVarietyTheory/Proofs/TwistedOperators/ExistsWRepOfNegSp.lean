import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

/- English proof (translation)
Substitute `hS` using the available equality. Substitute `hT` using the available equality. Set `ω : GlobalTheory.Grid.WRep S T` to `om.comp (((GlobalTheory.Grid.ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _) : GA D S × GA D T →* GA D (negSp S) × GA D T))`. Establish `e : ω.toSgn true = om` using `MonoidHom.ext fun _ => rfl`. Use `⟨ω, ?_, heq_of_eq e⟩` and prove the remaining obligations.

Use `show IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (ω.toSgn true)`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem exists_wRep_of_negSp {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χS χT om) :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ true S T χS χT ω ∧ HEq (ω.toSgn true) om := by
  subst hS; subst hT
  let ω : GlobalTheory.Grid.WRep S T :=
    om.comp (((GlobalTheory.Grid.ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _) :
      GA D S × GA D T →* GA D (negSp S) × GA D T))
  have e : ω.toSgn true = om := MonoidHom.ext fun _ => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  show IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (ω.toSgn true)
  rw [e]
  exact h

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

/- English proof (translation)
Introduce `D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hG _ hsp _ i j hi hj`. Establish `hv1` using `(hsp.vert (i + 1) j (by omega) hj).sp`. Establish `hv0` using `(hsp.vert i j (by omega) hj).sp`. Establish `hom` using `W.om_is (.chi i j) ⟨by omega, hj⟩`. Rewrite `hom` using `[hW.ψ]`.

Take `⟨ω, h1, h2⟩` from `exists_wRep_of_negSp hv1 hv0 R.ψ _ _ (W.om (.chi i j)) hom`. Use `⟨ω, ?_, h2⟩` and prove the remaining obligations. Establish `hchi : G.chi (D.R.m - i) = G'.ch.chi (D.R.m - i)` using `hsp.chi _ (by omega) (by omega)`. Establish `rS : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j`. Rewrite using `[← hv1]; exact (hG.vert i j (by omega) hj).rank`.

Establish `rT : (G'.V (.grid i j)).rank = rkV D i j`. Rewrite using `[← hv0]`. Consider the cases of `i with`. Consider the case `succ k => exact (hG.vert k j (by omega) hj).rank`. Consider the case `zero`.

Rewrite using `[hv0]`. Use `show (columnBlock R.toLevCh j).sp.rank = _`. Simplify using `only [rkV, zero_mul, add_zero]`. Break down `hj.eq_or_lt with rfl | hk` into its components or cases. Rewrite using `[colY_m]`.

Conclude with `D.sp.X'_rank`. Rewrite using `[colY_lt _ hk]`. Conclude with `(D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)`. Establish `cS : G'.chrS (.chi i j) = G.chiAt (D.R.m - i) (rkV D (i + 1) j)` using `by show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid (i + 1) j)).rank = _`. Rewrite using `[rS, ← hchi]`.

Establish `cT : G'.chrT (.chi i j) = G.chiAt (D.R.m - i) (rkV D i j)` using `by show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid i j)).rank = _`. Rewrite using `[rT, ← hchi]`. Rewrite `h1` using `[cS, cT]`. Conclude with `h1`.
-/
theorem exists_omX_of_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V, GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω ∧ HEq (ω.toSgn true) (W.om (.chi i j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hG _ hsp _ i j hi hj
  have hv1 := (hsp.vert (i + 1) j (by omega) hj).sp
  have hv0 := (hsp.vert i j (by omega) hj).sp
  have hom := W.om_is (.chi i j) ⟨by omega, hj⟩
  rw [hW.ψ] at hom
  obtain ⟨ω, h1, h2⟩ := exists_wRep_of_negSp hv1 hv0 R.ψ _ _ (W.om (.chi i j)) hom
  refine ⟨ω, ?_, h2⟩
  have hchi : G.chi (D.R.m - i) = G'.ch.chi (D.R.m - i) := hsp.chi _ (by omega) (by omega)
  have rS : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← hv1]; exact (hG.vert i j (by omega) hj).rank
  have rT : (G'.V (.grid i j)).rank = rkV D i j := by
    rw [← hv0]
    cases i with
    | succ k => exact (hG.vert k j (by omega) hj).rank
    | zero =>
      rw [hv0]
      show (columnBlock R.toLevCh j).sp.rank = _
      simp only [rkV, zero_mul, add_zero]
      rcases hj.eq_or_lt with rfl | hk
      · rw [colY_m]; exact D.sp.X'_rank
      · rw [colY_lt _ hk]
        exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)
  have cS : G'.chrS (.chi i j) = G.chiAt (D.R.m - i) (rkV D (i + 1) j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid (i + 1) j)).rank = _
    rw [rS, ← hchi]
  have cT : G'.chrT (.chi i j) = G.chiAt (D.R.m - i) (rkV D i j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid i j)).rank = _
    rw [rT, ← hchi]
  rw [cS, cT] at h1
  exact h1

end GlobalTheory.GridJoin
