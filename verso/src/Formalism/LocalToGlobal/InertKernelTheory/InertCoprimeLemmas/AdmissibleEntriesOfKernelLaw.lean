import Formalism.LocalToGlobal.InertKernelTheory.ThetaSeriesDataHypothesesBelowMaximalLevel
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelCoupled
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.LatticeShapeMiddleHolds
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FirstKernelSmallOfFrameTwist

noncomputable section

namespace Formalism.L2.KerInert.AdmLoc2

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (be : MvPowerSeries (Fin 2) (Formalism.L2.G.Pend.K0 p))

/- English proof (translation)
Set `_` to `wittFractionAlgebraCp p`. Set `_` to `algKfC E`. Introduce `hS`. Set `ThR' : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]` to `fun j La La' => if j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2 then ThR j La La' else 0`. Establish `hS' : StabLaw X ℂ_[p] hfin ThR'`.

Introduce `j c L0 La' ε h0 hε`. Distinguish the cases in `hj : j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2`. Simplify using `only [ThR', if_pos hj]`. Conclude with `hS j hj.1 c L0 La' ε h0 hj.2 hε`. Simplify using `only [ThR', if_neg hj]`.

Unfold `SA`. Rewrite using `[← MvPowerSeries.coe_substAlgHom (hasSubst_actS X ℂ_[p] j _), map_zero, mul_zero]`. Establish `hK` using `kapLaw_of_stabLaw X ℂ_[p] hfin ThR' pC_ne_zero hS'`. Introduce `j hj c L La' γ G hGv hL hLa'`. Establish `hEq : ∀ La, thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR') j La La' = thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j La La'`.

Introduce `La`. Simplify using `only [thFN, thGeo, ThR', if_pos (And.intro hj hLa')]`. Establish `key : ∀ t : X.G.Kf, (eSX X j (c, (X.Lv.lev j c).smul γ L) * t) • delF X ℂ_[p] j ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G) (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, (X.Lv.lev j c).smul γ L) La') = (eSX X j (c, L) * t) • delF X ℂ_[p] j G (thFN X ℂ_ …`. Introduce `t`. Use `ker_law X ℂ_[p] pC_ne_zero (delEquivOn_GdC X ℂ_[p]) _ hK j c L La' γ G hL (vtIn_GdC X ℂ_[p] j G hGv) t` as an intermediate fact.

Rewrite `this` using `[hEq, hEq]`. Then use the resulting hypothesis. Conclude with `key _`.
-/
theorem admissible_stabilizer_of_law (D : Formalism.BasicNotions.D7) (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) :
    StabLawLt X E hfin ThR → Formalism.MainNotions.FormalGroupSystem.MinkowskiCounting D X (pendR X E hfin hst be ThR) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  intro hS
  classical
  let ThR' : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p] :=
    fun j La La' => if j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2 then ThR j La La' else 0
  have hS' : StabLaw X ℂ_[p] hfin ThR' := by
    intro j c L0 La' ε h0 hε
    by_cases hj : j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2
    · simp only [ThR', if_pos hj]
      exact hS j hj.1 c L0 La' ε h0 hj.2 hε
    · simp only [ThR', if_neg hj]
      unfold SA
      rw [← MvPowerSeries.coe_substAlgHom (hasSubst_actS X ℂ_[p] j _), map_zero, mul_zero]
  have hK := kapLaw_of_stabLaw X ℂ_[p] hfin ThR' pC_ne_zero hS'
  intro j hj c L La' γ G hGv hL hLa'
  have hEq : ∀ La, thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR') j La La' = thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j La La' := by
    intro La
    simp only [thFN, thGeo, ThR', if_pos (And.intro hj hLa')]
  have key : ∀ t : X.G.Kf,
      (eSX X j (c, (X.Lv.lev j c).smul γ L) * t) •
          delF X ℂ_[p] j ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G)
            (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, (X.Lv.lev j c).smul γ L) La') =
        (eSX X j (c, L) * t) • delF X ℂ_[p] j G (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, L) La') := by
    intro t
    have := ker_law X ℂ_[p] pC_ne_zero (delEquivOn_GdC X ℂ_[p]) _ hK j c L La' γ G hL (vtIn_GdC X ℂ_[p] j G hGv) t
    rwa [hEq, hEq] at this
  exact key _

end Law

end Formalism.L2.KerInert.AdmLoc2

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.AdmLoc2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)

/- English proof (translation)
Introduce `D p _ X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw h3b h4`. Take `⟨h5, hAt, hin, hW, hcc, hδ, hχ, hlam, hLam⟩` from `hC`. Take `⟨hA, hcl, hXa, hS, ρ, hLP, hMI, hFL⟩` from `hK`. Take `⟨h2, h2b, h3⟩` from `hK1 D p h5 X E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ hAt hin hW hcc hδ hχ hlam hLam hA hcl hXa hS hLP hMI hFL`. Use `⟨Formalism.MainNotions.FormalGroupSystem.Pf.positivity_condition_holds D, h2, h2b, ?_, h3, h3b, h4, ?_, ?_, Formalism.L2.G.Pend.up_down_adjoint D X _, Formalism.L2.PairingIndexBounds.Ent.pending_tuple_admissible X E hfin hst hLT pos _ D, Formalism.L2.KerInert.admissible_all_level …` and prove the remaining obligations.

Conclude with `Formalism.L2.KerInert.admissible_second_inert D cc δ p g hLT hAt h5 hin hW X _ rfl`. Conclude with `(invariance_iff_additive_maps_exist X E hfin hst hLT pos _ D).2 hXi`. Conclude with `admissible_stabilizer_of_law X E.toCEmb hfin hst (beLT hLT) D _ hLaw`. Conclude with `Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hin hW X _ rfl`.
-/
theorem admissible_general_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmGen2 := by
  intro D p _ X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw h3b h4
  obtain ⟨h5, hAt, hin, hW, hcc, hδ, hχ, hlam, hLam⟩ := hC
  obtain ⟨hA, hcl, hXa, hS, ρ, hLP, hMI, hFL⟩ := hK
  obtain ⟨h2, h2b, h3⟩ := hK1 D p h5 X E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ
    hAt hin hW hcc hδ hχ hlam hLam hA hcl hXa hS hLP hMI hFL
  refine ⟨Formalism.MainNotions.FormalGroupSystem.Pf.positivity_condition_holds D, h2, h2b, ?_, h3, h3b, h4, ?_, ?_, Formalism.L2.G.Pend.up_down_adjoint D X _,
    Formalism.L2.PairingIndexBounds.Ent.pending_tuple_admissible X E hfin hst hLT pos _ D, Formalism.L2.KerInert.admissible_all_levels D p X, ?_⟩
  · exact Formalism.L2.KerInert.admissible_second_inert D cc δ p g hLT hAt h5 hin hW X _ rfl
  · exact (invariance_iff_additive_maps_exist X E hfin hst hLT pos _ D).2 hXi
  · exact admissible_stabilizer_of_law X E.toCEmb hfin hst (beLT hLT) D _ hLaw
  · exact Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hin hW X _ rfl

section At

open Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelCoupled

/- English proof (translation)
Introduce `D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies`. Take `⟨ι, Rd, Sr, hE, hL⟩` from `hTies`. Establish `hmm : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm = D.R.m` using `KA.fl_m`. Use `admissible_general_of_kernel_law hK1 D _ (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst g hLT pos _ cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw (admissible_third_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om) ?_` and prove the remaining obligations. Distinguish the cases in `hm : 0 < D.R.m`.

Take `⟨lp, hTC, hH⟩` from `hL hm`. Conclude with `admissible_fourth_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hE (fun _ => ⟨hTC, hH⟩)`. Conclude with `⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩`.
-/
theorem admissible_place_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmAt2 := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos
    Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies
  obtain ⟨ι, Rd, Sr, hE, hL⟩ := hTies
  have hmm : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm = D.R.m := KA.fl_m
  refine admissible_general_of_kernel_law hK1 D _ (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst g hLT pos _ cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw
    (admissible_third_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om) ?_
  by_cases hm : 0 < D.R.m
  · obtain ⟨lp, hTC, hH⟩ := hL hm
    exact admissible_fourth_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hE (fun _ => ⟨hTC, hH⟩)
  · exact ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩

/- English proof (translation)
Introduce `D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies`. Take `⟨ι, Rd, Sr, hA⟩` from `hTies`. Establish `h5b` using `admissible_stabilizer_of_law (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E.toCEmb hfin hst (beLT hLT) D _ hLaw`. Use `admissible_place_of_kernel_law hK1 D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om E hfin hst g hLT pos Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw ⟨ι, Rd, Sr, fun j hj => hA j (by omega), fun hm => ?_⟩` and prove the remaining obligations. Take `⟨lp, hsec⟩` from `coupled_section_exists D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ hm`.

Establish `hT1` using `hA (D.R.m - 1) (by omega)`. Apply the tactic sequence `exact ⟨lp, coupled_compatibility_at_place D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hm hsec hT1, hecke_coupled_entry D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ lp hm h5b hsec hT1.2.1 …`.
-/
theorem admissible_entries_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmAtEnt2 := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos
    Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies
  obtain ⟨ι, Rd, Sr, hA⟩ := hTies
  have h5b := admissible_stabilizer_of_law (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E.toCEmb hfin hst (beLT hLT) D _ hLaw
  refine admissible_place_of_kernel_law hK1 D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om E hfin hst g hLT pos Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT
    hC hK hXi hLaw ⟨ι, Rd, Sr, fun j hj => hA j (by omega), fun hm => ?_⟩
  obtain ⟨lp, hsec⟩ := coupled_section_exists D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ hm
  have hT1 := hA (D.R.m - 1) (by omega)
  exact ⟨lp, coupled_compatibility_at_place D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hm hsec hT1,
    hecke_coupled_entry D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ lp hm h5b hsec hT1.2.1⟩

end At

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
The claim follows from `admissible_entries_of_kernel_law Formalism.L2.KerInert.KGLt.first_kernel_law_global_small`.
-/
theorem admissible_entries_small_chain : AdmAtEnt2 := admissible_entries_of_kernel_law Formalism.L2.KerInert.KGLt.first_kernel_law_global_small

end Formalism.L2.KerInert.AdmLoc2
