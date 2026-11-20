import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ProdRootsOfMonic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContMapRepIotaOQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterIndependentOfLocalEmbeddingStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigConcrete

/- English proof (translation)
Introduce `i a r w hl _`. Rewrite using `[(P.wdOf i a r w).1]`. Conclude with `P.wd.away _ _ r w hl`.
-/
theorem wdOfTie {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D) : WDOfTie P.T := by
  intro i a r w hl _
  rw [(P.wdOf i a r w).1]
  exact P.wd.away _ _ r w hl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hd' : P.wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w` using `(P.wdOf i b r w).2.2.2.1.1 hd`. Establish `pst : ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O] (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F` using `D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → IsPstAt (D.loc (D.nd.l i)) Bw (resDec D.nd.plOm.1 r w) := by`. Introduce `O _ _ _ Bw hj`. Conclude with `hB.isPstAt (D.locT (D.nd.l i)) Bw _ (hr.comp continuous_subtype_val) ((GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) w hw O Bw hj b r hr).1 hd')`. Use `⟨pst _ (D.nbr i w hw) (D.nbr_ind i w hw), ?_⟩` and prove the remaining obligations.

Take `⟨L1, B1, j1, e1⟩` from `P.wd.above (D.nd.l i) (D.naut.iotaQC i) r w hw`. Rewrite using `[(P.wdOf i b r w).1, e1]`. Conclude with `GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w) _ (D.nd.O i) B1 (D.nbr i w hw) j1 (D.nbr_ind i w hw) b _ (hr.comp continuous_subtype_val) (p …`.
-/
theorem e_wdOf_above (hB : GlobalTheory.Published.DeRhamPotSemistable) {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D)
    (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {b : ℕ}
    (r : G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i)))
    (hr : Continuous (fun g => ((r g : GL (Fin b) (Qbar (D.nd.l i))) : Matrix (Fin b) (Fin b) (Qbar (D.nd.l i)))))
    (hd : D.naut.IsdRW i r w) :
    IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (resDec D.nd.plOm.1 r w) ∧
    P.T.e w (D.naut.wdOf i r w) = wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w)
      (D.nbr_ind i w hw) (resDec D.nd.plOm.1 r w) := by
  have hd' : P.wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w := (P.wdOf i b r w).2.2.2.1.1 hd
  have pst : ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
      (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw →
      IsPstAt (D.loc (D.nd.l i)) Bw (resDec D.nd.plOm.1 r w) := by
    intro O _ _ _ Bw hj
    exact hB.isPstAt (D.locT (D.nd.l i)) Bw _ (hr.comp continuous_subtype_val)
      ((GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) w hw O Bw hj b r hr).1 hd')
  refine ⟨pst _ (D.nbr i w hw) (D.nbr_ind i w hw), ?_⟩
  obtain ⟨L1, B1, j1, e1⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) r w hw
  rw [(P.wdOf i b r w).1, e1]
  exact GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ (D.naut.iotaQC i)
    D.host.E D.nd.Om _ w (D.nd.plOm.2 w) _ (D.nd.O i) B1 (D.nbr i w hw) j1 (D.nbr_ind i w hw) b _
    (hr.comp continuous_subtype_val) (pst _ B1 j1) (pst _ (D.nbr i w hw) (D.nbr_ind i w hw))

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hB hL D P`. Use `⟨eigAway_of_wdOfTie _ _ _ D.nd D.naut P.T (wdOfTie P), ?_⟩` and prove the remaining obligations. Introduce `i a ρ χ hρ hχ w hw dρ dχ hs σ hσ`. Take `⟨p1, e1⟩` from `e_wdOf_above hB P i w hw (mapRep (iotaOQ D.nd D.naut i) ρ) (GlobalTheory.LocalInv.cont_mapRep_iotaOQ D.nd D.naut i ρ hρ) dρ`. Take `⟨p2, e2⟩` from `e_wdOf_above hB P i w hw (mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.LocalInv.charRep D.nd i χ)) (GlobalTheory.LocalInv.cont_mapRep_iotaOQ D.nd D.naut i _ hχ) dχ`.

Establish `hW` using `mem_Weil_of_isFrob (D.nd.plOm.2 w) hσ`. Use `show ((P.T.e w (GlobalTheory.LocalInv.wd D.nd D.naut i (GlobalTheory.LocalInv.charRep D.nd i χ) w)).inePol σ).roots ≤ ((P.T.e w (GlobalTheory.LocalInv.wd D.nd D.naut i ρ w)).inePol σ).roots`. Rewrite using `[GlobalTheory.LocalInv.wd, GlobalTheory.LocalInv.wd, e1, e2, WD.inePol_of_mem _ hW, WD.inePol_of_mem _ hW]`. Take `⟨v, hv, hs⟩` from `hs`. Establish `hv0 : (D.naut.iotaQ i) ∘ v ≠ 0`.

Introduce `h0`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Use `congrFun h0 k` as an intermediate fact. Simplify using `using this`.

Establish `hM : ∀ g : ↥(Dec (F` using `D.host.E) (D.nd.plOm.1 w)), ((resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) ρ) w g : GL (Fin a) (Om (D.nd.l i))) : Matrix (Fin a) (Fin a) (Om (D.nd.l i))) = (GlobalTheory.LocalInv.matK D.nd i ρ g).map (D.naut.iotaQ i) := by`. Introduce `g`. Use extensionality with `p q`. Both sides reduce to the same expression. Establish `hC : ∀ g : ↥(Dec (F` using `D.host.E) (D.nd.plOm.1 w)), ((resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.LocalInv.charRep D.nd i χ)) w g : GL (Fin 1) (Om (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Om (D.nd.l i))) 0 0 = D.naut.iotaQ i (algebraMap (D.nd.O i) (Kf D.nd i) ((χ g : (D.nd.O i)ˣ) : D.n …`.

Introduce `g`. Both sides reduce to the same expression. Break down `hs with hs | hs` into its components or cases. Use `GlobalTheory.T.local_galois_rep_decomposition_induced (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ _ p1 p2 ((D.naut.iotaQ i) ∘ v) hv0 (fun g => ?_) ⟨σ, hW⟩` and prove the remaining obligations. Rewrite using `[hM, hC]`.

Use function extensionality and compare the values at `k`. Rewrite using `[← RingHom.map_mulVec, hs g g.2]`. Simplify using the standard rewrite rules. Use `GlobalTheory.T.local_galois_rep_induced_matches (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ _ p1 p2 ((D.naut.iotaQ i) ∘ v) hv0 (fun g => ?_) ⟨σ, hW⟩` and prove the remaining obligations. Rewrite using `[hM, hC]`.

Use function extensionality and compare the values at `k`. Rewrite using `[← RingHom.map_vecMul, hs g g.2]`. Simplify using the standard rewrite rules.
-/
theorem main : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D),
    GlobalTheory.LocalInv.EigAway D.nd D.naut P.T.eig ∧ GlobalTheory.LocalInv.EigAbove D.nd D.naut P.T.eig := by
  intro hB hL D P
  refine ⟨eigAway_of_wdOfTie _ _ _ D.nd D.naut P.T (wdOfTie P), ?_⟩
  intro i a ρ χ hρ hχ w hw dρ dχ hs σ hσ
  obtain ⟨p1, e1⟩ := e_wdOf_above hB P i w hw (mapRep (iotaOQ D.nd D.naut i) ρ)
    (GlobalTheory.LocalInv.cont_mapRep_iotaOQ D.nd D.naut i ρ hρ) dρ
  obtain ⟨p2, e2⟩ := e_wdOf_above hB P i w hw (mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.LocalInv.charRep D.nd i χ))
    (GlobalTheory.LocalInv.cont_mapRep_iotaOQ D.nd D.naut i _ hχ) dχ
  have hW := mem_Weil_of_isFrob (D.nd.plOm.2 w) hσ
  show ((P.T.e w (GlobalTheory.LocalInv.wd D.nd D.naut i (GlobalTheory.LocalInv.charRep D.nd i χ) w)).inePol σ).roots ≤
    ((P.T.e w (GlobalTheory.LocalInv.wd D.nd D.naut i ρ w)).inePol σ).roots
  rw [GlobalTheory.LocalInv.wd, GlobalTheory.LocalInv.wd, e1, e2, WD.inePol_of_mem _ hW, WD.inePol_of_mem _ hW]
  obtain ⟨v, hv, hs⟩ := hs
  have hv0 : (D.naut.iotaQ i) ∘ v ≠ 0 := by
    intro h0
    apply hv
    funext k
    have := congrFun h0 k
    simpa using this
  have hM : ∀ g : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)),
      ((resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) ρ) w g : GL (Fin a) (Om (D.nd.l i))) :
        Matrix (Fin a) (Fin a) (Om (D.nd.l i))) = (GlobalTheory.LocalInv.matK D.nd i ρ g).map (D.naut.iotaQ i) := by
    intro g
    ext p q
    rfl
  have hC : ∀ g : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)),
      ((resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.LocalInv.charRep D.nd i χ)) w g :
        GL (Fin 1) (Om (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Om (D.nd.l i))) 0 0 =
        D.naut.iotaQ i (algebraMap (D.nd.O i) (Kf D.nd i) ((χ g : (D.nd.O i)ˣ) : D.nd.O i)) := by
    intro g
    rfl
  rcases hs with hs | hs
  · refine GlobalTheory.T.local_galois_rep_decomposition_induced (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ _ p1 p2
      ((D.naut.iotaQ i) ∘ v) hv0 (fun g => ?_) ⟨σ, hW⟩
    rw [hM, hC]
    funext k
    rw [← RingHom.map_mulVec, hs g g.2]
    simp
  · refine GlobalTheory.T.local_galois_rep_induced_matches (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ (D.naut.iotaQC i) (D.nbr i w hw)
      (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ _ p1 p2 ((D.naut.iotaQ i) ∘ v) hv0 (fun g => ?_) ⟨σ, hW⟩
    rw [hM, hC]
    funext k
    rw [← RingHom.map_vecMul, hs g g.2]
    simp

end GlobalTheory.EigConcrete

end
