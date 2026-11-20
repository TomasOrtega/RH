import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LiftBoundOfIntegrality
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FormValuationGeNegDegree
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HeckeValueEstimateOfRecordValue
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StabilizerCount
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RestrictedHeckeIntegralOfEdges
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TsumRatTail
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HeckeConditionOfAdm
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulPsiGUp
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PositivityConditionHolds
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CommonEigenvectorThird
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RestEntOf
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FirstTheoremPlaceBound
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EbBrJet

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem linD (X : Sys p) : LinD X where
  Tt_add v i j F F' := by
    have := (TtLin X v i j).map_add F F'
    simp only [TtLin_apply] at this
    exact this
  Tt_smul v i j a F := by
    have := (TtLin X v i j).map_smul a F
    simp only [TtLin_apply] at this
    exact this
  yv_add v F F' := (yvLin X v).map_add F F'
  yv_smul v a F := (yvLin X v).map_smul a F
  yv_comm v v' F := funext fun i => Formalism.MainNotions.G.LatticeSystems.ef_yv_comm X.G.P v v' (F i)

variable {X : Sys p}

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify to obtain the desired conclusion from the available facts.
-/
theorem vGe_of_eO_zero (he : X.eO = 0) {j : ℕ} {F : X.Fm j} {g g' : ℝ} (h : X.vGe j F g) : X.vGe j F g' := by
  unfold Sys.vGe Sys.vsc at h ⊢
  simpa [he] using h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.

Substitute using the available equality. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem low_term_bound_of_eO_eq_zero_of_aux0 (D : Formalism.BasicNotions.D7) (Y : Pend X) (he : X.eO = 0) (h0 : Conclusion0 D X) : LowTermBound D X Y := by
  intro Gn G0n PRn S VV _ _ _ _ F hFm
  have hPl : ∀ _ : X.Pl, False := fun v => by have := eO_pos X v; omega
  have hFint : F ∈ X.Int 0 := by
    unfold Sys.Iprod at hFm
    refine (Submodule.span_le.2 ?_) hFm
    rintro F' ⟨BB, _, Lv, _, _, F0, hF0, rfl⟩
    have hLv : Lv = [] := by
      cases Lv with
      | nil => rfl
      | cons v _ => exact (hPl v).elim
    subst hLv
    have h1 : F0 ∈ scale (1 : X.G.Kf) (X.Int 0) := by simpa [he] using hF0
    rw [scale_one] at h1
    exact h1
  have key : ∀ m' ≤ X.mm, X.chainK m' F ∈ X.Int m' := by
    intro m'
    induction m' with
    | zero => intro _; exact hFint
    | succ n ih =>
      intro h
      have := h0 n (by omega) _ (ih (by omega))
      exact (vGe_zero_iff X).1 (vGe_of_eO_zero he this)
  exact vGe_of_eO_zero he ((vGe_zero_iff X).2 (key X.mm le_rfl))

structure Rests (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) : Prop where

  S1 : Conclusion1 D X Y

  allPlacesExpansion : ExpansionsMultiply D X Y

  U2 : VolumeRatio₂ D X Y

  Ent : EntCondition X Y

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem prv_and_kernel_commutation_up_to_units_of_rests (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) (R : Rests D X Y) :
    Conclusion₂ D X Y ∧ KernelCommutationUpToUnits D X := by
  have hF : FormB X Y := formB D X Y hA
  have hH : RestHecke X := heckeCondition_of_adm D X Y hA countLoc (restTmFQ X)
  obtain ⟨_, _, _, _, h3, h3b, _, _, _, _, _, h8, _⟩ := hA
  have p2b := hecke_integral_of_forms D hF R.Ent R.U2
  have p3 := latticeChain_succ_of_partial D hF R.Ent R.U2 (restricted_hecke_integral X)
  have pAlt := alternate_expansion_of_relations X D hH (restTmFQ X) h3b p3 p2b
  have p4 := theorem_of_alternate_form X D pAlt
  have p5D : LowTermBound D X Y := by
    rcases Nat.eq_zero_or_pos X.eO with he | he
    · exact low_term_bound_of_eO_eq_zero_of_aux0 D Y he (form_valuation_of_bound D hF h3)
    · exact lift_bound_of_integrality D (isFractionRing_of_pos_eO Y he) (pKf_ne Y) (linD X) hF R.Ent p4
        (fun v F hFm => h8.2 v F hFm)
  exact ⟨⟨form_valuation_of_bound D hF h3, R.S1, R.allPlacesExpansion, slopeEstimate_of_lemmaB_slopeLine D hF R.Ent R.U2, theorem_A_entries_of_corollary D R.Ent (restRat X) R.U2, R.U2, p2b, p3, p4,
    ramifiedLattice_of_chain_estimates D R.U2 p5D, p5D⟩, pAlt⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rests (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) : Rests D X Y where
  S1 := theta_kernel_expansion D X Y hA
  allPlacesExpansion := expansions_multiply D X Y hA
  U2 := auxU_of_firstTheoremPlaceBound D (first_theorem_place_bound X Y D (restGc p) (eb_brJet X)) hA
  Ent := restEnt_of X Y D (second_lemma_place_bound X Y D (restGc p) (eb_brJet X))
    (hecke_place_bound X Y D (restGc p) (eb_brJet X)) hA

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem packet_statements_hold (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) : Conclusion₂ D X Y :=
  (prv_and_kernel_commutation_up_to_units_of_rests D Y hA (rests D Y hA)).1

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem stmt_proved (D : Formalism.BasicNotions.D7) : Stmt D :=
  ⟨fun _ _ _ Y hA => packet_statements_hold D Y hA, relative_presentation_of_d7 D⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem stmtAt_proved (D : Formalism.BasicNotions.D7) : ErrorExponentStatement D :=
  fun _ _ _ _ _ Y _ hA => packet_statements_hold D Y hA

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem stmtF_proved {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : KudlaFamilyStatement Fm := fun x i => stmt_proved (Fm.D x i)

end Formalism.MainNotions.FormalGroupSystem.Pf
