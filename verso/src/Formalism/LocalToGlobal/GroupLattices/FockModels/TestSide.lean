import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSidePos

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

section Scale
variable {O Kf X Y : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X] [AddCommGroup Y] [Module Kf Y] [Module O Y] [IsScalarTower O Kf Y]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem scale_map (a : Kf) (A : Submodule O X) (Ψ : X →ₗ[Kf] Y) :
    (scale a A).map (Ψ.restrictScalars O) = scale a (A.map (Ψ.restrictScalars O)) := by
  unfold scale
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem scale_mono (a : Kf) {A B : Submodule O X} (h : A ≤ B) : scale a A ≤ scale a B := by
  unfold scale
  exact Submodule.map_mono h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem scale_comm (a b : Kf) (A : Submodule O X) : scale a (scale b A) = scale b (scale a A) := by
  unfold scale
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp [smul_smul, mul_comm]

end Scale

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem testSide_of_core (hC : FormCore) : TestSide := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r lam0 hd
  refine ⟨fun e he => dual_edge h m r e he, ?_⟩
  have := h.frac_O
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hanti := kp_lamAt_antitone lam0 hd
  have hpos : ∀ s : Fin n', ∃ β, PosCore O Kf p m (lamAt lam0 s) (expN p m (lamAt lam0 s)) β := by
    intro s
    obtain ⟨B, ha, hb, hc, hdd⟩ := hC p n' W Qq O Kf ι σ j w h m (lamAt lam0 s) (hanti s)
    exact posCore_of_form hinj p m (lamAt lam0 s) _ B ha hb hc hdd
  choose β hβ using hpos
  have hV : Vsp Kf lam0 = tensorLat Kf Kf
      (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := by
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (hanti s)]
  obtain ⟨Ψ, hΨ⟩ := ten_side O Kf p lam0 hd (fun s => expN p m (lamAt lam0 s)) β hβ (Vsp Kf lam0) hV
  have hκ : (p : Kf) ^ ((kap1 p lam0 : ℕ) : ℤ) = (p : Kf) ^ (∑ s, expN p m (lamAt lam0 s)) := by
    rw [zpow_natCast]
    rfl
  rw [hκ]
  refine ⟨Ψ, ?_, ?_⟩
  · intro L hL
    obtain ⟨g, hg, rfl⟩ := hL
    have h1 := hΨ (fun s => la_tw ι σ s.val g) (fun s => la_tw_det _ _ _ g hg)
    have e1 : HL (O := O) ι σ lam0 (colSpan W g) =
        (Hten O lam0 fun s => colSpan O (la_tw ι σ s.val g)).comap ((Vsp Kf lam0).subtype.restrictScalars O) := by
      unfold HL toV
      simp only [extO_colSpan h]
    have e2 : HL (O := O) ι σ lam0 (latDual (colSpan W g)) =
        (Hten O lam0 fun s => colSpan O ((la_tw ι σ s.val g)⁻¹).transpose).comap
          ((Vsp Kf lam0).subtype.restrictScalars O) := by
      unfold HL toV
      rw [latDual_colSpan g hg]
      simp only [extO_colSpan h, tw_invT ι σ _ g hg]
    rw [e1, e2]
    exact h1
  · intro e he
    obtain ⟨g, hgb⟩ := edgeBasis h m r e he
    have hg := hgb.1
    have hw := w_ne h
    have hp := p_eq h
    set c : Kf := algebraMap O Kf w with hc
    have hN : ∀ s : Fin n', IsUnit (la_tw ι σ s.val g * lb_D (m + 1) r c).det := by
      intro s
      rw [Matrix.det_mul]
      exact (la_tw_det _ _ _ g hg).mul (lb_D_det _ _ _ hw)
    have h1 := hΨ (fun s => la_tw ι σ s.val g * lb_D (m + 1) r c) hN
    have e1 : HLe (O := O) p ι σ w lam0 e =
        (Hten O lam0 fun s => colSpan O (la_tw ι σ s.val g * lb_D (m + 1) r c)).comap
          ((Vsp Kf lam0).subtype.restrictScalars O) := by
      unfold HLe toV
      simp only [leAt_of_basis h m r e g hgb, ← hc]
    have e2 : HLe (O := O) p ι σ w lam0 e.dual =
        (Hten O lam0 fun s => colSpan O ((la_tw ι σ s.val g * lb_D (m + 1) r c)⁻¹).transpose).comap
          ((Vsp Kf lam0).subtype.restrictScalars O) := by
      unfold HLe toV
      simp only [leAt_of_basis h m r e.dual _ (dual_edgeBasis p r (pQ_ne h) e g hgb), tw_mul, tw_invT ι σ _ g hg,
        tw_dE, invT_mul_D _ (la_tw_det ι σ _ g hg) r c hw, Matrix.mul_assoc, hp, ← hc, dE_sq_D r c hw]
    unfold Re Re'
    rw [e1, e2, scale_map, scale_comm]
    exact ⟨scale_mono _ h1.1, scale_mono _ h1.2⟩

end Formalism.L2.G.Model
