import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.SubstInvFActS

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

def RepresentativeCondition (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  ∀ j < X.mm, ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ExtensionGeneratorCondition p ℂ_[p] (OcC p) be (thA ℂ_[p] φ (thFOf X pos F j L0 La'))

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Simplify by unfolding definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify by unfolding definitions. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem adm_two_pendant_iff_representative (D : Formalism.BasicNotions.D7) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    adm2b D X (pendT X E hfin hst hLT pos F) ↔ RepresentativeCondition X E hfin (beLT hLT) pos F := by
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  rw [adm_two_pendant_iff]
  constructor
  · intro H
    dsimp only [RepresentativeCondition]
    intro j hj R hR La' hLa' φ
    have hlat : (X.Pj j).IsLatTup R.2 := repOf_lat (Lv := X.Lv) hfin j R hR
    have key := H j hj R La' hlat hLa'
    obtain ⟨L1, hL1, hL1'⟩ := delt_spec (X := X) (hfin := hfin) j R.1 R.2 hlat
    set δ := delt X hfin j R.1 R.2 with hδ
    obtain ⟨L2, _, huniq⟩ := repOf_ex (Lv := X.Lv) hfin j R.1 R.2 hlat
    have e1 : R.2 = L2 := huniq R.2 ⟨hR, 1, by rw [lsmul_one]⟩
    have e2 : L1 = L2 := huniq L1 ⟨hL1, δ, hL1'⟩
    have hS : (X.Lv.lev j R.1).smul δ⁻¹ R.2 = R.2 := by
      conv_lhs => rw [hL1']
      rw [lsmul_inv_lsmul, e2, e1]
    have hh : R.2 = (X.Lv.lev j R.1).smul δ ((X.Lv.lev j R.1).smul δ⁻¹ R.2) := by
      rw [lsmul_lsmul_inv]
    have key2 : ∀ ψ : Frm X j (R.1, (X.Lv.lev j R.1).smul δ⁻¹ R.2) La', ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT)
        (thA ℂ_[p] ψ (thFOf X pos F j (R.1, (X.Lv.lev j R.1).smul δ⁻¹ R.2) La')) := by
      intro ψ
      have h := key (frmBack X δ hh ψ)
      rw [thA_SA X ℂ_[p] δ hh] at h
      have hr : frmMove X δ hh (frmBack X δ hh ψ) = ψ := by
        cases ψ
        simp only [frmMove, frmBack, inv_mul_cancel_left]
      rw [hr] at h
      exact h
    rw [hS] at key2
    exact key2 φ
  · intro H j hj La La' hLa hLa' φ
    dsimp only [RepresentativeCondition] at H
    obtain ⟨L1, hL1, hL1'⟩ := delt_spec (X := X) (hfin := hfin) j La.1 La.2 hLa
    set δ := delt X hfin j La.1 La.2 with hδ
    have hS : (X.Lv.lev j La.1).smul δ⁻¹ La.2 = L1 := by
      conv_lhs => rw [hL1']
      rw [lsmul_inv_lsmul]
    have hh : La.2 = (X.Lv.lev j La.1).smul δ ((X.Lv.lev j La.1).smul δ⁻¹ La.2) := by
      rw [lsmul_lsmul_inv]
    rw [thA_SA X ℂ_[p] δ hh φ]
    have hrep : (La.1, (X.Lv.lev j La.1).smul δ⁻¹ La.2) ∈ repOf X.Lv hfin j := by
      rw [hS]
      exact hL1
    exact H j hj _ hrep La' hLa' (frmMove X δ hh φ)

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
