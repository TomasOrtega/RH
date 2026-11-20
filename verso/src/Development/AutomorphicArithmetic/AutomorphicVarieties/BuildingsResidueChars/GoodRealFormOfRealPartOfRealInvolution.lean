import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Imports

open NumberField UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem UpperTheory.good_real_form_of_real_part_of_real_involution :
    UpperTheory.V.Af.BA.RePart → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.GoodRe := by
  intro hRP hRI L _ _ _ N σ hσ
  have G := UpperTheory.V.KT.good L N
  have hqc : ∀ (y : NZ L N) (k : HS L N), qc L N y k = q k (y : Lat L N) := fun y k => by
    simp [qc, ev_apply]
  have hpoly : ∀ h : HR L N, h ∈ ConeExtensionAcyclic.poly (qr L N) → (h : HS L N) ∈ ConeExtensionAcyclic.poly (qc L N) :=
    fun h hh y => by
      have := hh y
      rw [qr_apply] at this
      rw [hqc]
      exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨S, hS, hev⟩ := G.locFin _ (hpoly h hh)
    refine ⟨S, hS, ?_⟩
    have := (continuous_subtype_val.tendsto h).eventually hev
    filter_upwards [this] with h' hh' y hy
    rw [qr_apply, ← hqc]
    exact hh' y hy
  · obtain ⟨k, hk⟩ := G.nonempty
    obtain ⟨k', hk', -⟩ := hRP L N σ hσ k
    have hinv := (hRI L N σ hσ).1
    refine ⟨k', fun y => ?_⟩
    have hne : sLat σ (y : Lat L N) ≠ 0 := by
      intro h0
      apply y.2
      funext a
      have := congrFun h0 a
      simp only [sLat, Pi.zero_apply] at this
      show (y : Lat L N) a = 0
      rw [← hinv ((y : Lat L N) a), this, map_zero]
    have h1 := hk y
    have h2 := hk ⟨_, hne⟩
    rw [hqc] at h1 h2
    rw [qr_apply, hk']
    have h2' : 1 ≤ q k (sLat σ (y : Lat L N)) := h2
    linarith
  · exact G.closed.preimage continuous_subtype_val
  · intro c hc k hk
    exact G.smul_mem c hc _ hk
  · intro h hh
    exact G.sub (hpoly h hh)
  · obtain ⟨x, hx⟩ := G.pos
    refine ⟨x.comp (HR L N).subtypeL, fun k hk hk0 => ?_⟩
    exact hx _ hk (fun h => hk0 (Subtype.ext h))
