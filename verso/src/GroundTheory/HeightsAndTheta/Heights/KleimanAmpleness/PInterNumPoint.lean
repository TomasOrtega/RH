import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.InterNumPointSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section InterNumPointLemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem interNumPoint_restrLen_eq_finrank (y : Fin (N + 1) → Ω) {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (F : SubSystem k y Ω) : restrLen (primeOf (S := k) y) F = Module.finrank k F.secs := by
  have hid : ∀ I : Chart y, idealMod (x := y) (primeOf (S := k) y) I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
    rw [(mem_primeOf_of_isHomogeneous y hfe).mp hf, zero_div]
  have hbot : ∀ I : Chart y, (F.twist (idealSys y (primeOf (S := k) y))).sub I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨q, hq, z, _, rfl⟩
    have hq' : q ∈ idealMod (x := y) (primeOf (S := k) y) I := hq
    rw [hid I, Submodule.mem_bot] at hq'
    rw [hq', zero_smul]
  have hsecs : (F.twist (idealSys y (primeOf (S := k) y))).secs = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have h1 := (Submodule.mem_iInf _).mp hz (singleChart hyj)
    rw [Submodule.restrictScalars_mem, hbot] at h1
    exact h1
  unfold restrLen
  rw [hsecs, Submodule.comap_bot, Submodule.ker_subtype,
    (Submodule.quotEquivOfEqBot (⊥ : Submodule k F.secs) rfl).length_eq, Module.length_eq_rank]
  rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem interNumPoint_interSum_eq (y : Fin (N + 1) → Ω) {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (L : Fin 0 → SubSystem k y Ω) (c : ℕ) :
    interSum (primeOf (S := k) y) L c = Module.finrank k (twistSys k y (c : ℤ)).secs := by
  have huniv : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by decide
  have h0 : tensorSub L ∅ = twistSys k y 0 := rfl
  rw [interSum, huniv, Finset.sum_singleton, h0, twistSys_zero_twist,
    interNumPoint_restrLen_eq_finrank y hyj]
  simp

end InterNumPointLemmas

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem InterNumPoint.proof (hHP : HilbertPoint.Statement.{u, w}) : InterNumPoint.Statement.{u, w} := by
  intro k _ Ω _ _ N y hsub L
  obtain ⟨_, hdim, hsecs⟩ := hHP k Ω N y hsub
  obtain ⟨j, hj⟩ := hsub.relevant
  have hyj : y j ≠ 0 := by
    intro h
    apply hj
    rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j), aeval_X]
    exact h
  have hev : (fun _ : ℕ => (Module.finrank k (funField (k := k) y) : ℤ)) =ᶠ[atTop]
      interSum (primeOf (S := k) y) L := by
    filter_upwards [hdim, hsecs] with n hn hs
    rw [interNumPoint_interSum_eq y hyj, hs, hn]
  exact (tendsto_const_nhds.congr' hev).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman
