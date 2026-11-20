import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcCGNonneg

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem nc_notSg {T p : ℕ} (hg : GIdx D.host T p) : ¬ Formalism.MainNotions.G.IsSg D p := by
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  unfold Formalism.MainNotions.G.IsSg at h
  rw [h1] at h
  exact absurd h (by decide)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem nc_step {T p : ℕ} (hg : GIdx D.host T p) : Formalism.MainNotions.G.stepP D p = Formalism.MainNotions.G.hP D p := by
  unfold Formalism.MainNotions.G.stepP; rw [if_neg (nc_notSg hg)]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem nc_bs_iter (X : Formalism.MainNotions.G.Inst D L) (h t : Formalism.MainNotions.G.HH D) (i : ℕ) : X.bs h (t + i • h) = X.bs h t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem nc_bs_rep (X : Formalism.MainNotions.G.Inst D L) (h t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Finset.univ.image (X.bs h)) :
    X.bs h t0 = t0 := by
  obtain ⟨t1, _, rfl⟩ := Finset.mem_image.1 ht0
  obtain ⟨i, hi⟩ := X.bs_orb h t1
  have := nc_bs_iter X h (X.bs h t1) i
  rw [hi] at this
  exact this.symm

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem nc_partner {T p : ℕ} (hg : GIdx D.host T p) (t : Formalism.MainNotions.G.HH D) (e : ℕ) :
    Formalism.MainNotions.G.partner D p t e = (false, t + e • Formalism.MainNotions.G.hP D p) := by
  unfold Formalism.MainNotions.G.partner
  simp [nc_notSg hg]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem nc_tsum_odd (g : ℕ → ℝ) [DecidablePred (fun e : ℕ => Odd e)] :
    ∑' e : ℕ, (if Odd e then g e else 0) = ∑' e : ℕ, g (2 * e + 1) := by
  have hi : Function.Injective (fun e : ℕ => 2 * e + 1) := by
    intro a b h
    simp only at h
    omega
  have hs : Function.support (fun e : ℕ => if Odd e then g e else 0) ⊆ Set.range (fun e : ℕ => 2 * e + 1) := by
    intro e he
    by_cases ho : Odd e
    · obtain ⟨k, rfl⟩ := ho
      exact ⟨k, by ring⟩
    · exact (he (if_neg ho)).elim
  rw [← hi.tsum_eq hs]
  congr 1
  funext e
  exact if_pos (odd_two_mul_add_one e)

end Formalism.MainNotions.FormalGroupSystem.Pf
