import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowClose

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem isoLoc_eq_twSum_zero (P : List (Part A.CG)) (h : ∀ p ∈ P, p.d = 1) (w : PlE H) :
    isoLoc N A P w =
      GlobalTheory.RowTie.twSum N A (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))) w := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    have hp : p.d = 1 := h p (by simp)
    have h1 : spehLoc N A p w = A.lpTw (A.locG p.π w) 0 := by
      simp [spehLoc, hp, A.lpSum_zero]
    change A.lpSum (spehLoc N A p w) (isoLoc N A P w) = A.lpSum (A.lpTw (A.locG p.π w) 0) _
    rw [h1, ih fun q hq => h q (by simp [hq])]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem isobaricCuspidalMultiplicityOne_of_twisted : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.IsobaricRigid N A → GlobalTheory.RowCopy.IsobaricCuspidalStrongMultiplicityOne N A := by
  intro R H what₂ N A hR Pa Pa' h h' hw
  have key := hR (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ)))
    (Pa'.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ)))
    (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (h p hp).1)
    (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (h' p hp).1)
    (hw.mono fun w e => by
      rw [← isoLoc_eq_twSum_zero N A Pa (fun p hp => (h p hp).2),
        ← isoLoc_eq_twSum_zero N A Pa' (fun p hp => (h' p hp).2), e])
  have back : ∀ P : List (Part A.CG), (∀ p ∈ P, p.d = 1) →
      (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))).map
        (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG)) = P := by
    intro P hP
    rw [List.map_map]
    conv_rhs => rw [← List.map_id P]
    refine List.map_congr_left fun p hp => ?_
    have := hP p hp
    obtain ⟨a, π, d⟩ := p
    simp only at this
    subst this
    rfl
  have := key.map (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG))
  rwa [back Pa (fun p hp => (h p hp).2), back Pa' (fun p hp => (h' p hp).2)] at this

end GlobalTheory.RowClose
