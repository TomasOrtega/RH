import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowClose

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

/- English proof (translation)
Proceed by induction on `P with`. Consider the case `nil => rfl`. Consider the case `cons p P ih`. Establish `hp : p.d = 1` using `h p (by simp)`. Establish `h1 : spehLoc N A p w = A.lpTw (A.locG p.π w) 0`.

Simplify using `[spehLoc, hp, A.lpSum_zero]`. Express the relevant statement in the definitionally equal form `A.lpSum (spehLoc N A p w) (isoLoc N A P w) = A.lpSum (A.lpTw (A.locG p.π w) 0) _`. Rewrite using `[h1, ih fun q hq => h q (by simp [hq])]`. Both sides reduce to the same expression.
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
Introduce `R H what₂ N A hR Pa Pa' h h' hw`. Establish `key` using `hR (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))) (Pa'.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))) (by`. Introduce `q hq`. Take `⟨p, hp, rfl⟩` from `List.mem_map.1 hq`. Conclude with `(h p hp).1)`.

Use the proof step `(by`. Introduce `q hq`. Take `⟨p, hp, rfl⟩` from `List.mem_map.1 hq`. Conclude with `(h' p hp).1)`. Use the proof step `(hw.mono fun w e => by`.

Rewrite using `[← isoLoc_eq_twSum_zero N A Pa (fun p hp => (h p hp).2), ← isoLoc_eq_twSum_zero N A Pa' (fun p hp => (h' p hp).2), e])`. Establish `back : ∀ P : List (Part A.CG), (∀ p ∈ P, p.d = 1) → (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))).map (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG)) = P`. Introduce `P hP`. Rewrite using `[List.map_map]`. Use `conv_rhs => rw [← List.map_id P]`.

Use `List.map_congr_left fun p hp => ?_` and prove the remaining obligations. Use `hP p hp` as an intermediate fact. Take `⟨a, π, d⟩` from `p`. Simplify using `only at this`. Substitute `this` using the available equality.

Both sides reduce to the same expression. Use `key.map (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG))` as an intermediate fact. Rewrite `this` using `[back Pa (fun p hp => (h p hp).2), back Pa' (fun p hp => (h' p hp).2)]`. Then use the resulting hypothesis.
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
