import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FinalG

open Matrix
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace PI.UnitaryGroupMassFormula.QnFFZero

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Simplify using `only [Glev, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h.1`. Introduce `h`.

Conclude with `⟨h, fun a ha => absurd ha (by simp)⟩`.
-/
theorem glev_zero (k r : ℕ) (g : Mx k r) : g ∈ Glev k r 0 ↔ g ∈ UH (Hpk k r) := by
  simp only [Glev, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, fun a ha => absurd ha (by simp)⟩

/- English proof (translation)
Simplify using `only [Nset, Set.mem_ofPred_eq] at h`. Conclude with `h.1`.
-/
theorem nset_uh (k r : ℕ) (n : Mx k r) (h : n ∈ Nset k r) : n ∈ UH (Hpk k r) := by
  simp only [Nset, Set.mem_ofPred_eq] at h
  exact h.1

/- English proof (translation)
Simplify using `only [Nlev, Set.mem_inter_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h.1`. Introduce `h`.

Conclude with `⟨h, (glev_zero k r n).2 (nset_uh k r n h)⟩`.
-/
theorem nlev_zero (k r : ℕ) (n : Mx k r) : n ∈ Nlev k r 0 ↔ n ∈ Nset k r := by
  simp only [Nlev, Set.mem_inter_iff]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, (glev_zero k r n).2 (nset_uh k r n h)⟩

/- English proof (translation)
Unfold `ell`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Use `split_ifs with h`. Apply `Matrix.one_apply_ne` to reduce the goal to its premises.

Introduce `he`. Simplify using `[eI, Fin.ext_iff] at he`. Rewrite using `[Matrix.one_mulVec]`. Conclude with `hz _ (Or.inl (by simp [eI]))`.
-/
theorem ell_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : ell k r z 1 = 0 := by
  unfold ell
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · apply Matrix.one_apply_ne
    intro he
    simp [eI, Fin.ext_iff] at he
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl (by simp [eI]))

/- English proof (translation)
Simplify using `[psi, ell_one k r z hz]`.
-/
theorem psi_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z) : psi k r z c 1 = 1 := by
  simp [psi, ell_one k r z hz]

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ k r z z' π π' hz hz'`. Establish `hdet : IsUnit (Hpk k r).det` using `Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1`. Establish `hmul : ∀ g ∈ UH (Hpk k r), ∀ h ∈ UH (Hpk k r), g * h ∈ UH (Hpk k r)` using `(uHGroup (2 * r + k + 1) (Hpk k r) hdet).2.1`. Establish `hN1 : (1 : Mx k r) ∈ Nset k r` using `(nSubgroup k r).1`. Use extensionality with `J`.

Simplify using `only [FFl, EqF, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hS, hL, hR, hW⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g₀ hg₀`.

Take `⟨U, F, hU, hgU, hF, hE⟩` from `hS g₀ (Set.mem_inter ((glev_zero k r g₀).2 hg₀) (Set.mem_univ _))`. Conclude with `⟨U, F, hU, hgU, hF, fun g hg hgH => hE g hg ((glev_zero k r g).2 hgH)⟩`. Introduce `g hg n hn n' hn'`. Establish `hng : n * g ∈ UH (Hpk k r)` using `hmul n (nset_uh k r n hn) g hg`. Rewrite using `[hR (n * g) (Set.mem_inter ((glev_zero k r _).2 hng) (Set.mem_univ _)) n' ((nlev_zero k r n').2 hn'), hL g (Set.mem_inter ((glev_zero k r g).2 hg) (Set.mem_univ _)) n ((nlev_zero k r n).2 hn), smul_smul, mul_comm]`.

Introduce `g hg h hh h' hh'`. Conclude with `hW g (Set.mem_inter ((glev_zero k r g).2 hg) (Set.mem_univ _)) h hh h' hh'`. Introduce and unpack `⟨hS, hNN, hW⟩`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g₀ hg₀`.

Take `⟨U, F, hU, hgU, hF, hE⟩` from `hS g₀ ((glev_zero k r g₀).1 hg₀.1)`. Conclude with `⟨U, F, hU, hgU, hF, fun g hg hgG => hE g hg ((glev_zero k r g).1 hgG)⟩`. Introduce `g hg n hn`. Establish `h1` using `hNN g ((glev_zero k r g).1 hg.1) n ((nlev_zero k r n).1 hn) 1 hN1`. Rewrite `h1` using `[mul_one, psi_one k r z' cStd hz', mul_one]`.

Conclude with `h1`. Introduce `g hg n hn`. Establish `h1` using `hNN g ((glev_zero k r g).1 hg.1) 1 hN1 n ((nlev_zero k r n).1 hn)`. Rewrite `h1` using `[one_mul, psi_one k r z cStd hz, one_mul]`. Conclude with `h1`.

Introduce `g hg h hh h' hh'`. Conclude with `hW g ((glev_zero k r g).1 hg.1) h hh h' hh'`.
-/
theorem ffZero : FFZero := by
  intro Wp Wq _ _ _ _ k r z z' π π' hz hz'
  have hdet : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hmul : ∀ g ∈ UH (Hpk k r), ∀ h ∈ UH (Hpk k r), g * h ∈ UH (Hpk k r) :=
    (uHGroup (2 * r + k + 1) (Hpk k r) hdet).2.1
  have hN1 : (1 : Mx k r) ∈ Nset k r := (nSubgroup k r).1
  ext J
  simp only [FFl, EqF, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hS, hL, hR, hW⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g₀ hg₀
      obtain ⟨U, F, hU, hgU, hF, hE⟩ := hS g₀ (Set.mem_inter ((glev_zero k r g₀).2 hg₀) (Set.mem_univ _))
      exact ⟨U, F, hU, hgU, hF, fun g hg hgH => hE g hg ((glev_zero k r g).2 hgH)⟩
    · intro g hg n hn n' hn'
      have hng : n * g ∈ UH (Hpk k r) := hmul n (nset_uh k r n hn) g hg
      rw [hR (n * g) (Set.mem_inter ((glev_zero k r _).2 hng) (Set.mem_univ _)) n' ((nlev_zero k r n').2 hn'),
        hL g (Set.mem_inter ((glev_zero k r g).2 hg) (Set.mem_univ _)) n ((nlev_zero k r n).2 hn),
        smul_smul, mul_comm]
    · intro g hg h hh h' hh'
      exact hW g (Set.mem_inter ((glev_zero k r g).2 hg) (Set.mem_univ _)) h hh h' hh'
  · rintro ⟨hS, hNN, hW⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g₀ hg₀
      obtain ⟨U, F, hU, hgU, hF, hE⟩ := hS g₀ ((glev_zero k r g₀).1 hg₀.1)
      exact ⟨U, F, hU, hgU, hF, fun g hg hgG => hE g hg ((glev_zero k r g).1 hgG)⟩
    · intro g hg n hn
      have h1 := hNN g ((glev_zero k r g).1 hg.1) n ((nlev_zero k r n).1 hn) 1 hN1
      rw [mul_one, psi_one k r z' cStd hz', mul_one] at h1
      exact h1
    · intro g hg n hn
      have h1 := hNN g ((glev_zero k r g).1 hg.1) 1 hN1 n ((nlev_zero k r n).1 hn)
      rw [one_mul, psi_one k r z cStd hz, one_mul] at h1
      exact h1
    · intro g hg h hh h' hh'
      exact hW g ((glev_zero k r g).1 hg.1) h hh h' hh'

end PI.UnitaryGroupMassFormula.QnFFZero
