import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp)
open Module

namespace GlobalTheory.Cusp.WittIdx

section Lin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Formalism.BasicNotions.HSpace E}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_perp' {W : Submodule E V.V} {y : V.V} : y ∈ perp V W ↔ ∀ x ∈ W, V.hT x y = 0 := by
  simp only [perp, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem perp_eq_ker_pi_hT_finBasis (A : Submodule E V.V) :
    perp V A = LinearMap.ker (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V)) := by
  ext y
  rw [mem_perp', LinearMap.mem_ker]
  constructor
  · intro h
    funext k
    simpa using h _ (Module.finBasis E A k).2
  · intro h x hx
    have hk : ∀ k, V.hT ((Module.finBasis E A k : A) : V.V) y = 0 := fun k => by
      simpa using congrFun h k
    have hx' : x = ∑ k, (Module.finBasis E A).repr ⟨x, hx⟩ k • ((Module.finBasis E A k : A) : V.V) := by
      have e := congrArg A.subtype ((Module.finBasis E A).sum_repr ⟨x, hx⟩)
      simp only [map_sum, map_smul, Submodule.subtype_apply] at e
      exact e.symm
    rw [hx']
    simp [map_sum, hk]

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem pi_hT_finBasis_range_surjective (A : Submodule E V.V) :
    LinearMap.range (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V)) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := (LinearMap.range (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V))).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
  have hw : ∀ y, V.hT (∑ k, star (φ fun j => if k = j then (1 : E) else 0) •
      ((Module.finBasis E A k : A) : V.V)) y = 0 := by
    intro y
    have h1 := hle ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [LinearMap.pi_apply, smul_eq_mul] at h1
    have h2 : ∑ k, (φ fun j => if k = j then (1 : E) else 0) *
        V.hT ((Module.finBasis E A k : A) : V.V) y = 0 := by
      calc _ = ∑ k, V.hT ((Module.finBasis E A k : A) : V.V) y *
            (φ fun j => if k = j then (1 : E) else 0) := Finset.sum_congr rfl fun k _ => mul_comm _ _
        _ = 0 := h1
    rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
    exact h2
  have h0 := V.nondeg.1 _ hw
  have h0' : ∑ k, star (φ fun j => if k = j then (1 : E) else 0) • Module.finBasis E A k = 0 := by
    apply Subtype.ext
    simpa using h0
  have hc : ∀ k, φ (fun j => if k = j then (1 : E) else 0) = 0 := fun k => by
    have := Fintype.linearIndependent_iff.1 (Module.finBasis E A).linearIndependent _ h0' k
    simpa using this
  apply hφ
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp [hc]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_add_finrank_perp (A : Submodule E V.V) : finrank E A + finrank E (perp V A) = V.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V))
  rw [pi_hT_finBasis_range_surjective, finrank_top, Module.finrank_fin_fun, ← perp_eq_ker_pi_hT_finBasis, V.rank_eq] at h
  exact h

end Lin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.Cusp.WittIdx
