import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

/- English proof (translation)
Introduce `k _ _ _ _ n ψ hψ`. Establish `hT` using `(triv_ev_props k).2.2.2.2.2.1`. Establish `hS : ∀ i j, IsOpen {x : k | Triv (ψ i / ψ j) x} ∧ IsClosed {x : k | Triv (ψ i / ψ j) x}` using `fun i j => by`. Use `hT _ ?_` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv]`.

Conclude with `(hψ i).mul (hψ j).inv`. Establish `hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) k => g.val i j` using `fun i j => by`. Establish `h1 : Continuous fun g : GL (Fin n) k => (g.val : Matrix (Fin n) (Fin n) k)` using `Units.continuous_val`. Conclude with `(continuous_apply j).comp ((continuous_apply i).comp h1)`. Establish `hE : grp ψ = (KO k (Fin n) : Set (GL (Fin n) k)) ∩ ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), (fun g : GL (Fin n) k => g.val i j) ⁻¹' {x : k | Triv (ψ i / ψ j) x}`.

Use extensionality with `g`. Simplify using `[grp]`. Rewrite using `[hE]`. Use `⟨GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => (hS i j).1.preimage (hc i j)), ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => (hS i j).2.preimage (hc i j))`.
-/
theorem grp_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsOpen (grp ψ) ∧ IsCompact (grp ψ) := by
  intro k _ _ _ _ n ψ hψ
  have hT := (triv_ev_props k).2.2.2.2.2.1
  have hS : ∀ i j, IsOpen {x : k | Triv (ψ i / ψ j) x} ∧ IsClosed {x : k | Triv (ψ i / ψ j) x} := fun i j => by
    refine hT _ ?_
    rw [div_eq_mul_inv]
    exact (hψ i).mul (hψ j).inv
  have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) k => g.val i j := fun i j =>
    by
    have h1 : Continuous fun g : GL (Fin n) k => (g.val : Matrix (Fin n) (Fin n) k) := Units.continuous_val
    exact (continuous_apply j).comp ((continuous_apply i).comp h1)
  have hE : grp ψ = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), (fun g : GL (Fin n) k => g.val i j) ⁻¹' {x : k | Triv (ψ i / ψ j) x} := by
    ext g; simp [grp]
  rw [hE]
  refine ⟨GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => (hS i j).1.preimage (hc i j)), ?_⟩
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => (hS i j).2.preimage (hc i j))

end GlobalTheory.PsType
