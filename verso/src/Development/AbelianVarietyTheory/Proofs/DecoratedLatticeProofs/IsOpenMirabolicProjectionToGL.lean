import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.OpenPr

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `Continuous fun x : GL A k => (fromBlocks (x : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)`. Conclude with `(Units.continuous_val).matrix_fromBlocks continuous_const continuous_const continuous_const`. Express the relevant statement in the definitionally equal form `Continuous fun x : GL A k => (fromBlocks ((x⁻¹ : GL A k) : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)`.

Conclude with `(Units.continuous_coe_inv).matrix_fromBlocks continuous_const continuous_const continuous_const`.
-/
theorem continuous_embX {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {A : Type} [Fintype A] [DecidableEq A] (c : ℕ) :
    Continuous (embX c : GL A k → GL (A ⊕ Fin c) k) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GL A k => (fromBlocks (x : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)
    exact (Units.continuous_val).matrix_fromBlocks continuous_const continuous_const continuous_const
  · change Continuous fun x : GL A k => (fromBlocks ((x⁻¹ : GL A k) : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)
    exact (Units.continuous_coe_inv).matrix_fromBlocks continuous_const continuous_const continuous_const

/- English proof (translation)
Introduce `k _ _ _ _ A _ _ c Ck O hO h1 hCk`. Establish `hc : Continuous (embX c : GL A k → GL (A ⊕ Fin c) k)` using `continuous_embX c`. Establish `hU : IsOpen ((embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O)` using `hO.preimage hc`. Establish `h1U : (1 : GL A k) ∈ (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O`. Simplify using `only [Set.mem_preimage, map_one]`.

Conclude with `h1`. Establish `hsub : (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O ⊆ (prX Ck : Set (GL A k))`. Introduce `x hx`. Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul]`.

Conclude with `hCk _ (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨x, rfl⟩)) hx`. Conclude with `Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1U) hsub)`.
-/
theorem isOpen_prX : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (1 : GL (A ⊕ Fin c) k) ∈ O → (∀ z ∈ R k A c 1, z ∈ O → z ∈ Ck) → IsOpen (prX Ck : Set (GL A k)) := by
  intro k _ _ _ _ A _ _ c Ck O hO h1 hCk
  have hc : Continuous (embX c : GL A k → GL (A ⊕ Fin c) k) := continuous_embX c
  have hU : IsOpen ((embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O) := hO.preimage hc
  have h1U : (1 : GL A k) ∈ (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O := by
    simp only [Set.mem_preimage, map_one]; exact h1
  have hsub : (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O ⊆ (prX Ck : Set (GL A k)) := by
    intro x hx
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul]
    exact hCk _ (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨x, rfl⟩)) hx
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1U) hsub)

end GlobalTheory.OpenPr
