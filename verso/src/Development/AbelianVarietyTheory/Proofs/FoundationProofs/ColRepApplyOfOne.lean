import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ZeroSubmodule

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact (Nat.Prime l)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem colRep_apply_of_one (V : GlobalTheory.Ord2.R2 Ω l) (s : G ℚ Ω)
    (hs : (V : G ℚ Ω → GL (Fin 2) (Qbar l)) s = 1) (v : Fin 2 → Qbar l) :
    UpperTheory.V.Loc.colRep V s v = v := by
  show Matrix.toLin' ((V s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) v = v
  rw [hs]
  simp

def zeroSub (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hV : ∀ a ∈ H, (V : G ℚ Ω → GL (Fin 2) (Qbar l)) a = 1)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : Subgroup (G ℚ Ω) where
  carrier := {s | s ∈ H ∧ x s = 0}
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 1 1
    rw [mul_one, colRep_apply_of_one V 1 (map_one V)] at h
    simpa using h
  mul_mem' := by
    rintro s t ⟨hs, hs0⟩ ⟨ht, ht0⟩
    refine ⟨H.mul_mem hs ht, ?_⟩
    rw [((mem_Z1_iff_cocycle _ x).1 hx).2 s t, colRep_apply_of_one V s (hV s hs), hs0, ht0, add_zero]
  inv_mem' := by
    rintro s ⟨hs, hs0⟩
    refine ⟨H.inv_mem hs, ?_⟩
    have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 s s⁻¹
    rw [mul_inv_cancel, colRep_apply_of_one V s (hV s hs), hs0, zero_add] at h
    have h1 : x 1 = 0 := by
      have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 1 1
      rw [mul_one, colRep_apply_of_one V 1 (map_one V)] at h
      simpa using h
    rw [← h, h1]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem cocycle_one (V : GlobalTheory.Ord2.R2 Ω l) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : x 1 = 0 := by
  have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 1 1
  rw [mul_one, colRep_apply_of_one V 1 (map_one V)] at h
  simpa using h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.
-/
theorem zeroSub_normal (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hH : H.Normal) (hV : ∀ a ∈ H, (V : G ℚ Ω → GL (Fin 2) (Qbar l)) a = 1)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : (zeroSub V H x hV hx).Normal := by
  constructor
  rintro s ⟨hs, hs0⟩ g
  refine ⟨hH.conj_mem s hs g, ?_⟩
  have hc := ((mem_Z1_iff_cocycle _ x).1 hx).2
  rw [hc (g * s) g⁻¹, hc g s, hs0, map_zero, add_zero, map_mul, Module.End.mul_apply,
    colRep_apply_of_one V s (hV s hs), ← hc g g⁻¹, mul_inv_cancel, cocycle_one V x hx]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem zeroSub_isClosed (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hHc : IsClosed (H : Set (G ℚ Ω))) (hV : ∀ a ∈ H, (V : G ℚ Ω → GL (Fin 2) (Qbar l)) a = 1)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : IsClosed (zeroSub V H x hV hx : Set (G ℚ Ω)) := by
  have : (zeroSub V H x hV hx : Set (G ℚ Ω)) = (H : Set (G ℚ Ω)) ∩ x ⁻¹' {0} := rfl
  rw [this]
  exact hHc.inter (isClosed_singleton.preimage ((mem_Z1_iff_cocycle _ x).1 hx).1)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem main : ∀ {Ω : Type} [inst : Field Ω] [inst_1 : Algebra ℚ Ω] {l : ℕ} [inst_2 : Fact (Nat.Prime l)] (S : Set GlobalTheory.Ord2.Pl) (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (Formalism.ConjugateSelfDual.G ℚ Ω)) (x : Formalism.ConjugateSelfDual.G ℚ Ω → Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l), Subgroup.Normal H → IsClosed (↑H : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) → (∀ a ∈ H, (V : Formalism.ConjugateSelfDual.G ℚ Ω → GL (Fin (2 : ℕ)) (Formalism.ConjugateSelfDual.Qbar l)) a = (1 : GL (Fin (2 : ℕ)) (Formalism.ConjugateSelfDual.Qbar l))) → x ∈ ReciprocityTheory.Gal.Z1 (UpperTheory.V.Loc.colRep V) → (∀ v ∉ S, ∀ (B : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver B v → ∀ s ∈ ReciprocityTheory.Gal.Ine B, s ∈ H ∧ x s = (0 : Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l)) → ∀ a ∈ ReciprocityTheory.Gal.NS Ω S, x a = (0 : Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l) := by
  intro Ω _ _ l _ S V H x hH hHc hV hx hI a ha
  haveI := zeroSub_normal V H x hH hV hx
  have hle : NS Ω S ≤ zeroSub V H x hV hx := by
    apply Subgroup.topologicalClosure_minimal _ _ (zeroSub_isClosed V H x hHc hV hx)
    apply Subgroup.normalClosure_le_normal
    intro s hs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs
    obtain ⟨v, hv, B, hB, hsB⟩ := hs
    exact hI v hv B hB s hsB
  exact (hle ha).2

end GlobalTheory.ZeroSubmodule
