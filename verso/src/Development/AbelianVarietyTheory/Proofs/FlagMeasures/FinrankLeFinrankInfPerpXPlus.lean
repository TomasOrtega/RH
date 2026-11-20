import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA

namespace GlobalTheory.SA

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_le_finrank_inf_perp_xPlus {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ} (S : Submodule K V) (F : FlagD H r) :
    Module.finrank K S ≤ Module.finrank K ↥(S ⊓ perp H (xPlus F)) + (r + 1) := by
  let f : S →ₗ[K] (Fin (r + 1) → K) := (LinearMap.pi fun i => H.B.flip (F.e i)).comp S.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank K (LinearMap.range f) ≤ r + 1 :=
    (Submodule.finrank_le _).trans (by simp)
  have h3 : (LinearMap.ker f).map S.subtype = S ⊓ perp H (xPlus F) := by
    ext y
    rw [Submodule.mem_inf, xPlus_eq_span, mem_perp_span, Set.forall_mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, LinearMap.mem_ker.2 (funext h), rfl⟩
  rw [← h3, Submodule.finrank_map_subtype_eq]
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem norLift_decomp : ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r), IsTransv F F' →
    Module.finrank K (norLift F F') = r + 1 ∧ norLift F F' ⊔ norLift F' F = V0 F F' ∧
    wSp F F' ⊔ norLift F F' = perp H (xPlus F) ∧ Disjoint (wSp F F') (norLift F F') ∧
    IsCompl (V0 F F') (wSp F F') := by
  intro K V _ _ _ _ _ H r F F' h
  have a1 : 2 * r + 2 ≤ Module.finrank K (norLift F F') + (r + 1) :=
    h.1.ge.trans (finrank_le_finrank_inf_perp_xPlus (V0 F F') F)
  have a2 : 2 * r + 2 ≤ Module.finrank K (norLift F' F) + (r + 1) :=
    h.symm.1.ge.trans (finrank_le_finrank_inf_perp_xPlus (V0 F' F) F')
  have hle : norLift F F' ⊔ norLift F' F ≤ V0 F F' :=
    sup_le inf_le_left (inf_le_left.trans (jointSpan_comm F F').le)
  have a3 := Submodule.finrank_sup_add_finrank_inf_eq (norLift F F') (norLift F' F)
  rw [h.disjoint_norLift.eq_bot, finrank_bot] at a3
  have a4 := Submodule.finrank_mono hle
  have a5 := h.1
  have hc : IsCompl (V0 F F') (wSp F F') := by
    have b1 := finrank_le_finrank_inf_perp_xPlus (⊤ : Submodule K V) F
    have b2 := finrank_le_finrank_inf_perp_xPlus (perp H (xPlus F)) F'
    rw [top_inf_eq, finrank_top] at b1
    rw [← wSp_eq] at b2
    have b3 := Submodule.finrank_sup_add_finrank_inf_eq (V0 F F') (wSp F F')
    rw [h.2.eq_bot, finrank_bot] at b3
    refine ⟨h.2, codisjoint_iff.2 (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_))⟩
    omega
  refine ⟨by omega, Submodule.eq_of_le_of_finrank_le hle (by omega), ?_,
    h.2.symm.mono_right inf_le_left, hc⟩
  have hw : wSp F F' ≤ perp H (xPlus F) := by rw [wSp_eq]; exact inf_le_left
  rw [norLift, ← sup_inf_assoc_of_le _ hw, hc.symm.sup_eq_top, top_inf_eq]

end GlobalTheory.SA
