import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.InvSubOneBd
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.FiltRelIndex

namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {n : ℕ} {K : Type*} [Field K] (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sub_mono (k : ℕ) : (FG n K (k + 1)).subgroupOf L ≤ (FG n K k).subgroupOf L := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact FG_mono k hx

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem sub_comm (hLF : L ≤ FG n K 0) (k : ℕ) (a b : L) (hb : b ∈ (FG n K k).subgroupOf L) :
    a * b * a⁻¹ * b⁻¹ ∈ (FG n K (k + 1)).subgroupOf L := by
  rw [Subgroup.mem_subgroupOf] at hb ⊢
  have h := FG_comm k (a : Matrix.GeneralLinearGroup (Fin n) K) b (hLF a.2) hb
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sub_top (hLF : L ≤ FG n K 0) : (FG n K 0).subgroupOf L = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_subgroupOf]
  exact hLF x.2

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem sub_bot : (FG n K n).subgroupOf L = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  apply Subtype.ext
  rw [FG_eq_one hx, Subgroup.coe_one]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem cj_subgroupOf (X : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (g : Matrix.GeneralLinearGroup (Fin n) K) (hg : g ∈ L) (hX : X ≤ L) :
    (cj g X).subgroupOf L = cj ⟨g, hg⟩ (X.subgroupOf L) := by
  ext y
  rw [Subgroup.mem_subgroupOf, mem_cj, mem_cj]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨⟨x, hX hx⟩, by rw [Subgroup.mem_subgroupOf]; exact hx, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hxy
  · rintro ⟨x, hx, hxy⟩
    rw [Subgroup.mem_subgroupOf] at hx
    refine ⟨x, hx, ?_⟩
    rw [← hxy, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem relIndex_unipotent_conj_symm (hLF : L ≤ FG n K 0) (X : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (g : Matrix.GeneralLinearGroup (Fin n) K) (hg : g ∈ L) (hX : X ≤ L) :
    X.relIndex (cj g X) = (cj g X).relIndex X := by
  have hY : cj g X ≤ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_cj g X y).1 hy
    exact L.mul_mem (L.mul_mem hg (hX hx)) (L.inv_mem hg)
  have key : (X.subgroupOf L).relIndex (cj ⟨g, hg⟩ (X.subgroupOf L)) =
      (cj ⟨g, hg⟩ (X.subgroupOf L)).relIndex (X.subgroupOf L) :=
    filt_relIndex (fun k => (FG n K k).subgroupOf L) (sub_mono L) (sub_comm L hLF) n
      (sub_top L hLF) (sub_bot L) (X.subgroupOf L) ⟨g, hg⟩
  rw [← Subgroup.relIndex_subgroupOf hY, ← Subgroup.relIndex_subgroupOf hX,
    cj_subgroupOf L X g hg hX]
  exact key

end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
