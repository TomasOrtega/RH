import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation.EtNbhd

variable {R : Type} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem algebraMap_comp_eq_of_pt {i j : EtNbhd R} (φ₁ φ₂ : i.A →ₐ[R] j.A)
    (h₁ : j.pt.comp φ₁ = i.pt) (h₂ : j.pt.comp φ₂ = i.pt) (a : i.A) :
    algebraMap j.A j.B (φ₁ a) = algebraMap j.A j.B (φ₂ a) := by
  let ψ₁ : i.A →ₐ[R] j.B := (IsScalarTower.toAlgHom R j.A j.B).comp φ₁
  let ψ₂ : i.A →ₐ[R] j.B := (IsScalarTower.toAlgHom R j.A j.B).comp φ₂
  have : ψ₁ = ψ₂ := by
    refine GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq fun b => ?_
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    show algebraMap j.A j.B (φ₁ b) - algebraMap j.A j.B (φ₂ b) ∈ maximalIdeal j.B
    rw [← map_sub, IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show φ₁ b - φ₂ b ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (congr($h₁ b)).trans (congr($h₂ b)).symm
  exact congr($this a)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trans_algebraMap_eq_of_pt {i j : EtNbhd R} (h : i ≤ j) (φ : i.A →ₐ[R] j.A)
    (hφ : j.pt.comp φ = i.pt) (a : i.A) :
    trans h (algebraMap i.A i.B a) = algebraMap j.A j.B (φ a) := by
  unfold trans
  rw [Localization.localRingHom_to_map]
  exact algebraMap_comp_eq_of_pt _ _ h.choose_spec hφ a

end GlobalTheory.Henselisation.EtNbhd

namespace GlobalTheory.Henselisation

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trans_system : ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ (i : EtNbhd R) (x : i.B), EtNbhd.trans (le_refl i) x = x) ∧ ∀ (i j k : EtNbhd R) (hij : i ≤ j) (hjk : j ≤ k) (x : i.B), EtNbhd.trans hjk (EtNbhd.trans hij x) = EtNbhd.trans (hij.trans hjk) x := by
  intro R _ _
  refine ⟨fun i x => ?_, fun i j k hij hjk x => ?_⟩
  · have : EtNbhd.trans (le_refl i) = RingHom.id i.B :=
      IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by
        simp only [RingHom.comp_apply, RingHom.id_apply]
        exact EtNbhd.trans_algebraMap_eq_of_pt _ (AlgHom.id R i.A) (AlgHom.comp_id _) a)
    exact congr($this x)
  · have : (EtNbhd.trans hjk).comp (EtNbhd.trans hij) = EtNbhd.trans (hij.trans hjk) :=
      IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by
        simp only [RingHom.comp_apply]
        rw [EtNbhd.trans_algebraMap_eq_of_pt hij hij.choose hij.choose_spec,
          EtNbhd.trans_algebraMap_eq_of_pt hjk hjk.choose hjk.choose_spec,
          EtNbhd.trans_algebraMap_eq_of_pt (hij.trans hjk) (hjk.choose.comp hij.choose)
            (by rw [← AlgHom.comp_assoc, hjk.choose_spec, hij.choose_spec])]
        rfl)
    exact congr($this x)

end GlobalTheory.Henselisation
