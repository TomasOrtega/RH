import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation.EtNbhd

variable {R : Type} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Set `ψ₁ : i.A →ₐ[R] j.B` to `(IsScalarTower.toAlgHom R j.A j.B).comp φ₁`. Set `ψ₂ : i.A →ₐ[R] j.B` to `(IsScalarTower.toAlgHom R j.A j.B).comp φ₂`. Establish `: ψ₁ = ψ₂`. Use `GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq fun b => ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`.

Use `show algebraMap j.A j.B (φ₁ b) - algebraMap j.A j.B (φ₂ b) ∈ maximalIdeal j.B`. Rewrite using `[← map_sub, IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]`. Use `show φ₁ b - φ₂ b ∈ RingHom.ker j.pt`. Rewrite using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Conclude with `(congr($h₁ b)).trans (congr($h₂ b)).symm`.

Conclude with `congr($this a)`.
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
Unfold `trans`. Rewrite using `[Localization.localRingHom_to_map]`. Conclude with `algebraMap_comp_eq_of_pt _ _ h.choose_spec hφ a`.
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
Introduce `R _ _`. Use `⟨fun i x => ?_, fun i j k hij hjk x => ?_⟩` and prove the remaining obligations. Establish `: EtNbhd.trans (le_refl i) = RingHom.id i.B` using `IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by`. Simplify using `only [RingHom.comp_apply, RingHom.id_apply]`. Conclude with `EtNbhd.trans_algebraMap_eq_of_pt _ (AlgHom.id R i.A) (AlgHom.comp_id _) a)`.

Conclude with `congr($this x)`. Establish `: (EtNbhd.trans hjk).comp (EtNbhd.trans hij) = EtNbhd.trans (hij.trans hjk)` using `IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[EtNbhd.trans_algebraMap_eq_of_pt hij hij.choose hij.choose_spec, EtNbhd.trans_algebraMap_eq_of_pt hjk hjk.choose hjk.choose_spec, EtNbhd.trans_algebraMap_eq_of_pt (hij.trans hjk) (hjk.choose.comp hij.choose) (by rw [← AlgHom.comp_assoc, hjk.choose_spec, hij.choose_spec])]`. Use the proof step `rfl)`.

Conclude with `congr($this x)`.
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
