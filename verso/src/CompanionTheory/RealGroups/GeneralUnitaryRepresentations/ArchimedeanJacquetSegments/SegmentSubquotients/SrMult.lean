import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.ExistsNabsNeOne
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.Imports
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel GlobalTheory.LocGL

namespace CompanionTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrMult

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem irrAdm : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π hs hi =>
  (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isSmooth_segTerm' {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isIrreducible_segTerm' {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  GlobalTheory.LocGL.isIrreducible_twist σ.irr _

def cl {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrGL k :=
  IrrGL.of (segTerm σ.ρ l a) (isSmooth_segTerm' σ a) (isIrreducible_segTerm' σ a)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem cl_injective {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) : Function.Injective (cl σ l) := by
  intro a b h
  by_contra hab
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h
  exact (CompanionTheory.Pf1.SegRepC.Twist.not_equiv_segTerm hd σ l hab).false φ

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem cl_cusp {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) (a : Fin l) :
    (cl σ l a).IsCusp := by
  have h0 : (IrrGL.of σ.ρ σ.smooth σ.irr).IsCusp := ⟨hd, isCuspidal_of_equiv (IrrGL.equivOf _ _ _) hσ⟩
  have h1 := h0.nu ((a : ℕ) : ℂ)
  have e : (IrrGL.of σ.ρ σ.smooth σ.irr).nu ((a : ℕ) : ℂ) = cl σ l a := by
    unfold IrrGL.nu cl segTerm
    rw [IrrGL.tw_of]
  rwa [e] at h1

def jacEquivOf {α : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] {N : ℕ} (e : (Σ a, m a) ≃ Fin N) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (φ : π.Equiv τ) : (jac e π).Equiv (jac e τ) :=
  equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap,
      fun q => Submodule.Quotient.induction_on _ q fun v => by
        show (Submodule.Quotient.mk (φ.symm (φ v)) : _) = _
        rw [φ.symm_apply_apply],
      fun q => Submodule.Quotient.induction_on _ q fun v => by
        show (Submodule.Quotient.mk (φ (φ.symm v)) : _) = _
        rw [φ.apply_symm_apply]⟩)

def cl' {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrGL k := ⟨d, (cl σ l a).2⟩

end SrMult

open SrMult in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Assume the hypotheses and unpack their components. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem jhMult_jac_multiProd (hG : GeometricLemma) {d l : ℕ} (hd : 0 < d) (hl : 0 < l)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) :
    jhMult (piTensor (segTerm σ.ρ l))
      (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) = 1 := by
  classical
  have hx : ∑ a, (cl' σ l a).1 = l * d := by
    simp [cl', mul_comm]
  have hinj : Function.Injective (cl' σ l) := fun a b h => cl_injective hd σ h
  have hc : ∀ a, (cl' σ l a).IsCusp := fun a => cl_cusp hd σ hσ a
  have key := GlobalTheory.T.jacquet_multiplicity_cuspidal_product irrAdm (cl' σ l) (cl' σ l) hx hx hc hc
  have hset : {e : Fin l ≃ Fin l | ∀ a, cl' σ l a = cl' σ l (e a)} = {Equiv.refl _} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      ext a
      exact congrArg Fin.val (hinj (h a)).symm
    · rintro rfl a
      rfl
  rw [hset, Set.ncard_singleton] at key
  have h1 : jhMult (piTensor fun a => (cl' σ l a).rep)
      (jac (stdBlocks (fun _ : Fin l => d) hx)
        (multiProd (stdBlocks (fun _ : Fin l => d) hx) fun a => (cl' σ l a).rep)) = 1 := by
    have h := key
    exact_mod_cast h
  have hblk0 : ∀ h : ∑ _a : Fin l, d = l * d, stdBlocks (fun _ : Fin l => d) h = consecBlocks l d := by
    intro h
    ext ⟨a, i⟩
    rw [stdBlocks_val, consecBlocks_val]
    simp [mul_comm, add_comm]
  rw [hblk0 hx] at h1
  calc jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
      = jhMult (piTensor fun a => (cl' σ l a).rep)
          (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) :=
        jhMult_congr_left (piTensorEquiv fun a => IrrGL.equivOf (segTerm σ.ρ l a) (isSmooth_segTerm' σ a)
          (isIrreducible_segTerm' σ a)) _
    _ = jhMult (piTensor fun a => (cl' σ l a).rep)
          (jac (consecBlocks l d) (multiProd (consecBlocks l d) fun a => (cl' σ l a).rep)) :=
        jhMult_congr_right _ (jacEquivOf (consecBlocks l d)
          (multiProdEquiv (consecBlocks l d) fun a => IrrGL.equivOf (segTerm σ.ρ l a) (isSmooth_segTerm' σ a)
            (isIrreducible_segTerm' σ a)))
    _ = 1 := h1

end CompanionTheory.RgGu.SRC

end
