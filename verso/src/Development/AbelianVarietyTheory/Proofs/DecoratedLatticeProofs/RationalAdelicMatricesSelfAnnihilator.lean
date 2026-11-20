import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramAnnih

variable {D : D7} {m n : ℕ}

/- English proof (translation)
Rewrite using `[rat_mul, rat_conjTranspose]`. Both sides reduce to the same expression.
-/
theorem pairing_rat (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ)
    (ξ : Matrix (Fin m) (Fin n) D.host.E) (x : Mx D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) x =
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (GlobalTheory.MixModel.rat (ξᴴ * T) ⬝ x))) := by
  rw [rat_mul, rat_conjTranspose]
  rfl

/- English proof (translation)
The claim follows from `Matrix.map_single j i e (incA D)`.
-/
theorem rat_single (j : Fin n) (i : Fin m) (e : D.host.E) :
    GlobalTheory.MixModel.rat (D := D) (Matrix.single j i e) = Matrix.single j i (incA D e) :=
  Matrix.map_single j i e (incA D)

/- English proof (translation)
Use `haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)`. Establish `e : (2 : D.host.E)⁻¹ = algebraMap D.host.F D.host.E 2⁻¹` using `by rw [map_inv₀, map_ofNat]`. Rewrite using `[e, GlobalTheory.LatVac.trace_tmul, Algebra.trace_algebraMap, D.sp.cm.deg2]`. Simplify using the standard rewrite rules.
-/
theorem trace_tmul_half (t : AF D.host.F) :
    Algebra.trace (AF D.host.F) (AE D) (t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹) = t := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have e : (2 : D.host.E)⁻¹ = algebraMap D.host.F D.host.E 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [e, GlobalTheory.LatVac.trace_tmul, Algebra.trace_algebraMap, D.sp.cm.deg2]
  simp

/- English proof (translation)
Introduce `D m n T hT ψ hψ`. Use `haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)`. Establish `hU : IsUnit T.det` using `isUnit_iff_ne_zero.2 hT.2`. Use `⟨fun x => ⟨fun h => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `key : ∀ i j (e : D.host.E), ψ (Algebra.trace (AF D.host.F) (AE D) (incA D e * x i j)) = 1`.

Introduce `i j e`. Establish `h1` using `h _ (rat_mem (Matrix.single j i e * T⁻¹)ᴴ)`. Rewrite `h1` using `[pairing_rat, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul_cancel_right _ _ hU, rat_single, Matrix.trace_single_mul, smul_eq_mul]`. Conclude with `h1`. Establish `hent : ∀ i j, ∃ e : D.host.E, x i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e` using `fun i j => GlobalTheory.RatAnnih.tensor_rat (x i j) fun e => (GlobalTheory.SWQ.Annihilator.self_annihilator D.host.F inferInstance ψ hψ).2 _ fun c => (congrArg ψ (GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c)).trans (key i j (c • e))`.

Use `choose M hM using hent`. Conclude with `⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩`. Introduce and unpack `⟨η, rfl⟩ _ ⟨ξ, rfl⟩`. Express the relevant statement in the definitionally equal form `GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) (GlobalTheory.MixModel.rat η) = 1`. Establish `e : Matrix.trace (GlobalTheory.MixModel.rat (D` using `D) (ξᴴ * T * η)) = (1 : AF D.host.F) ⊗ₜ[D.host.F] Matrix.trace (ξᴴ * T * η) := (AddMonoidHom.map_trace (incA D) _).symm`.

Rewrite using `[pairing_rat, ← rat_mul, e, GlobalTheory.LatVac.trace_tmul, one_mul]`. Conclude with `hψ.2.2.1 _`. Introduce and unpack `_ ⟨ξ, rfl⟩ h`. Express the relevant statement in the definitionally equal form `GlobalTheory.MixModel.rat ξ = 0`. Establish `hM : ξᴴ * T = 0`.

Use `Matrix.ext fun j i => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `ha`. Use `replace ha : (ξᴴ * T) j i ≠ 0 := ha`. Take `⟨t, ht⟩` from `hψ.2.2.2`. Establish `h1 : GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) _ = 1` using `h (Matrix.single i j (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)))`.

Establish `e : (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)) * GlobalTheory.MixModel.rat (D` using `D) (ξᴴ * T) j i = t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹ := by`. Express the relevant statement in the definitionally equal form `_ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (ξᴴ * T) j i) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel_right₀ ha]`. Rewrite `h1` using `[pairing_rat, Matrix.trace_mul_comm, Matrix.trace_single_mul, smul_eq_mul, e, trace_tmul_half]`. Conclude with `ht h1`.

Establish `h0 : ξᴴ = 0`. Rewrite using `[← Matrix.mul_nonsing_inv_cancel_right T ξᴴ hU, hM, Matrix.zero_mul]`. Rewrite using `[Matrix.conjTranspose_eq_zero.1 h0, rat_zero]`.
-/
theorem ratMx_annihilator : ∀ (D : D7) (m n : ℕ) (T : Matrix (Fin m) (Fin m) D.host.E), IsHermND D.sp.cm.sig T → ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ x : Mx D m n, (∀ γ ∈ ratMx D m n, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) ↔ x ∈ ratMx D m n) ∧ ∀ γ ∈ ratMx D m n, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) → γ = 0 := by
  intro D m n T hT ψ hψ
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have hU : IsUnit T.det := isUnit_iff_ne_zero.2 hT.2
  refine ⟨fun x => ⟨fun h => ?_, ?_⟩, ?_⟩
  · have key : ∀ i j (e : D.host.E), ψ (Algebra.trace (AF D.host.F) (AE D) (incA D e * x i j)) = 1 := by
      intro i j e
      have h1 := h _ (rat_mem (Matrix.single j i e * T⁻¹)ᴴ)
      rw [pairing_rat, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul_cancel_right _ _ hU, rat_single,
        Matrix.trace_single_mul, smul_eq_mul] at h1
      exact h1
    have hent : ∀ i j, ∃ e : D.host.E, x i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := fun i j =>
      GlobalTheory.RatAnnih.tensor_rat (x i j) fun e =>
        (GlobalTheory.SWQ.Annihilator.self_annihilator D.host.F inferInstance ψ hψ).2 _ fun c =>
          (congrArg ψ (GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c)).trans (key i j (c • e))
    choose M hM using hent
    exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩
  · rintro ⟨η, rfl⟩ _ ⟨ξ, rfl⟩
    change GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) (GlobalTheory.MixModel.rat η) = 1
    have e : Matrix.trace (GlobalTheory.MixModel.rat (D := D) (ξᴴ * T * η)) =
        (1 : AF D.host.F) ⊗ₜ[D.host.F] Matrix.trace (ξᴴ * T * η) :=
      (AddMonoidHom.map_trace (incA D) _).symm
    rw [pairing_rat, ← rat_mul, e, GlobalTheory.LatVac.trace_tmul, one_mul]
    exact hψ.2.2.1 _
  · rintro _ ⟨ξ, rfl⟩ h
    change GlobalTheory.MixModel.rat ξ = 0
    have hM : ξᴴ * T = 0 := by
      refine Matrix.ext fun j i => ?_
      by_contra ha
      replace ha : (ξᴴ * T) j i ≠ 0 := ha
      obtain ⟨t, ht⟩ := hψ.2.2.2
      have h1 : GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) _ = 1 :=
        h (Matrix.single i j (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)))
      have e : (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)) * GlobalTheory.MixModel.rat (D := D) (ξᴴ * T) j i =
          t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹ := by
        change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (ξᴴ * T) j i) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel_right₀ ha]
      rw [pairing_rat, Matrix.trace_mul_comm, Matrix.trace_single_mul, smul_eq_mul, e, trace_tmul_half] at h1
      exact ht h1
    have h0 : ξᴴ = 0 := by
      rw [← Matrix.mul_nonsing_inv_cancel_right T ξᴴ hU, hM, Matrix.zero_mul]
    rw [Matrix.conjTranspose_eq_zero.1 h0, rat_zero]

end GlobalTheory.GramAnnih
