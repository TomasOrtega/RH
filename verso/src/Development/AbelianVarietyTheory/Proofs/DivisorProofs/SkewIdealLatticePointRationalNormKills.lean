import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecMemThetaSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PtHomInjective
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.SkewPoints

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv B (c • B) (MulSemiringAction.toRingEquiv _ _ c) rfl).toEquiv).symm`.
-/
theorem absNorm_galois_smul {E : Type} [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (B : Ideal (𝓞 E)) :
    Ideal.absNorm (c • B) = Ideal.absNorm B := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv B (c • B) (MulSemiringAction.toRingEquiv _ _ c) rfl).toEquiv).symm

/- English proof (translation)
Introduce `D δ _ 𝔪 h𝔪 a d y hy`. Establish `hrange : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ≤ (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d).range`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, A, -, rfl⟩`. Take `⟨c, -, rfl⟩` from `(GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw`.

Conclude with `⟨((c : D.host.K) : D.host.E) • A, GlobalTheory.ThetaLatticePoints.ptHom_smul D ⊤ δ a d c A⟩`. Take `⟨z, hz⟩` from `hrange hy`. Rewrite `hz` using `[GlobalTheory.ThetaLatticePoints.ptHom_apply]`. Use `⟨z, hz.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, ← absNorm_galois_smul (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E) 𝔪]`.

Conclude with `GlobalTheory.FunObj.CosetTheta.absNormConj_smul_mem_stdThetaLattice h𝔪 hy`.
-/
theorem points : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ}, ∀ y ∈ (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), ∃ z : Matrix (Fin d) (Fin a) D.host.E, y = pt D (tor0 D ⊤ δ) δ z ∧ Ideal.absNorm 𝔪 • pt D (tor0 D ⊤ δ) δ z ∈ (La0 D (tor0 D ⊤ δ) a d) := by
  intro D δ _ 𝔪 h𝔪 a d y hy
  have hrange : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ≤ (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d).range := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, -, rfl⟩
    obtain ⟨c, -, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
    exact ⟨((c : D.host.K) : D.host.E) • A, GlobalTheory.ThetaLatticePoints.ptHom_smul D ⊤ δ a d c A⟩
  obtain ⟨z, hz⟩ := hrange hy
  rw [GlobalTheory.ThetaLatticePoints.ptHom_apply] at hz
  refine ⟨z, hz.symm, ?_⟩
  rw [hz, ← absNorm_galois_smul (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E) 𝔪]
  exact GlobalTheory.FunObj.CosetTheta.absNormConj_smul_mem_stdThetaLattice h𝔪 hy

end GlobalTheory.FunObj.StdDatum.SkewPoints

end
