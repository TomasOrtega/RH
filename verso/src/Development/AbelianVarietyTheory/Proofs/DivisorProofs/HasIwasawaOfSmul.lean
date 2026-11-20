import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section
namespace GlobalTheory.SkewDblIwasawa

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities.
-/
theorem mem_hR_smul_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (c : E) (hc : c ≠ 0) (Q : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) (R ⊗[F] E)) :
    g ∈ HR R σ (c • Q) ↔ g ∈ HR R σ Q := by
  have hu : IsUnit (inclR (F := F) R c) := (IsUnit.mk0 c hc).map _
  have e : JR (F := F) R (c • Q) = inclR (F := F) R c • JR R Q := by
    ext i j; simp [JR, Matrix.map_apply, Matrix.smul_apply, map_mul]
  change Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR (F := F) R (c • Q) *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR (F := F) R (c • Q) ↔
    Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR (F := F) R Q *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR (F := F) R Q
  rw [e, Matrix.mul_smul, Matrix.smul_mul, hu.smul_left_cancel]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem hasIwasawa_of_smul {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (c : E) (hc : c ≠ 0) (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (S : Subgroup (GL (Fin (n + n)) (R ⊗[F] E)))
    (h : HasIwasawa σ (c • Q) (S.comap (GlobalTheory.AdelicU.matHom R σ (c • Q)))) :
    HasIwasawa σ Q (S.comap (GlobalTheory.AdelicU.matHom R σ Q)) := by
  intro g
  obtain ⟨p, k, hk, e⟩ := h ⟨g.1, (mem_hR_smul_iff R σ c hc Q g.1).2 g.2⟩
  refine ⟨⟨⟨p.1.1, (mem_hR_smul_iff R σ c hc Q _).1 p.1.2⟩, p.2⟩, ⟨k.1, (mem_hR_smul_iff R σ c hc Q _).1 k.2⟩, hk, ?_⟩
  apply Subtype.ext
  have := congrArg Subtype.val e
  exact this

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem dblGram_smul {E : Type} [Field E] {n : ℕ} (c : E) (J : Matrix (Fin n) (Fin n) E) :
    dblGram finSumFinEquiv (c • J) = c • dblGram finSumFinEquiv J := by
  ext i j
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp only [dblGram, blkMat, Matrix.smul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, smul_zero, smul_neg]

end GlobalTheory.SkewDblIwasawa

end
