import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescentGeometricPoints
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaleGeomDescent.descent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleFaithfullyFlatDescentGeometricPoints.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.etale_faithfullyFlat_descent_geometric_points : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := by
  first | exact @GlobalTheory.EtaleGeomDescent.descent | exact GlobalTheory.EtaleGeomDescent.descent | (intros; apply GlobalTheory.EtaleGeomDescent.descent <;> assumption)
