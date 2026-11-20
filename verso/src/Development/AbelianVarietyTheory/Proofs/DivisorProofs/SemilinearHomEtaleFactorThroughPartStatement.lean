import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomEtaleFactorThroughPart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEt
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSemilinearHomEtaleFactorThroughPart.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.semilinearHom_etale_factor_through_part : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₀.IsConn → C.IsEt →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₁.app n (i₁.app n (x.app n a)) = x.app n a := by
  first | exact @GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt | exact GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt | (intros; apply GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt <;> assumption)
