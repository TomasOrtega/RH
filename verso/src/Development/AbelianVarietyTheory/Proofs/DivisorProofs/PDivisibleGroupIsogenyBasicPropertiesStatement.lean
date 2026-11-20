import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPDivisibleGroupIsogenyBasicProperties.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G : PDivGroup p k), (∀ m : ℕ, IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) ∧ HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height)) ∧ (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog g → IsIsog (f ≫ g)) ∧ (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog (f ≫ g) → IsIsog g) ∧ ∀ (H : PDivGroup p k) (f : G ⟶ H), IsIsog f → (HasLogDeg f 0 ↔ IsIso f) := by
  first | exact @GlobalTheory.Dieu.isog_basics | exact GlobalTheory.Dieu.isog_basics | (intros; apply GlobalTheory.Dieu.isog_basics <;> assumption)
